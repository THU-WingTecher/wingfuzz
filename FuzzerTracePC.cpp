//===- FuzzerTracePC.cpp - PC tracing--------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
// Trace PCs.
// This module implements __sanitizer_cov_trace_pc_guard[_init],
// the callback required for -fsanitize-coverage=trace-pc-guard instrumentation.
//
//===----------------------------------------------------------------------===//

#include "FuzzerTracePC.h"
#include "FuzzerBuiltins.h"
#include "FuzzerBuiltinsMsvc.h"
#include "FuzzerCorpus.h"
#include "FuzzerDefs.h"
#include "FuzzerDictionary.h"
#include "FuzzerExtFunctions.h"
#include "FuzzerIO.h"
#include "FuzzerPlatform.h"
#include "FuzzerTraceMemory.h"
#include "FuzzerUtil.h"
#include "FuzzerValueBitMap.h"
#include <set>

// Used by -fsanitize-coverage=stack-depth to track stack depth
ATTRIBUTES_INTERFACE_TLS_INITIAL_EXEC uintptr_t __sancov_lowest_stack;

namespace {
uint8_t tolower_u(uint8_t C) {
  return std::tolower(C);
}

size_t strnlen2(const char *Xs, const char *Ys, size_t N) {
  size_t Len1 = strnlen(Xs, N);
  size_t Len2 = strnlen(Ys, N);
  N = std::min(N, Len1);
  N = std::min(N, Len2);
  return N;
}

}  // namespace

namespace fuzzer {

TracePC TPC __attribute__((init_priority(101)));

size_t TracePC::GetTotalPCCoverage() {
  return ObservedPCs.size();
}


void TracePC::HandleInline8bitCountersInit(uint8_t *Start, uint8_t *Stop) {
  if (Start == Stop) return;
  if (NumModules &&
      Modules[NumModules - 1].Start() == Start)
    return;
  assert(NumModules <
         sizeof(Modules) / sizeof(Modules[0]));
  auto &M = Modules[NumModules++];
  uint8_t *AlignedStart = RoundUpByPage(Start);
  uint8_t *AlignedStop  = RoundDownByPage(Stop);
  size_t NumFullPages = AlignedStop > AlignedStart ?
                        (AlignedStop - AlignedStart) / PageSize() : 0;
  bool NeedFirst = Start < AlignedStart || !NumFullPages;
  bool NeedLast  = Stop > AlignedStop && AlignedStop >= AlignedStart;
  M.NumRegions = NumFullPages + NeedFirst + NeedLast;;
  assert(M.NumRegions > 0);
  M.Regions = new Module::Region[M.NumRegions];
  assert(M.Regions);
  size_t R = 0;
  if (NeedFirst)
    M.Regions[R++] = {Start, std::min(Stop, AlignedStart), true, false};
  for (uint8_t *P = AlignedStart; P < AlignedStop; P += PageSize())
    M.Regions[R++] = {P, P + PageSize(), true, true};
  if (NeedLast)
    M.Regions[R++] = {AlignedStop, Stop, true, false};
  assert(R == M.NumRegions);
  assert(M.Size() == (size_t)(Stop - Start));
  assert(M.Stop() == Stop);
  assert(M.Start() == Start);
  NumInline8bitCounters += M.Size();
}

void TracePC::HandlePCsInit(const uintptr_t *Start, const uintptr_t *Stop) {
  const PCTableEntry *B = reinterpret_cast<const PCTableEntry *>(Start);
  const PCTableEntry *E = reinterpret_cast<const PCTableEntry *>(Stop);
  if (NumPCTables && ModulePCTable[NumPCTables - 1].Start == B) return;
  assert(NumPCTables < sizeof(ModulePCTable) / sizeof(ModulePCTable[0]));
  ModulePCTable[NumPCTables++] = {B, E};
  NumPCsInPCTables += E - B;
}

void TracePC::PrintModuleInfo() {
  if (NumModules) {
    Printf("INFO: Loaded %zd modules   (%zd inline 8-bit counters): ",
           NumModules, NumInline8bitCounters);
    for (size_t i = 0; i < NumModules; i++)
      Printf("%zd [%p, %p), ", Modules[i].Size(), Modules[i].Start(),
             Modules[i].Stop());
    Printf("\n");
  }
  if (NumPCTables) {
    Printf("INFO: Loaded %zd PC tables (%zd PCs): ", NumPCTables,
           NumPCsInPCTables);
    for (size_t i = 0; i < NumPCTables; i++) {
      Printf("%zd [%p,%p), ", ModulePCTable[i].Stop - ModulePCTable[i].Start,
             ModulePCTable[i].Start, ModulePCTable[i].Stop);
    }
    Printf("\n");

    if (NumInline8bitCounters && NumInline8bitCounters != NumPCsInPCTables) {
      Printf("ERROR: The size of coverage PC tables does not match the\n"
             "number of instrumented PCs. This might be a compiler bug,\n"
             "please contact the libFuzzer developers.\n"
             "Also check https://bugs.llvm.org/show_bug.cgi?id=34636\n"
             "for possible workarounds (tl;dr: don't use the old GNU ld)\n");
      _Exit(1);
    }
  }
  if (size_t NumExtraCounters = ExtraCountersEnd() - ExtraCountersBegin())
    Printf("INFO: %zd Extra Counters\n", NumExtraCounters);

  size_t MaxFeatures = CollectFeatures([](uint32_t) {});
  if (MaxFeatures > std::numeric_limits<uint32_t>::max())
    Printf("WARNING: The coverage PC tables may produce up to %zu features.\n"
           "This exceeds the maximum 32-bit value. Some features may be\n"
           "ignored, and fuzzing may become less precise. If possible,\n"
           "consider refactoring the fuzzer into several smaller fuzzers\n"
           "linked against only a portion of the current target.\n",
           MaxFeatures);
}

ATTRIBUTE_NO_SANITIZE_ALL
void TracePC::HandleCallerCallee(uintptr_t Caller, uintptr_t Callee) {
  const uintptr_t kBits = 12;
  const uintptr_t kMask = (1 << kBits) - 1;
  uintptr_t Idx = (Caller & kMask) | ((Callee & kMask) << kBits);
  ValueProfileMap.AddValueModPrime(Idx);
}

/// \return the address of the previous instruction.
/// Note: the logic is copied from `sanitizer_common/sanitizer_stacktrace.h`
inline ALWAYS_INLINE uintptr_t GetPreviousInstructionPc(uintptr_t PC) {
#if defined(__arm__)
  // T32 (Thumb) branch instructions might be 16 or 32 bit long,
  // so we return (pc-2) in that case in order to be safe.
  // For A32 mode we return (pc-4) because all instructions are 32 bit long.
  return (PC - 3) & (~1);
#elif defined(__powerpc__) || defined(__powerpc64__) || defined(__aarch64__)
  // PCs are always 4 byte aligned.
  return PC - 4;
#elif defined(__sparc__) || defined(__mips__)
  return PC - 8;
#else
  return PC - 1;
#endif
}

/// \return the address of the next instruction.
/// Note: the logic is copied from `sanitizer_common/sanitizer_stacktrace.cpp`
ALWAYS_INLINE uintptr_t TracePC::GetNextInstructionPc(uintptr_t PC) {
#if defined(__mips__)
  return PC + 8;
#elif defined(__powerpc__) || defined(__sparc__) || defined(__arm__) || \
    defined(__aarch64__)
  return PC + 4;
#else
  return PC + 1;
#endif
}

void TracePC::UpdateObservedPCs() {
  std::vector<uintptr_t> CoveredFuncs;
  auto ObservePC = [&](const PCTableEntry *TE) {
    if (ObservedPCs.insert(TE).second && DoPrintNewPCs) {
      PrintPC("\tNEW_PC: %p %F %L", "\tNEW_PC: %p",
              GetNextInstructionPc(TE->PC));
      Printf("\n");
    }
  };

  auto Observe = [&](const PCTableEntry *TE) {
    if (PcIsFuncEntry(TE))
      if (++ObservedFuncs[TE->PC] == 1 && NumPrintNewFuncs)
        CoveredFuncs.push_back(TE->PC);
    ObservePC(TE);
  };

  if (NumPCsInPCTables) {
    if (NumInline8bitCounters == NumPCsInPCTables) {
      for (size_t i = 0; i < NumModules; i++) {
        auto &M = Modules[i];
        assert(M.Size() ==
               (size_t)(ModulePCTable[i].Stop - ModulePCTable[i].Start));
        for (size_t r = 0; r < M.NumRegions; r++) {
          auto &R = M.Regions[r];
          if (!R.Enabled) continue;
          for (uint8_t *P = R.Start; P < R.Stop; P++)
            if (*P)
              Observe(&ModulePCTable[i].Start[M.Idx(P)]);
        }
      }
    }
  }

  for (size_t i = 0, N = Min(CoveredFuncs.size(), NumPrintNewFuncs); i < N;
       i++) {
    Printf("\tNEW_FUNC[%zd/%zd]: ", i + 1, CoveredFuncs.size());
    PrintPC("%p %F %L", "%p", GetNextInstructionPc(CoveredFuncs[i]));
    Printf("\n");
  }
}

uintptr_t TracePC::PCTableEntryIdx(const PCTableEntry *TE) {
  size_t TotalTEs = 0;
  for (size_t i = 0; i < NumPCTables; i++) {
    auto &M = ModulePCTable[i];
    if (TE >= M.Start && TE < M.Stop)
      return TotalTEs + TE - M.Start;
    TotalTEs += M.Stop - M.Start;
  }
  assert(0);
  return 0;
}

const TracePC::PCTableEntry *TracePC::PCTableEntryByIdx(uintptr_t Idx) {
  for (size_t i = 0; i < NumPCTables; i++) {
    auto &M = ModulePCTable[i];
    size_t Size = M.Stop - M.Start;
    if (Idx < Size) return &M.Start[Idx];
    Idx -= Size;
  }
  return nullptr;
}

static std::string GetModuleName(uintptr_t PC) {
  char ModulePathRaw[4096] = "";  // What's PATH_MAX in portable C++?
  void *OffsetRaw = nullptr;
  if (!EF->__sanitizer_get_module_and_offset_for_pc(
      reinterpret_cast<void *>(PC), ModulePathRaw,
      sizeof(ModulePathRaw), &OffsetRaw))
    return "";
  return ModulePathRaw;
}

template<class CallBack>
void TracePC::IterateCoveredFunctions(CallBack CB) {
  for (size_t i = 0; i < NumPCTables; i++) {
    auto &M = ModulePCTable[i];
    assert(M.Start < M.Stop);
    auto ModuleName = GetModuleName(M.Start->PC);
    for (auto NextFE = M.Start; NextFE < M.Stop; ) {
      auto FE = NextFE;
      assert(PcIsFuncEntry(FE) && "Not a function entry point");
      do {
        NextFE++;
      } while (NextFE < M.Stop && !(PcIsFuncEntry(NextFE)));
      CB(FE, NextFE, ObservedFuncs[FE->PC]);
    }
  }
}

void TracePC::SetFocusFunction(const std::string &FuncName) {
  // This function should be called once.
  assert(!FocusFunctionCounterPtr);
  // "auto" is not a valid function name. If this function is called with "auto"
  // that means the auto focus functionality failed.
  if (FuncName.empty() || FuncName == "auto")
    return;
  for (size_t M = 0; M < NumModules; M++) {
    auto &PCTE = ModulePCTable[M];
    size_t N = PCTE.Stop - PCTE.Start;
    for (size_t I = 0; I < N; I++) {
      if (!(PcIsFuncEntry(&PCTE.Start[I]))) continue;  // not a function entry.
      auto Name = DescribePC("%F", GetNextInstructionPc(PCTE.Start[I].PC));
      if (Name[0] == 'i' && Name[1] == 'n' && Name[2] == ' ')
        Name = Name.substr(3, std::string::npos);
      if (FuncName != Name) continue;
      Printf("INFO: Focus function is set to '%s'\n", Name.c_str());
      FocusFunctionCounterPtr = Modules[M].Start() + I;
      return;
    }
  }

  Printf("ERROR: Failed to set focus function. Make sure the function name is "
         "valid (%s) and symbolization is enabled.\n", FuncName.c_str());
  exit(1);
}

bool TracePC::ObservedFocusFunction() {
  return FocusFunctionCounterPtr && *FocusFunctionCounterPtr;
}

void TracePC::PrintCoverage(bool PrintAllCounters) {
  if (!EF->__sanitizer_symbolize_pc ||
      !EF->__sanitizer_get_module_and_offset_for_pc) {
    Printf("INFO: __sanitizer_symbolize_pc or "
           "__sanitizer_get_module_and_offset_for_pc is not available,"
           " not printing coverage\n");
    return;
  }
  Printf(PrintAllCounters ? "FULL COVERAGE:\n" : "COVERAGE:\n");
  auto CoveredFunctionCallback = [&](const PCTableEntry *First,
                                     const PCTableEntry *Last,
                                     uintptr_t Counter) {
    assert(First < Last);
    auto VisualizePC = GetNextInstructionPc(First->PC);
    std::string FileStr = DescribePC("%s", VisualizePC);
    if (!IsInterestingCoverageFile(FileStr))
      return;
    std::string FunctionStr = DescribePC("%F", VisualizePC);
    if (FunctionStr.find("in ") == 0)
      FunctionStr = FunctionStr.substr(3);
    std::string LineStr = DescribePC("%l", VisualizePC);
    size_t NumEdges = Last - First;
    std::vector<uintptr_t> UncoveredPCs;
    std::vector<uintptr_t> CoveredPCs;
    for (auto TE = First; TE < Last; TE++)
      if (!ObservedPCs.count(TE))
        UncoveredPCs.push_back(TE->PC);
      else
        CoveredPCs.push_back(TE->PC);

    if (PrintAllCounters) {
      Printf("U");
      for (auto PC : UncoveredPCs)
        Printf(DescribePC(" %l", GetNextInstructionPc(PC)).c_str());
      Printf("\n");

      Printf("C");
      for (auto PC : CoveredPCs)
        Printf(DescribePC(" %l", GetNextInstructionPc(PC)).c_str());
      Printf("\n");
    } else {
      Printf("%sCOVERED_FUNC: hits: %zd", Counter ? "" : "UN", Counter);
      Printf(" edges: %zd/%zd", NumEdges - UncoveredPCs.size(), NumEdges);
      Printf(" %s %s:%s\n", FunctionStr.c_str(), FileStr.c_str(),
             LineStr.c_str());
      if (Counter)
        for (auto PC : UncoveredPCs)
          Printf("  UNCOVERED_PC: %s\n",
                 DescribePC("%s:%l", GetNextInstructionPc(PC)).c_str());
    }
  };

  IterateCoveredFunctions(CoveredFunctionCallback);
}

template <typename T>
void TracePC::HandleSwitch(uintptr_t PC, T Val, T N, const T* Vals) {
  auto Cmp = [&](int J) {
    if (J >= 0 && (int)J < N)
      HandleCmp(PC + J, Val, Vals[J]);
  };

  if (Val < Vals[0] || Val > Vals[N - 1]) {
    Cmp(0), Cmp(N - 1);
    return;
  }

  int I = std::lower_bound(Vals, Vals + N, Val) - Vals;
  Cmp(I), Cmp(I + 1);
  if (Vals[I] == Val) Cmp(I - 1);
}

template <typename T, unsigned (*EqFn)(T X, T Y)>
void TracePC::HandleCmp(size_t Hash, T XVal, T YVal) {
  auto *PSlot = MemoryTrace.locatePriority(Hash);
  if (!PSlot)  // Skip if already succeeded.
    return;

  auto Solved = XVal == YVal;
  auto PVal = Solved ? MemoryTracer::MAX_PRIORITY : EqFn(XVal, YVal);
  MemoryTrace.addFeature(Hash, *PSlot, PVal);

  if (PVal == MemoryTracer::MAX_PRIORITY) {
    // Prune the extra entries.
    if (sizeof(T) == 4)
      TORC4.Clear(Hash);
    else if (sizeof(T) == 8)
      TORC8.Clear(Hash);
    return;
  }

  if (!MemoryTracer::hasRichInfo(XVal)) return;
  if (!MemoryTracer::hasRichInfo(YVal)) return;

  if (sizeof(T) == 4)
    TORC4.Insert(Hash, XVal, YVal);
  else if (sizeof(T) == 8)
    TORC8.Insert(Hash, XVal, YVal);
}

template <bool ZeroTerminate, MemoryTracer::TransformFnTy Transform>
void TracePC::HandleBufferCmp(void *PC, const void *X, const void *Y, size_t N,
                              bool Solved) {
  if (!fuzzer::RunningUserCallback) return;
  auto Hash = MemoryTrace.hashBufferCompare(PC, X, Y);
  auto *PSlot = MemoryTrace.locatePriority(Hash);
  if (PSlot) {
    auto PVal = Solved
                    ? MemoryTracer::MAX_PRIORITY
                    : MemoryTracer::progress<ZeroTerminate, Transform>(X, Y, N);
    MemoryTrace.addFeature(Hash, *PSlot, PVal);
  }
  AddValueForMemcmp<ZeroTerminate>(Hash, X, Y, N);
}

template <bool ZeroTerminate>
void TracePC::AddValueForMemcmp(size_t Hash, const void *XPtr, const void *YPtr,
                                size_t MaxLen) {
  if (MaxLen <= 1) return;

  auto &MT = fuzzer::TPC.MemoryTrace;
  // Ensure Y is more likely to be a constant.
  auto Constness = MT.constness(YPtr) - MT.constness(XPtr);
  if (Constness == 0) return;  // Skip non-constants.
  if (Constness < 0) std::swap(XPtr, YPtr);

  auto Xn = MaxLen, Yn = MaxLen;
  if (ZeroTerminate) {
    Xn = strnlen(reinterpret_cast<const char *>(XPtr), MaxLen);
    Yn = strnlen(reinterpret_cast<const char *>(YPtr), MaxLen);
    if (Xn <= 1 && Yn <= 1) return;
  }

  auto *Xs = reinterpret_cast<const uint8_t *>(XPtr),
       *Ys = reinterpret_cast<const uint8_t *>(YPtr);
  fuzzer::TPC.TORCW.Insert(Hash, {Xs, Xn}, {Ys, Yn});
}

void TracePC::ClearInlineCounters() {
  IterateCounterRegions([](const Module::Region &R){
    if (R.Enabled)
      memset(R.Start, 0, R.Stop - R.Start);
  });
}

ATTRIBUTE_NO_SANITIZE_ALL
void TracePC::RecordInitialStack() {
  int stack;
  __sancov_lowest_stack = InitialStack = reinterpret_cast<uintptr_t>(&stack);
}

uintptr_t TracePC::GetMaxStackOffset() const {
  return InitialStack - __sancov_lowest_stack;  // Stack grows down
}

void WarnAboutDeprecatedInstrumentation(const char *flag) {
  // Use RawPrint because Printf cannot be used on Windows before OutputFile is
  // initialized.
  RawPrint(flag);
  RawPrint(
      " is no longer supported by libFuzzer.\n"
      "Please either migrate to a compiler that supports -fsanitize=fuzzer\n"
      "or use an older version of libFuzzer\n");
  exit(1);
}

} // namespace fuzzer

extern "C" {
ATTRIBUTE_INTERFACE
ATTRIBUTE_NO_SANITIZE_ALL
void __sanitizer_cov_trace_pc_guard(uint32_t *Guard) {
  fuzzer::WarnAboutDeprecatedInstrumentation(
      "-fsanitize-coverage=trace-pc-guard");
}

// Best-effort support for -fsanitize-coverage=trace-pc, which is available
// in both Clang and GCC.
ATTRIBUTE_INTERFACE
ATTRIBUTE_NO_SANITIZE_ALL
void __sanitizer_cov_trace_pc() {
  fuzzer::WarnAboutDeprecatedInstrumentation("-fsanitize-coverage=trace-pc");
}

ATTRIBUTE_INTERFACE
void __sanitizer_cov_trace_pc_guard_init(uint32_t *Start, uint32_t *Stop) {
  fuzzer::WarnAboutDeprecatedInstrumentation(
      "-fsanitize-coverage=trace-pc-guard");
}

ATTRIBUTE_INTERFACE
void __sanitizer_cov_8bit_counters_init(uint8_t *Start, uint8_t *Stop) {
  fuzzer::TPC.HandleInline8bitCountersInit(Start, Stop);
}

ATTRIBUTE_INTERFACE
void __sanitizer_cov_pcs_init(const uintptr_t *pcs_beg,
                              const uintptr_t *pcs_end) {
  fuzzer::TPC.HandlePCsInit(pcs_beg, pcs_end);
}

ATTRIBUTE_INTERFACE
ATTRIBUTE_NO_SANITIZE_ALL
void __sanitizer_cov_trace_pc_indir(uintptr_t Callee) {
  fuzzer::TPC.HandleCallerCallee(GET_CALLER_PC_INT(), Callee);
}

#define GEN_CMP_FN(BYTES, TYPE, ...)                                       \
  ATTRIBUTE_INTERFACE ATTRIBUTE_NO_SANITIZE_ALL void                       \
      __sanitizer_cov_trace_load##BYTES(TYPE *Ptr) {                       \
    fuzzer::TPC.MemoryTrace.traceLoad(Ptr, BYTES);                         \
  }                                                                        \
  ATTRIBUTE_INTERFACE ATTRIBUTE_NO_SANITIZE_ALL void                       \
      __sanitizer_cov_tracecmp_var##BYTES(                                 \
          TYPE LHS, TYPE RHS, const uint8_t *LPtr, const uint8_t *RPtr) {  \
    auto Hash = fuzzer::TPC.MemoryTrace.hashBufferCompare(GET_CALLER_PC(), \
                                                          LPtr, RPtr);     \
    fuzzer::TPC.HandleCmp(Hash, LHS, RHS);                                 \
  }                                                                        \
  ATTRIBUTE_INTERFACE ATTRIBUTE_NO_SANITIZE_ALL void                       \
      __sanitizer_cov_tracecmp_ord##BYTES(                                 \
          TYPE LHS, TYPE RHS, const uint8_t *LPtr, const uint8_t *RPtr) {  \
    auto Hash = fuzzer::TPC.MemoryTrace.hashBufferCompare(GET_CALLER_PC(), \
                                                          LPtr, RPtr);     \
    fuzzer::TPC                                                            \
        .HandleCmp<TYPE, fuzzer::MemoryTracer::countLeadingZeroes<TYPE>>(  \
            Hash, LHS, RHS);                                               \
  }                                                                        \
  ATTRIBUTE_INTERFACE ATTRIBUTE_NO_SANITIZE_ALL void                       \
      __sanitizer_cov_tracecmp_const##BYTES(TYPE Var, TYPE Const) {        \
    fuzzer::TPC.HandleCmp(GET_CALLER_PC_INT(), Var, Const);                \
  }                                                                        \
  ATTRIBUTE_INTERFACE ATTRIBUTE_NO_SANITIZE_ALL void                       \
      __sanitizer_cov_trace_switch##BYTES(TYPE Val, TYPE Num,              \
                                          const TYPE *Cases) {             \
    fuzzer::TPC.HandleSwitch(GET_CALLER_PC_INT(), Val, Num, Cases);        \
  }

#define GEN_CMP_ALL(GENFN, ...)   \
  GENFN(1, uint8_t, __VA_ARGS__)  \
  GENFN(2, uint16_t, __VA_ARGS__) \
  GENFN(4, uint32_t, __VA_ARGS__) \
  GENFN(8, uint64_t, __VA_ARGS__)

GEN_CMP_ALL(GEN_CMP_FN)

#undef GEN_CMP_ALL
#undef GEN_CMP_FN

ATTRIBUTE_INTERFACE
ATTRIBUTE_NO_SANITIZE_ALL
ATTRIBUTE_TARGET_POPCNT
void __sanitizer_cov_trace_div4(uint32_t Val) {
  fuzzer::TPC.HandleCmp(GET_CALLER_PC_INT(), Val, (uint32_t)0);
}

ATTRIBUTE_INTERFACE
ATTRIBUTE_NO_SANITIZE_ALL
ATTRIBUTE_TARGET_POPCNT
void __sanitizer_cov_trace_div8(uint64_t Val) {
  fuzzer::TPC.HandleCmp(GET_CALLER_PC_INT(), Val, (uint64_t)0);
}

ATTRIBUTE_INTERFACE
ATTRIBUTE_NO_SANITIZE_ALL
ATTRIBUTE_TARGET_POPCNT
void __sanitizer_cov_trace_gep(uintptr_t Idx) {
  fuzzer::TPC.HandleCmp(GET_CALLER_PC_INT(), Idx, (uintptr_t)0);
}

ATTRIBUTE_INTERFACE ATTRIBUTE_NO_SANITIZE_MEMORY
void __sanitizer_weak_hook_memcmp(void *caller_pc, const void *s1,
                                  const void *s2, size_t n, int result) {
  fuzzer::TPC.HandleBufferCmp(caller_pc, s1, s2, n, !result);
}

ATTRIBUTE_INTERFACE ATTRIBUTE_NO_SANITIZE_MEMORY
void __sanitizer_weak_hook_strncmp(void *caller_pc, const char *s1,
                                   const char *s2, size_t n, int result) {
  fuzzer::TPC.HandleBufferCmp<true>(caller_pc, s1, s2, n, !result);
}

ATTRIBUTE_INTERFACE ATTRIBUTE_NO_SANITIZE_MEMORY void
__sanitizer_weak_hook_strcmp(void *caller_pc, const char *s1, const char *s2,
                             int result) {
  fuzzer::TPC.HandleBufferCmp<true>(caller_pc, s1, s2, -1, !result);
}

ATTRIBUTE_INTERFACE ATTRIBUTE_NO_SANITIZE_MEMORY
    void __sanitizer_weak_hook_strncasecmp(void *caller_pc, const char *s1,
                                           const char *s2, size_t n,
                                           int result) {
  fuzzer::TPC.HandleBufferCmp<true, tolower_u>(caller_pc, s1, s2, n, !result);
}

ATTRIBUTE_INTERFACE ATTRIBUTE_NO_SANITIZE_MEMORY
void __sanitizer_weak_hook_strcasecmp(void *caller_pc, const char *s1,
                                      const char *s2, int result) {
  fuzzer::TPC.HandleBufferCmp<true, tolower_u>(caller_pc, s1, s2, -1, !result);
}

ATTRIBUTE_INTERFACE ATTRIBUTE_NO_SANITIZE_MEMORY
void __sanitizer_weak_hook_strstr(void *called_pc, const char *s1,
                                  const char *s2, char *result) {
  if (!fuzzer::RunningUserCallback) return;
  fuzzer::TPC.MMT.Add(reinterpret_cast<const uint8_t *>(s2), strlen(s2));
}

ATTRIBUTE_INTERFACE ATTRIBUTE_NO_SANITIZE_MEMORY
void __sanitizer_weak_hook_strcasestr(void *called_pc, const char *s1,
                                      const char *s2, char *result) {
  if (!fuzzer::RunningUserCallback) return;
  fuzzer::TPC.MMT.Add(reinterpret_cast<const uint8_t *>(s2), strlen(s2));
}

ATTRIBUTE_INTERFACE ATTRIBUTE_NO_SANITIZE_MEMORY
void __sanitizer_weak_hook_memmem(void *called_pc, const void *s1, size_t len1,
                                  const void *s2, size_t len2, void *result) {
  if (!fuzzer::RunningUserCallback) return;
  fuzzer::TPC.MMT.Add(reinterpret_cast<const uint8_t *>(s2), len2);
}
}  // extern "C"
