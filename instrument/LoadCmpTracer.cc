#include "llvm/IR/Attributes.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace {

bool IsBackEdge(BasicBlock *From, BasicBlock *To, const DominatorTree *DT) {
  if (DT->dominates(To, From)) return true;
  if (auto Next = To->getUniqueSuccessor())
    if (DT->dominates(Next, From)) return true;
  return false;
}

bool IsInterestingCmp(ICmpInst *CMP, const DominatorTree *DT,
                      const DataLayout &DL) {
  auto *Ty = CMP->getOperand(0)->getType();
  if (!Ty->isIntegerTy()) return false;
  auto Bits = DL.getTypeSizeInBits(Ty);
  if (Bits < 8 || Bits > 64) return false;

  if (!CMP->hasOneUse()) return true;
  auto BR = dyn_cast<BranchInst>(CMP->user_back());
  if (!BR) return true;

  for (BasicBlock *B : BR->successors())
    if (IsBackEdge(BR->getParent(), B, DT)) return false;
  return true;
}

bool shouldInstrument(const Function &F) {
  if (F.empty()) return false;
  if (F.getName().find(".module_ctor") != std::string::npos)
    return false;  // Should not instrument sanitizer init functions.
  if (F.getName().startswith("__sanitizer_"))
    return false;  // Don't instrument __sanitizer_* callbacks.
  // Don't touch available_externally functions, their actual body is elewhere.
  if (F.getLinkage() == GlobalValue::AvailableExternallyLinkage) return false;
  // Don't instrument MSVC CRT configuration helpers. They may run before normal
  // initialization.
  if (F.getName() == "__local_stdio_printf_options" ||
      F.getName() == "__local_stdio_scanf_options")
    return false;
  if (isa<UnreachableInst>(F.getEntryBlock().getTerminator())) return false;
  return true;
}

struct LoadCmpTracerPass : public PassInfoMixin<LoadCmpTracerPass> {
  FunctionCallee TraceVarFn[4];
  FunctionCallee TraceConstFn[4];
  FunctionCallee TraceSwitchFn;

  void survey(Module &M, ModuleAnalysisManager &MAM,
              SmallVectorImpl<ICmpInst *> &Cmps,
              SmallVectorImpl<SwitchInst *> &Switches) {
    auto &FAM =
        MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();
    auto &DL = M.getDataLayout();

    for (auto &F : M) {
      if (!shouldInstrument(F)) continue;
      const auto &DT = FAM.getResult<DominatorTreeAnalysis>(F);

      for (auto &I : instructions(F)) {
        if (auto *Cmp = dyn_cast<ICmpInst>(&I))
          if (IsInterestingCmp(Cmp, &DT, DL)) Cmps.emplace_back(Cmp);
        if (auto *Switch = dyn_cast<SwitchInst>(&I))
          Switches.emplace_back(Switch);
      }
    }
  }

  Value *findPointer(Value *Val) const {
    Val = Val->stripPointerCasts();
    auto *Inst = dyn_cast<Instruction>(Val);
    if (!Inst) return nullptr;

    if (auto *Load = dyn_cast<LoadInst>(Val)) return Load->getPointerOperand();
    if (auto *Cast = dyn_cast<CastInst>(Val))
      return findPointer(Cast->getOperand(0));
    if (auto *Intrin = dyn_cast<IntrinsicInst>(Val)) {
      if (Intrin->getIntrinsicID() == Intrinsic::bswap)
        return findPointer(Intrin->getOperand(0));
    }
    if (isa<BinaryOpIntrinsic>(Val) || isa<BinaryOperator>(Val)) {
      auto *LHS = Inst->getOperand(0), *RHS = Inst->getOperand(1);
      auto LConst = isa<ConstantInt>(LHS), RConst = isa<ConstantInt>(RHS);
      if (LConst == RConst) return nullptr;
      auto *Var = LConst ? RHS : LHS;
      return findPointer(Var);
    }
    return nullptr;
  }

  Value *findPointer(const ICmpInst *Cmp, Value *Val) const {
    auto *Ptr = findPointer(Val);
    if (Ptr) return Ptr;

#if defined(ENABLE_DEBUG)
    auto *F = Cmp->getFunction();
    errs() << "PtrMissing: " << F->getName() << ": " << *Val << "\n";
#endif
    auto &C = Cmp->getContext();
    return ConstantPointerNull::get(IntegerType::getInt8PtrTy(C));
  }

  FunctionCallee *findFunction(unsigned Bits, FunctionCallee *Array) {
    if (Bits == 8) return &Array[0];
    if (Bits == 16) return &Array[1];
    if (Bits == 32) return &Array[2];
    if (Bits == 64) return &Array[3];
    return nullptr;
  }

  bool instrumentConst(ICmpInst *Cmp, Value *Var, ConstantInt *Const) {
#if defined(ENABLE_DEBUG)
    errs() << "LConst-Enter: " << Cmp->getFunction()->getName() << ": " << *Cmp
           << "\n";
#endif
    // cmp(a - b, c) => cmp(a, b)
    if (auto *Binop = dyn_cast<BinaryOperator>(Var->stripPointerCasts())) {
      if (Binop->getOpcode() == BinaryOperator::Sub) {
#if defined(ENABLE_DEBUG)
        errs() << "  LConst-Redirect\n";
#endif
        return instrument(Cmp, Binop->getOperand(0), Binop->getOperand(1));
      }
    }

    auto &DL = Cmp->getModule()->getDataLayout();
    auto IntBits = DL.getTypeSizeInBits(Var->getType());
    auto *RuntimeFn = findFunction(IntBits, TraceConstFn);
    if (!RuntimeFn) {
#if defined(ENABLE_DEBUG)
      errs() << "  LConst-NoFn\n";
#endif
      return false;
    }

    auto BitsSet = Const->getValue().countPopulation();
    auto FewBitsSet = BitsSet < 2 || Const->getBitWidth() - BitsSet < 2;
    if (FewBitsSet) {
#if defined(ENABLE_DEBUG)
      (errs() << "  LConst-Prune: (").write_hex(Const->getZExtValue())
          << ") " << *Var << "\n";
#endif
      return false;
    }

    IRBuilder<> IRB(Cmp);
    auto *IntTy = IRB.getIntNTy(IntBits);
    auto *VarPtr = findPointer(Cmp, Var);
#if defined(ENABLE_DEBUG)
    errs() << "  LConst-Instrument:\n";
    errs() << "    LConst-Value: " << *Const << "\n";
    errs() << "    LConst-Variable: " << *Var << "\n";
    errs() << "    LConst-Ptr: " << *VarPtr << "\n";
#endif
    IRB.CreateCall(*RuntimeFn,
                   {IRB.CreateIntCast(Var, IntTy, false),
                    IRB.CreateIntCast(Const, IntTy, false),
                    IRB.CreateBitOrPointerCast(VarPtr, IRB.getInt8PtrTy())});
    return true;
  }

  bool instrumentVariable(ICmpInst *Cmp, Value *LHS, Value *RHS) {
#if defined(ENABLE_DEBUG)
    errs() << "LVar-Enter: " << Cmp->getFunction()->getName() << ": " << *Cmp
           << "\n";
#endif
    auto &DL = Cmp->getModule()->getDataLayout();
    auto IntBits = DL.getTypeSizeInBits(LHS->getType());
    auto *RuntimeFn = findFunction(IntBits, TraceVarFn);
    if (!RuntimeFn) {
#if defined(ENABLE_DEBUG)
      errs() << "  LVar-NoFn\n";
#endif
      return false;
    }

    auto *LPtr = findPointer(Cmp, LHS), *RPtr = findPointer(Cmp, RHS);
#if defined(ENABLE_DEBUG)
    errs() << "  LVar-Instrument:\n";
    errs() << "    LVar-LHS: " << *LHS << "\n";
    errs() << "    LVar-RHS: " << *RHS << "\n";
    errs() << "    LVar-LPtr: " << *LPtr << "\n";
    errs() << "    LVar-RPtr: " << *RPtr << "\n";
#endif

    IRBuilder<> IRB(Cmp);
    auto *IntTy = IRB.getIntNTy(IntBits);
    IRB.CreateCall(*RuntimeFn,
                   {IRB.CreateIntCast(LHS, IntTy, Cmp->isSigned()),
                    IRB.CreateIntCast(RHS, IntTy, Cmp->isSigned()),
                    IRB.CreateBitOrPointerCast(LPtr, IRB.getInt8PtrTy()),
                    IRB.CreateBitOrPointerCast(RPtr, IRB.getInt8PtrTy())});
    return true;
  }

  bool instrumentSwitch(Module &M, SwitchInst *SI) {
    IRBuilder<> IRB(SI);
    static constexpr unsigned MaxBits = 64;
    auto *IntTy = IRB.getIntNTy(MaxBits);
    auto *Cond = SI->getCondition();
    auto CondBits = Cond->getType()->getScalarSizeInBits();

    SmallVector<Constant *, 16> Initializers;
    if (CondBits > MaxBits) return false;

    Initializers.push_back(IRB.getInt64(SI->getNumCases()));
    Initializers.push_back(IRB.getInt64(CondBits));
    for (auto It : SI->cases()) {
      Constant *C = It.getCaseValue();
      if (CondBits < MaxBits)
        C = ConstantExpr::getCast(CastInst::ZExt, It.getCaseValue(), IntTy);
      Initializers.push_back(C);
    }

    llvm::sort(drop_begin(Initializers, 2),
               [](const Constant *A, const Constant *B) {
                 return cast<ConstantInt>(A)->getLimitedValue() <
                        cast<ConstantInt>(B)->getLimitedValue();
               });

    ArrayType *IntArrayTy = ArrayType::get(IntTy, Initializers.size());
    GlobalVariable *GV = new GlobalVariable(
        M, IntArrayTy, false, GlobalVariable::InternalLinkage,
        ConstantArray::get(IntArrayTy, Initializers),
        "__sancov_gen_cov_switch_values");
    if (CondBits < MaxBits) Cond = IRB.CreateIntCast(Cond, IntTy, false);

    IRB.CreateCall(TraceSwitchFn, {Cond, IRB.CreateBitOrPointerCast(
                                             GV, IntTy->getPointerTo())});
    return true;
  }

  bool instrument(ICmpInst *Cmp, Value *LHS, Value *RHS) {
    IRBuilder<> IRB(Cmp);
    auto *LConst = dyn_cast<ConstantInt>(LHS),
         *RConst = dyn_cast<ConstantInt>(RHS);
    if (LConst && RConst) return false;
    if (!LConst && !RConst) return instrumentVariable(Cmp, LHS, RHS);

    if (LConst)
      return instrumentConst(Cmp, RHS, LConst);
    else
      return instrumentConst(Cmp, LHS, RConst);  // assert(RConst)
  }

  void createRuntimeFunction(Module &M, unsigned FnIndex, unsigned NBytes) {
    std::string FName;

    IRBuilder<> IRB(M.getContext());
    auto *Ty = IRB.getIntNTy(8 * NBytes);
    auto *PtrTy = IRB.getInt8PtrTy();
    AttributeList Attrs;
    Attrs = Attrs.addParamAttribute(M.getContext(), 0, Attribute::ZExt);
    Attrs = Attrs.addParamAttribute(M.getContext(), 1, Attribute::ZExt);

    // void tracecmp_var(LHS, RHS, LPtr, RPtr);
    FName = (Twine("__sanitizer_cov_tracecmp_var") + Twine(NBytes)).str();

    auto VarFn = M.getOrInsertFunction(FName, Attrs, IRB.getVoidTy(), Ty, Ty,
                                       PtrTy, PtrTy);

    // void tracecmp_const(Var, Const, VarPtr);
    FName = (Twine("__sanitizer_cov_tracecmp_const") + Twine(NBytes)).str();
    auto ConstFn =
        M.getOrInsertFunction(FName, Attrs, IRB.getVoidTy(), Ty, Ty, PtrTy);

    TraceVarFn[FnIndex] = VarFn;
    TraceConstFn[FnIndex] = ConstFn;
    TraceSwitchFn = M.getOrInsertFunction("__sanitizer_cov_trace_switch",
                                          IRB.getVoidTy(), IRB.getInt64Ty(),
                                          IRB.getInt64Ty()->getPointerTo());
  }

  PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM) {
    createRuntimeFunction(M, 0, 1);
    createRuntimeFunction(M, 1, 2);
    createRuntimeFunction(M, 2, 4);
    createRuntimeFunction(M, 3, 8);

    SmallVector<ICmpInst *, 0> Cmps;
    SmallVector<SwitchInst *, 16> Switches;
    survey(M, MAM, Cmps, Switches);
    for (auto *Cmp : Cmps)
      instrument(Cmp, Cmp->getOperand(0), Cmp->getOperand(1));
    for (auto *Switch : Switches) instrumentSwitch(M, Switch);
    return PreservedAnalyses::none();
  }
};

}  // namespace

#if LLVM_VERSION_MAJOR <= 13
using OptimizationLevel = typename PassBuilder::OptimizationLevel;
#endif
// This part is the new way of registering your pass
extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "LoadCmpTracer", "v0.1",
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, ModulePassManager &MPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "load-cmp-tracer") {
                    MPM.addPass(LoadCmpTracerPass());
                    return true;
                  }
                  return false;
                });
            PB.registerOptimizerLastEPCallback(
                [](llvm::ModulePassManager &PM, OptimizationLevel Level) {
                  PM.addPass(LoadCmpTracerPass());
                });
          }};
}
