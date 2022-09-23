#ifndef LLVM_FUZZER_TRACE_MEMORY_H
#define LLVM_FUZZER_TRACE_MEMORY_H
#include <array>
#include <cstdint>
#include <cstdlib>
#include <vector>

#include "FuzzerIO.h"

struct dl_phdr_info;

namespace fuzzer {
struct Region {
  const uint8_t *Begin = reinterpret_cast<const uint8_t *>(-1), *End = nullptr;

  void extend(const uint8_t *X, const uint8_t *Y) {
    Begin = std::min(Begin, X);
    End = std::max(End, Y);
  }

  void set(const uint8_t *Ptr, size_t Len) {
    Begin = Ptr;
    End = Begin + Len;
  }

  bool contains(const void *P) const {
    auto *Ptr = reinterpret_cast<const uint8_t *>(P);
    return Ptr >= Begin && Ptr < End;
  }
};

class MemoryTracer {
  using PriorityT = uint8_t;
  using Feature = uint32_t;
  static constexpr size_t CAPACITY = 1 << 24;  // 16M

  std::array<PriorityT, CAPACITY> Priorities;

  static uintptr_t P2I(const void *Ptr) {
    return reinterpret_cast<uintptr_t>(Ptr);
  }

  static int iterateProgramHeader(dl_phdr_info *Info, size_t Size, void *Data);

 public:
  std::array<InputInfo *, CAPACITY> CorpusMap;
  std::vector<Feature> CurrentDiscovery;
  Region Input, Data, Load;

  static constexpr Feature MASK = 1u << (sizeof(Feature) * 8 - 1);
  static constexpr PriorityT MAX_PRIORITY = 0xff;

  // Data > Load > (Unknown) = 0 > Input
  int constness(const void *P) const {
    if (Input.contains(P))
      return -1;
    if (Data.contains(P))
      return 2;
    if (Load.contains(P))
      return 1;
    return 0;
  }

  void setInputRegion(const void *P, size_t L) {
    Input.set(reinterpret_cast<const uint8_t *>(P), L);
  }

  PriorityT *locatePriority(size_t I) {
    auto &P = Priorities[I % CAPACITY];
    if (P == MAX_PRIORITY)
      return nullptr;
    return &P;
  }

  void addFeature(size_t Hash, PriorityT &Val, PriorityT New) {
    if (New <= Val) {
      [[likely]] return;
    }

    Printf("TMEM: Feature %x Priority %zu\n", Hash, New);
    Val = New;
    CurrentDiscovery.push_back(Hash % CAPACITY);
  }

  size_t hashBufferCompare(void *PC, const void *X, const void *Y) const {
    auto Hash = P2I(PC) << 8;
    if (Load.contains(X)) Hash ^= P2I(X) << 4;
    if (Load.contains(Y)) Hash ^= P2I(Y);
    return Hash;
  }

  void initialize();

  template <typename T>
  static bool hasRichInfo(T Val) {
    T AllBits = sizeof(T) * 8;
    T ValBits = __builtin_popcountl(Val);
    ValBits = std::min(ValBits, (T)(AllBits - ValBits));
    return ValBits > AllBits / 8;
  }

  using TransformFnTy = uint8_t (*)(uint8_t);
  template <bool ZeroTerminate = false, TransformFnTy Transform = nullptr>
  static size_t progress(const void *XPtr, const void *YPtr, size_t N) {
    size_t P = 0;
    auto *Xs = reinterpret_cast<const uint8_t *>(XPtr),
         *Ys = reinterpret_cast<const uint8_t *>(YPtr);

    for (size_t I = 0; I < N; ++I) {
      auto X = Xs[I], Y = Ys[I];
      if (ZeroTerminate && (X == 0 || Y == 0)) {
        auto Equals = X == 0 && Y == 0;
        return Equals ? MAX_PRIORITY : P;
      }

      if (Transform != nullptr) X = Transform(X), Y = Transform(Y);
      if (X != Y) return P;
      P += 1;
    }
    // assert(I == N)
    return MAX_PRIORITY;
  }
};

}  // namespace fuzzer

#endif
