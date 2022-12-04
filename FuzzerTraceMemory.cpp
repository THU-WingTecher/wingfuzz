#include "FuzzerTraceMemory.h"

#include <link.h>

#include <algorithm>
#include "FuzzerIO.h"

namespace fuzzer {

int MemoryTracer::iterateProgramHeader(dl_phdr_info *Info, size_t Size,
                                       void *Data) {
  if (Info->dlpi_name[0] != 0) return 0;  // Not the main program.
  if (Info->dlpi_phnum > 0 && Info->dlpi_phdr->p_type != PT_PHDR)
    return 0;  // VDSO

  auto &MT = *reinterpret_cast<MemoryTracer *>(Data);
  auto BaseAddr = Info->dlpi_addr;
  for (auto *I = Info->dlpi_phdr, *J = I + Info->dlpi_phnum; I != J; ++I) {
    // Only care about loaded, non-executable segments.
    if (I->p_type != PT_LOAD) continue;

    auto *Begin = reinterpret_cast<const uint8_t *>(BaseAddr + I->p_vaddr);
    auto Size = std::min(I->p_memsz, I->p_filesz);
    auto *End = Begin + Size;

    if (I->p_flags == PF_R) MT.Data.extend(Begin, End);
    MT.Load.extend(Begin, End);
  }

  return 0;
}

void MemoryTracer::initialize() {
  dl_iterate_phdr(iterateProgramHeader, this);
  Printf("LAYOUT: Load %p-%p; Data %p-%p\n", Load.Begin, Load.End, Data.Begin,
         Data.End);
}

void MemoryTracer::sortDiscovery() {
  auto &CD = CurrentDiscovery;
  std::sort(CD.begin(), CD.end());
  CD.erase(std::unique(CD.begin(), CD.end()), CD.end());
}

}  // namespace fuzzer
