#define ATTRIBUTE_INTERFACE __attribute__((visibility("default")))
#define SANITIZER_WEAK_ATTRIBUTE __attribute__((weak))

#define GEN_CMP_FN(BYTES, TYPE, ...)                \
  ATTRIBUTE_INTERFACE SANITIZER_WEAK_ATTRIBUTE void \
      __sanitizer_cov_tracecmp_var##BYTES() {       \
    return;                                         \
  }                                                 \
  ATTRIBUTE_INTERFACE SANITIZER_WEAK_ATTRIBUTE void \
      __sanitizer_cov_tracecmp_const##BYTES() {       \
    return;                                         \
  }

#define GEN_CMP_ALL(GENFN, ...)   \
  GENFN(1, uint8_t, __VA_ARGS__)  \
  GENFN(2, uint16_t, __VA_ARGS__) \
  GENFN(4, uint32_t, __VA_ARGS__) \
  GENFN(8, uint64_t, __VA_ARGS__)

GEN_CMP_ALL(GEN_CMP_FN)

#undef GEN_CMP_ALL
#undef GEN_CMP_FN
