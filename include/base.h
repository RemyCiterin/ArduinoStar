#define uint8_t char
#define uint16_t short

inline void write_ref_u8(uint16_t ref, uint8_t value) {
    *(uint8_t *)ref = value;
}

inline uint8_t read_ref_u8(uint16_t ref) {
    return *(uint8_t *)ref;
}

