// tests/main.c
#include <stdio.h>
#include <stdint.h>
#include <time.h>
#include "../src/api.h"
#include "../src/params.h"

#define MLEN 32
#define ITERATIONS 10000

double get_current_time() {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec / 1e9;
}

int main() {
    uint8_t pk[pqcrystals_dilithium2_ref_PUBLICKEYBYTES];
    uint8_t sk[pqcrystals_dilithium2_ref_SECRETKEYBYTES];
    uint8_t sig[pqcrystals_dilithium2_ref_BYTES];
    uint8_t msg[MLEN] = {0x12, 0x34};
    size_t sig_len;
    int result = 0;

    double total_keygen = 0, total_sign = 0, total_verify = 0;

    for (int i = 0; i < ITERATIONS; i++) {
        double start;

        start = get_current_time();
        pqcrystals_dilithium2_ref_keypair(pk, sk);
        total_keygen += get_current_time() - start;

        start = get_current_time();
        pqcrystals_dilithium2_ref_signature(sig, &sig_len, msg, MLEN, NULL, 0, sk);
        total_sign += get_current_time() - start;

        start = get_current_time();
        result = pqcrystals_dilithium2_ref_verify(sig, sig_len, msg, MLEN, NULL, 0, pk);
        total_verify += get_current_time() - start;

        if (result != 0) {
            printf("Verification failed at iteration %d\n", i);
            return 1;
        }
    }

    printf("Test PASSED after %d iterations.\n", ITERATIONS);
    printf("Average KeyGen Time   : %.6f s\n", total_keygen / ITERATIONS);
    printf("Average Sign Time     : %.6f s\n", total_sign / ITERATIONS);
    printf("Average Verify Time   : %.6f s\n", total_verify / ITERATIONS);

    return 0;
}

