// tests/ntt_test.c
#include <stdio.h>
#include <stdint.h>
#include <time.h>
#include "../src/ntt.h"
#include "../src/params.h"
#include "../src/poly.h"

#define ITERATIONS 10000

double get_current_time() {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec / 1e9;
}

int main() {
    poly p;
    for (size_t i = 0; i < N; i++) {
        p.coeffs[i] = i;
    }

    double total_ntt = 0, total_invntt = 0;

    for (int i = 0; i < ITERATIONS; i++) {
        double start;

        start = get_current_time();
        pqcrystals_dilithium2_ref_ntt(p.coeffs);  // Doğru kullanım
        total_ntt += get_current_time() - start;

        start = get_current_time();
        pqcrystals_dilithium2_ref_invntt_tomont(p.coeffs);  // Doğru kullanım
        total_invntt += get_current_time() - start;
    }

    printf("NTT Test Completed (%d iterations)\n", ITERATIONS);
    printf("Average NTT Time      : %.6f s\n", total_ntt / ITERATIONS);
    printf("Average INVNTT Time   : %.6f s\n", total_invntt / ITERATIONS);

    return 0;
}

