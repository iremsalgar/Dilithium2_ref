CC = gcc
CFLAGS = -O3 -Wall -Wextra -std=c11 -I. -Isrc -D_GNU_SOURCE -pg
LDFLAGS = -lrt -pg

SOURCES = $(wildcard src/*.c)

# Test hedefleri
MAIN_TEST = tests/main.c
NTT_TEST = tests/ntt_test.c

BIN_MAIN = bin_main
BIN_NTT = bin_ntt

all: $(BIN_MAIN) $(BIN_NTT)

$(BIN_MAIN): $(SOURCES) $(MAIN_TEST)
	$(CC) $(CFLAGS) $^ -o $@ $(LDFLAGS)

$(BIN_NTT): $(SOURCES) $(NTT_TEST)
	$(CC) $(CFLAGS) $^ -o $@ $(LDFLAGS)

clean:
	rm -f $(BIN_MAIN) $(BIN_NTT) *.o gmon.out analysis.txt

run-main: $(BIN_MAIN)
	./$(BIN_MAIN)

run-ntt: $(BIN_NTT)
	./$(BIN_NTT)

gprof-main: run-main
	gprof ./$(BIN_MAIN) gmon.out > analysis.txt

gprof-ntt: run-ntt
	gprof ./$(BIN_NTT) gmon.out > analysis.txt

.PHONY: all clean run-main run-ntt gprof-main gprof-ntt

