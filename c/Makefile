# Makefile for cyclic buffer program

CC = gcc
CFLAGS = -Wall -Wextra -std=c99
TARGET = cyclic
SRC = cyclic.c

# Optional: override buffer size (default is 10 in cyclic.c)
# Usage: make BUF_SIZE=20
ifdef BUF_SIZE
    CFLAGS += -DBUF_SIZE=$(BUF_SIZE)
endif

all: $(TARGET)

$(TARGET): $(SRC)
	$(CC) $(CFLAGS) -o $(TARGET) $(SRC)

cyclic-afl: $(SRC)
	afl-cc $(CFLAGS) cyclic.c -o cyclic-afl

fuzz-binary: cyclic-afl
	AFL_SKIP_CPUFREQ=1 afl-fuzz -D -i binary-seeds -o out -- ./cyclic binary

fuzz-text: cyclic-afl
	AFL_SKIP_CPUFREQ=1 afl-fuzz -D -i text-seeds -o out -- ./cyclic text

clean:
	rm -f $(TARGET)

.PHONY: all clean
