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

clean:
	rm -f $(TARGET)

.PHONY: all clean
