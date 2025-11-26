# Makefile for cyclic buffer program

CC = gcc
CFLAGS = -Wall -Wextra -std=c99
TARGET = cyclic
SRC = cyclic.c

all: $(TARGET)

$(TARGET): $(SRC)
	$(CC) $(CFLAGS) -o $(TARGET) $(SRC)

clean:
	rm -f $(TARGET)

.PHONY: all clean
