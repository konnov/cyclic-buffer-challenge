// vim: ts=4 sw=4 et:
/**
 * Cyclic buffer challenge in C.
 *
 * @author Igor Konnov, 2025 (bootstrapped with ChatGPT)
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

// Define buffer size if not already defined, e.g., with -DBUF_SIZE=20
#ifndef BUF_SIZE
    #define BUF_SIZE 10
#endif

static int buffer[BUF_SIZE];
static int* head = buffer;  // next element to read
static int* tail = buffer;  // next free slot to write
static int count = 0;       // number of elements in buffer

/* Write an element to the cyclic buffer */
void write_cb(int in_val) {
    if (count == BUF_SIZE) {
        // here we crash, and this is what we want a tool to find!
        fprintf(stderr, "error: buffer full\n");
        assert(0);
    }

    *tail = in_val;
    if (++tail == buffer + BUF_SIZE) {
        tail = buffer;
    }
    count++;
}

/* Read an element from the cyclic buffer */
int read_cb(int *out_val) {
    if (count == 0) {
        return 0; // empty
    }
    *out_val = *head;
    if (++head == buffer + BUF_SIZE) {
        head = buffer;
    }
    count--;
    return 1;
}

int starts_with(const char *s, const char *prefix) {
    return strncmp(s, prefix, strlen(prefix)) == 0;
}

// execute commands that we read in the text mode
int run_text() {
    char line[256];
    while (fgets(line, sizeof(line), stdin)) {
        // Strip trailing whitespace
        line[strcspn(line, "\r\n")] = 0;

        if (starts_with(line, "W")) {
            int val;
            if (sscanf(line + 1, "%d", &val) == 1) {
                write_cb(val);
                printf("WROTE %d\n", val);
            } else {
                fprintf(stderr, "Malformed WRITE command: '%s'\n", line);
		return 2;
            }
        }
        else if (starts_with(line, "R")) {
            int value;
            if (read_cb(&value)) {
                printf("READ %d\n", value);
            } else {
                fprintf(stderr, "Warning: READ called on empty buffer\n");
                return 3;
            }
        }
        else if (strlen(line) == 0) {
            // Ignore empty lines
        }
        else {
            fprintf(stderr, "Unknown command: '%s'\n", line);
	    return 4;
        }
    }

    return 0;
}

// execute commands that we read in the binary mode
int run_binary() {
    int val;
    while (!feof(stdin)) {
        if (fread(&val, sizeof(int), 1, stdin) == 0) {
            fprintf(stderr, "Expected a command\n");
            return 1;
        }
        if ((val % 2) == 0) {
            if (fread(&val, sizeof(int), 1, stdin) == 0) {
                fprintf(stderr, "Expected an int\n");
                return 2;
            }
            write_cb(val);
            printf("WROTE %d\n", val);
        } else {
            if (read_cb(&val)) {
                printf("READ %d\n", val);
            } else {
                fprintf(stderr, "Warning: READ called on empty buffer\n");
                return 4;
            }
        }
    }

    return 0;
}

int main(int argc, char **argv) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s (binary|text)\n", argv[0]);
        return 1;
    }

    if (strcmp(argv[1], "binary") == 0) {
        return run_binary();
    } else if (strcmp(argv[1], "text") == 0) {
    	return run_text();
    } else {
        fprintf(stderr, "Unexpected command");
        return 1;
    }

    return 0;
}
