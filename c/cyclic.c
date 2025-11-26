/**
 * Cyclic buffer challenge in C.
 *
 * @author ChatGPT and Igor Konnov, 2025
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define BUF_SIZE 10

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

int main(int argc, char **argv) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <commands.txt|->\n", argv[0]);
        return 1;
    }

    FILE *f;
    if (strcmp(argv[1], "-") == 0) {
        f = stdin;
    } else {
        f = fopen(argv[1], "r");
        if (!f) {
            perror("Cannot open input file");
            return 1;
        }
    }

    char line[256];
    while (fgets(line, sizeof(line), f)) {
        // Strip trailing whitespace
        line[strcspn(line, "\r\n")] = 0;

        if (starts_with(line, "W")) {
            int val;
            if (sscanf(line + 1, "%d", &val) == 1) {
                write_cb(val);
                printf("WROTE %d\n", val);
            } else {
                fprintf(stderr, "Malformed WRITE command: '%s'\n", line);
            }
        }
        else if (starts_with(line, "R")) {
            int value;
            if (read_cb(&value)) {
                printf("READ %d\n", value);
            } else {
                fprintf(stderr, "Warning: READ called on empty buffer\n");
            }
        }
        else if (strlen(line) == 0) {
            // Ignore empty lines
        }
        else {
            fprintf(stderr, "Unknown command: '%s'\n", line);
        }
    }

    if (f != stdin) {
        fclose(f);
    }
    return 0;
}