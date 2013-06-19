CC = gcc
INCLUDE =
CFLAGS = -Wall -Wextra -g -std=c99 -DDEBUG $(INCLUDE)
#CFLAGS = -Wall -Wextra -g -std=gnu99 $(INCLUDE)
LN = $(CC)
LIBS = -lpthread -lrt -lm
LFLAGS = $(LIBS)

BINARY = rapl-benchmark

SOURCES = main.c

all: $(BINARY)

$(BINARY): $(SOURCES) Makefile
	$(CC) -o $(BINARY) $< $(CFLAGS) $(LFLAGS)
	@echo ""

.PHONY: clean
clean:
	-rm -f $(BINARY) *.o *.h.gch

