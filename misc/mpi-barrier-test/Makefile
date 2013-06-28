CC = gcc
INCLUDE = -I/usr/lib/openmpi/include
CFLAGS = -Wall -Wextra -g -std=c99 $(INCLUDE)
LN = $(CC)
LIBS = -L/usr/lib/debug/usr/lib/openmpi/lib/ -lmpi
LFLAGS = $(LIBS)

BINARY = mpi-barrier-test

SOURCES = main.c

all: $(BINARY)

$(BINARY): $(SOURCES)
	$(CC) -o $(BINARY) $< $(CFLAGS) $(LFLAGS)
	@echo ""

.PHONY: clean
clean:
	-rm -f $(BINARY) *.o *.h.gch

