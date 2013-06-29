CC = mpicc
INCLUDE =
#CFLAGS = -Wall -Wextra -g -std=c99 -DDEBUG $(INCLUDE)
CFLAGS = -O3 -Wall -Wextra -g -std=c99 $(INCLUDE)
LN = $(CC)
LIBS = -lrt -lm
LFLAGS = $(LIBS)

BINARY = distributed

SOURCES = main.c

all: $(BINARY)

$(BINARY): $(SOURCES) Makefile
	$(CC) -o $(BINARY) $< $(CFLAGS) $(LFLAGS)
	@echo ""

.PHONY: clean
clean:
	-rm -f $(BINARY) *.o *.h.gch


