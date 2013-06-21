CC = gcc
INCLUDE =
CFLAGS = -Wall -Wextra -g -std=c99 $(INCLUDE)
LN = $(CC)
LIBS = -lpthread -lrt
LFLAGS = $(LIBS)

BINARY = measure-sleeping

SOURCES = main.c

all: $(BINARY)

$(BINARY): $(SOURCES)
	$(CC) -o $(BINARY) $< $(CFLAGS) $(LFLAGS)
	@echo ""

.PHONY: clean
clean:
	-rm -f $(BINARY) *.o *.h.gch

