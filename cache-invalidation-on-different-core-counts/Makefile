CC = gcc
INCLUDE =
CFLAGS = -O2 -Wall -Wextra -g -pedantic $(INCLUDE)
LN = $(CC)
LIBS = -lpthread -lrt
LFLAGS = $(LIBS)

BINARY = cache-test

OBJECTS = main.o
INCLUDES = 
SOURCES = main.c


all: dep $(BINARY)

$(BINARY): $(OBJECTS)
	$(LN) -o $(BINARY) $^ $(LFLAGS)
	@echo ""

%.o: %.c
	$(CC) $(CFLAGS) -c $<

dep: $(SOURCES)
	$(CC) $(CFLAGS) -MM $^ > .depend

-include .depend

.PHONY: clean
clean:
	-rm -f $(BINARY) *.o *.h.gch

