CC = gcc
#INCLUDE =
INCLUDE =
CFLAGS = -O0 -Wall -Wextra -g -std=c99 -DDEBUG $(INCLUDE)
LN = $(CC)
LIBS = -lpthread
LFLAGS = $(LIBS)

BARRIER = barrier

BARRIER_OBJECTS = main.o
BARRIER_INCLUDES = 
BARRIER_SOURCES = main.c


all: dep $(BARRIER)

$(BARRIER): $(BARRIER_OBJECTS)
	$(LN) -o $(BARRIER) $^ $(LFLAGS)
	@echo ""

%.o: %.c
	$(CC) $(CFLAGS) -c $<

dep: $(BARRIER_SOURCES)
	$(CC) $(CFLAGS) -MM $^ > .depend

-include .depend

.PHONY: clean
clean:
	-rm -f $(BARRIER) *.o *.h.gch

