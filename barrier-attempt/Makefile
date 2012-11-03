CC = gcc
#INCLUDE =
INCLUDE = -I/opt/papi/include/
CFLAGS = -Wall -Wextra -g -std=c99 -DDEBUG $(INCLUDE)
LN = $(CC)
#LIBS = -lpthread
LIBS = -lpthread -lpapi
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

