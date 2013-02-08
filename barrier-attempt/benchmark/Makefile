CC = gcc
#INCLUDE =
INCLUDE =
CFLAGS = -fopenmp -Wall -Wextra -g -std=c99 -DDEBUG $(INCLUDE)
LN = $(CC)
#LIBS = -lpthread
LIBS = -lpthread
LFLAGS = $(LIBS)

PTHREADS = pthreads
OPENMP = openmp
RONNY = ronny

SOURCES = main.c

all: $(PTHREADS) $(OPENMP) $(RONNY)

$(PTHREADS): $(SOURCES)
	$(CC) -o $(PTHREADS) main.c -DUSE_PTHREADS $(CFLAGS) $(LFLAGS)
	@echo ""

$(OPENMP): $(SOURCES)
	$(CC) -o $(OPENMP) main.c -DUSE_OPENMP $(CFLAGS) $(LFLAGS)
	@echo ""

$(RONNY): $(SOURCES)
	$(CC) -o $(RONNY) main.c -DUSE_RONNY $(CFLAGS) $(LFLAGS)
	@echo ""

.PHONY: clean
clean:
	-rm -f $(PTHREADS) $(OPENMP) $(RONNY) *.o *.h.gch

