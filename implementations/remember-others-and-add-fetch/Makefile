CC = gcc
INCLUDE =
#CFLAGS = -Wall -Wextra -g -std=c99 -DDEBUG $(INCLUDE)
CFLAGS = -O3 -Wall -Wextra -g -std=c99 $(INCLUDE)
LN = $(CC)
LIBS = -lpthread -lrt
LFLAGS = $(LIBS)

ADD_FETCH = add-fetch
RONNY = ronny

SOURCES = main.c

all: $(ADD_FETCH) $(RONNY)

$(ADD_FETCH): $(SOURCES)
	$(CC) -o $(ADD_FETCH) $< -DUSE_ADD_FETCH $(CFLAGS) $(LFLAGS)
	@echo ""

$(RONNY): $(SOURCES)
	$(CC) -o $(RONNY) $< -DUSE_RONNY $(CFLAGS) $(LFLAGS)
	@echo ""

.PHONY: clean
clean:
	-rm -f $(ADD_FETCH) $(RONNY) *.o *.h.gch

