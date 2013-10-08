SHARED_SOURCE = pre.tex post.tex

RONNY_FANCY_SOURCE = ronny-fancy-no-reset.tex
RONNY_FANCY_TARGET = ronny-fancy-no-reset.pdf

all: $(RONNY_FANCY_TARGET)

.IGNORE: $(RONNY_FANCY_TARGET)
$(RONNY_FANCY_TARGET): $(RONNY_FANCY_SOURCE) $(SHARED_SOURCE)
	pdflatex -interaction=nonstopmode $(RONNY_FANCY_SOURCE)

.PHONY: clean
clean:
	@rm -f *.out *.aux *.log *.pdf
	
