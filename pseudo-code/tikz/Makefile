SHARED_SOURCE = pre.tex post.tex

DISSEMINATION_SOURCE = dissemination-no-reset.tex
DISSEMINATION_TARGET = dissemination-no-reset.pdf

RONNY_FANCY_SOURCE = ronny-fancy-no-reset.tex
RONNY_FANCY_TARGET = ronny-fancy-no-reset.pdf

all: $(DISSEMINATION_TARGET) $(RONNY_FANCY_TARGET)

.IGNORE: $(DISSEMINATION_TARGET)
$(DISSEMINATION_TARGET): $(DISSEMINATION_SOURCE) $(SHARED_SOURCE)
	pdflatex -interaction=nonstopmode $(DISSEMINATION_SOURCE)

.IGNORE: $(RONNY_FANCY_TARGET)
$(RONNY_FANCY_TARGET): $(RONNY_FANCY_SOURCE) $(SHARED_SOURCE)
	pdflatex -interaction=nonstopmode $(RONNY_FANCY_SOURCE)

.PHONY: clean
clean:
	@rm -f *.out *.aux *.log *.pdf
	
