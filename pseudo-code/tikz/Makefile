SHARED_SOURCE = pre.tex post.tex

CENTRAL_COUNTER_SOURCE = central-counter-no-reset.tex
CENTRAL_COUNTER_TARGET = central-counter-no-reset.pdf

DISSEMINATION_SOURCE = dissemination-no-reset.tex
DISSEMINATION_TARGET = dissemination-no-reset.pdf

RONNY_SIMPLE_SOURCE = ronny-simple-no-reset.tex
RONNY_SIMPLE_TARGET = ronny-simple-no-reset.pdf

RONNY_FANCY_SOURCE = ronny-fancy-no-reset.tex
RONNY_FANCY_TARGET = ronny-fancy-no-reset.pdf

all: $(CENTRAL_COUNTER_TARGET) $(DISSEMINATION_TARGET) $(RONNY_SIMPLE_TARGET) $(RONNY_FANCY_TARGET)

.IGNORE: $(CENTRAL_COUNTER_TARGET) #ignores errors in the pdflatex execution
$(CENTRAL_COUNTER_TARGET): $(CENTRAL_COUNTER_SOURCE) $(SHARED_SOURCE)
	pdflatex -interaction=nonstopmode $(CENTRAL_COUNTER_SOURCE)

.IGNORE: $(DISSEMINATION_TARGET)
$(DISSEMINATION_TARGET): $(DISSEMINATION_SOURCE) $(SHARED_SOURCE)
	pdflatex -interaction=nonstopmode $(DISSEMINATION_SOURCE)

.IGNORE: $(RONNY_SIMPLE_TARGET)
$(RONNY_SIMPLE_TARGET): $(RONNY_SIMPLE_SOURCE) $(SHARED_SOURCE)
	pdflatex -interaction=nonstopmode $(RONNY_SIMPLE_SOURCE)

.IGNORE: $(RONNY_FANCY_TARGET)
$(RONNY_FANCY_TARGET): $(RONNY_FANCY_SOURCE) $(SHARED_SOURCE)
	pdflatex -interaction=nonstopmode $(RONNY_FANCY_SOURCE)

.PHONY: clean
clean:
	@rm -f *.out *.aux *.log *.pdf
	
