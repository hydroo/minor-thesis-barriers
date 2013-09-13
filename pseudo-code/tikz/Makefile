SHARED_SOURCE = pre.tex post.tex

ADD_FETCH_SOURCE = add-fetch-no-reset.tex
ADD_FETCH_TARGET = add-fetch-no-reset.pdf

DISSEMINATION_SOURCE = dissemination-no-reset.tex
DISSEMINATION_TARGET = dissemination-no-reset.pdf

RONNY_SIMPLE_SOURCE = ronny-simple-no-reset.tex
RONNY_SIMPLE_TARGET = ronny-simple-no-reset.pdf

RONNY_FANCY_SOURCE = ronny-fancy-no-reset.tex
RONNY_FANCY_TARGET = ronny-fancy-no-reset.pdf

all: $(ADD_FETCH_TARGET) $(DISSEMINATION_TARGET) $(RONNY_SIMPLE_TARGET) $(RONNY_FANCY_TARGET)

.IGNORE: $(ADD_FETCH_TARGET) #ignores errors in the pdflatex execution
$(ADD_FETCH_TARGET): $(ADD_FETCH_SOURCE) $(SHARED_SOURCE)
	pdflatex -interaction=nonstopmode $(ADD_FETCH_SOURCE)

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
	
