SHARED_SOURCE = pre.tex post.tex

ADD_FETCH_SOURCE = add-fetch-no-reset.tex
ADD_FETCH_TARGET = add-fetch-no-reset.pdf

DISSEMINATION_SOURCE = dissemination-no-reset.tex
DISSEMINATION_TARGET = dissemination-no-reset.pdf

OUR_SIMPLE_SOURCE = our-simple-no-reset.tex
OUR_SIMPLE_TARGET = our-simple-no-reset.pdf

OUR_MORE_ELABORATE_SOURCE = our-more-elaborate-no-reset.tex
OUR_MORE_ELABORATE_TARGET = our-more-elaborate-no-reset.pdf

all: $(ADD_FETCH_TARGET) $(DISSEMINATION_TARGET) $(OUR_SIMPLE_TARGET) $(OUR_MORE_ELABORATE_TARGET)

.IGNORE: $(ADD_FETCH_TARGET) #ignores errors in the pdflatex execution
$(ADD_FETCH_TARGET): $(ADD_FETCH_SOURCE) $(SHARED_SOURCE)
	pdflatex -interaction=nonstopmode $(ADD_FETCH_SOURCE)

.IGNORE: $(DISSEMINATION_TARGET)
$(DISSEMINATION_TARGET): $(DISSEMINATION_SOURCE) $(SHARED_SOURCE)
	pdflatex -interaction=nonstopmode $(DISSEMINATION_SOURCE)

.IGNORE: $(OUR_SIMPLE_TARGET)
$(OUR_SIMPLE_TARGET): $(OUR_SIMPLE_SOURCE) $(SHARED_SOURCE)
	pdflatex -interaction=nonstopmode $(OUR_SIMPLE_SOURCE)

.IGNORE: $(OUR_MORE_ELABORATE_TARGET)
$(OUR_MORE_ELABORATE_TARGET): $(OUR_MORE_ELABORATE_SOURCE) $(SHARED_SOURCE)
	pdflatex -interaction=nonstopmode $(OUR_MORE_ELABORATE_SOURCE)

.PHONY: clean
clean:
	@rm -f *.out *.aux *.log *.pdf
	
