SHARED_SOURCE = pre.tex post.tex

ADD_FETCH_SOURCE = add-fetch-no-reset.tex
ADD_FETCH_TARGET = add-fetch-no-reset.pdf

.IGNORE: $(ADD_FETCH_TARGET) #ignores errors in the pdflatex execution
$(ADD_FETCH_TARGET): $(ADD_FETCH_SOURCE) $(SHARED_SOURCE)
	pdflatex -interaction=nonstopmode $(ADD_FETCH_SOURCE)

all: $(ADD_FETCH_TARGET)

.PHONY: clean
clean:
	@rm -f *.out *.aux *.log *.pdf
	
