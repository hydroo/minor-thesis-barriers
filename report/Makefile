IMAGES =

REFERENCES_SOURCE = references.bib

REPORT_SOURCE = report.tex
REPORT_AUX = report.aux
REPORT_TARGET = report.pdf

.IGNORE: $(REPORT_TARGET)
$(REPORT_TARGET): $(REPORT_SOURCE) $(REFERENCES_SOURCE) $(IMAGES)
	#delete later. keep for reference
	#dot -Tpdf -o images/mdp.pdf images/mdp.dot
	#dot -Tpdf -o images/ctmc.pdf images/ctmc.dot
	#dot -Tpdf -o images/cache.pdf images/cache.dot
	@echo ""

	@echo ">>> PRERUN PDFLATEX <<<"
	@echo ""
	pdflatex -interaction=nonstopmode $(REPORT_SOURCE) 1> /dev/null 2> /dev/null
	@echo ""
	@echo ">>> BIBTEX <<<"
	@echo ""
	bibtex $(REPORT_AUX)
	@echo ""
	@echo ">>> PDFLATEX <<<"
	@echo ""
	pdflatex -interaction=nonstopmode $(REPORT_SOURCE)

all: $(REPORT_TARGET)

.PHONY: clean
clean:
	@rm -f *.out *.aux *.log *.pdf *.bbl *.blg *.dvi *.toc *.lof *.lot
	
