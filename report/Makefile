IMAGES =

CHARTS = \
	charts/cs-work-100-B-C-D.eps \
	charts/cs-work-100-partition.eps \
	charts/cs-work-100-percent.eps \
	charts/cs-work-1000-B-C-D.eps \
	charts/cs-work-1000-percent.eps

LISTINGS = \
	listings/central-counter-no-reset.tex \
	listings/dissemination-no-reset.tex \
	listings/nmg-ronny-with-reset.tex \
	listings/ronny-simple-no-reset.tex \
	listings/ronny-fancy-no-reset.tex

TIKZ = \
	tikz/central-counter-no-reset.tex \
	tikz/dissemination-no-reset.tex \
	tikz/ronny-simple-no-reset.tex \
	tikz/ronny-fancy-no-reset.tex \
	tikz/shared-memory.tex

BIBLIOGRAPHY_SOURCE = bibliography.bib

REPORT_SOURCE = report.tex
REPORT_AUX = report.aux
REPORT_TARGET = report.pdf

.IGNORE: $(REPORT_TARGET)
$(REPORT_TARGET): $(REPORT_SOURCE) $(BIBLIOGRAPHY_SOURCE) $(CHARTS) $(IMAGES) $(LISTINGS) $(TIKZ)
	#delete later. keep for reference
	#dot -Tpdf -o images/mdp.pdf images/mdp.dot
	#dot -Tpdf -o images/ctmc.pdf images/ctmc.dot
	#dot -Tpdf -o images/cache.pdf images/cache.dot
	@echo ""

	@echo ">>> PRERUN PDFLATEX <<<"
	@echo ""
	pdflatex -shell-escape -interaction=nonstopmode $(REPORT_SOURCE) 1> /dev/null 2> /dev/null
	@echo ""
	@echo ">>> BIBTEX <<<"
	@echo ""
	bibtex $(REPORT_AUX)
	@echo ""
	@echo ">>> PRERUN PDFLATEX <<<"
	@echo ""
	pdflatex -shell-escape -interaction=nonstopmode $(REPORT_SOURCE) 1> /dev/null 2> /dev/null
	@echo ""
	@echo ">>> PDFLATEX <<<"
	@echo ""
	pdflatex -shell-escape -interaction=nonstopmode $(REPORT_SOURCE)

all: $(REPORT_TARGET)

.PHONY: clean
clean:
	@rm -f *.out *.aux *.log *.pdf *.bbl *.blg *.dvi *.toc *.lof *.lot $(CHARTS:.eps=.pdf)
	
