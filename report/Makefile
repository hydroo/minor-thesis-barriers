IMAGES =

CHARTS = \
	charts/cs-energy-work-100-partition.eps \
	charts/cs-energy-work-1000-partition.eps \
	\
	charts/cs-power-work-100.eps \
	charts/cs-power-work-1000.eps \
	\
	charts/cs-time-work-100-B-C-D.eps \
	charts/cs-time-work-100-partition.eps \
	charts/cs-time-work-100-percent.eps \
	charts/cs-time-work-1000-B-C-D.eps \
	charts/cs-time-work-1000-partition.eps \
	\
	charts/df-energy-work-100-partition.eps \
	charts/df-energy-work-1000-partition.eps \
	\
	charts/df-power-work-100.eps \
	charts/df-power-work-1000.eps \
	\
	charts/df-time-work-100-partition.eps \
	charts/df-time-work-1000-partition.eps \
	\
	charts/d-energy-work-100-partition.eps \
	charts/d-energy-work-1000-partition.eps \
	\
	charts/d-time-work-100-partition.eps \
	charts/d-time-work-1000-partition.eps

LISTINGS = \
	listings/central-counter.tex \
	listings/dissemination.tex \
	listings/mgb.tex \
	listings/ronny-simple.tex \
	listings/ronny-fancy.tex \
	listings/triple-reset.tex

TIKZ = \
	tikz/diagram-central-counter.tex \
	tikz/diagram-dissemination.tex \
	tikz/diagram-dissemination-progress.tex \
	tikz/diagram-gather-broadcast.tex \
	tikz/model-central-counter.tex \
	tikz/model-dissemination.tex \
	tikz/model-ronny-simple.tex \
	tikz/model-ronny-fancy.tex \
	tikz/model-shared-memory.tex

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
	
