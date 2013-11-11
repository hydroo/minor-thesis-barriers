IMAGES =

CHARTS = \
	charts/c1-energy-work-100-partition.eps \
	charts/c1-energy-work-1000-partition.eps \
	\
	charts/c1-power-work-100.eps \
	charts/c1-power-work-1000.eps \
	\
	charts/c1-time-work-100-B-C-D.eps \
	charts/c1-time-work-100-partition.eps \
	charts/c1-time-work-100-percent.eps \
	charts/c1-time-work-1000-B-C-D.eps \
	charts/c1-time-work-1000-partition.eps \
	\
	charts/d2-energy-work-100-partition.eps \
	charts/d2-energy-work-1000-partition.eps \
	\
	charts/d2-power-work-100.eps \
	charts/d2-power-work-1000.eps \
	\
	charts/d2-time-work-100-partition.eps \
	charts/d2-time-work-1000-partition.eps \
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
	listings/b1.tex \
	listings/b2.tex \
	listings/triple-reset.tex

TIKZ = \
	tikz/diagram-central-counter.tex \
	tikz/diagram-dissemination.tex \
	tikz/diagram-dissemination-progress.tex \
	tikz/diagram-gather-broadcast.tex \
	tikz/model-central-counter.tex \
	tikz/model-dissemination.tex \
	tikz/model-b1.tex \
	tikz/model-b2.tex \
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
	
