
all: paper.pdf

paper.pdf: bibliography.bib $(wildcard *.tex)
	latexmk paper.tex -pdf

clean:
	latexmk -C
	rm -f *.spl *.bbl
