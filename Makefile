# Makefile for Sized HOAS
# Author : Andreas Abel
# Created: 2008-05-09, 2010-03-29, 2010-11-23
# Source : project/normCC/implicit/Makefile

destdir=$(HOME)/public_html

# commands
bibtool=bibtool -- 'preserve.key.case = ON' \
	  -- 'check.double = ON' \
	  -- 'check.double.delete = ON' \
	  -- 'delete.field = { abstract }' \
	  -- 'delete.field = { dvi }' \
	  -- 'delete.field = { postscript }' \
	  -- 'delete.field = { pdf }' \
	  -- 'delete.field = { month }' \
	  -- 'delete.field = { isbn }' \
	  -- 'delete.field = { doi }' \
	  -- 'delete.field = { url }' \
	  -- 'delete.field = { note }'
#	  -- 'delete.field = { editor }'
catcfg=sed -e "s/%.*//g" <
latex=latex
pdflatex=pdflatex
bibliography=medium.bib

# stdlib=$(HOME)/agda/std-lib/src

files=lf-definability.tex Makefile macros.tex

.PHONY : all debugMake html

.PRECIOUS : %.dvi %.ps %.gz %.pdf %.tex


default : lf-definability.pdf

pack : lf-definability.zip

lf-definability.zip : lf-definability.pdf $(files) jfp1.cls harpoons.sty lf-definability.bbl jfp.bst auto-lf-definability.bib
	zip $@ $^

html : html/Everything.html

html/Everything.html : $(agdafiles)
	agda --html $<

latex/%.tex : %.lagda
	agda --latex $<

talkTYPES18.pdf : talkTYPES18.tex macros.tex latex/MonusDiagError.tex latex/MonusDiag.tex
	pdflatex $<

# lf-definability
##################################################################

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
lf-definability_aux : lf-definability.tex $(files)
	$(pdflatex) lf-definability.tex;
	touch $@;

# then, run bibtex
lf-definability.bbl : lf-definability_aux auto-lf-definability.bib
	-bibtex lf-definability;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
lf-definability.pdf : lf-definability.bbl
	$(pdflatex) lf-definability.tex;
	$(pdflatex) lf-definability.tex;

# auto-lf-definability.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-lf-definability.bib : lf-definability_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x lf-definability.aux -i $(bibliography) >> $@;
endif
endif

# lf-definability-long
##################################################################

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
lf-definability-long_aux : lf-definability-long.tex $(files)
	$(pdflatex) lf-definability-long.tex;
	touch $@;

# then, run bibtex
lf-definability-long.bbl : lf-definability-long_aux auto-lf-definability-long.bib
	-bibtex lf-definability-long;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
lf-definability-long.pdf : lf-definability-long.bbl
	$(pdflatex) lf-definability-long.tex;
	$(pdflatex) lf-definability-long.tex;

# auto-lf-definability-long.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-lf-definability-long.bib : lf-definability-long_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x lf-definability-long.aux -i $(bibliography) >> $@;
endif
endif



# Templates (reverted back to simple templates)


talk% : talk%.pdf
	cp -p $? $(destdir)/;
	touch $@;

talk%.pdf : talk%.tex
	pdflatex $<;


%.tex : %.lhs
	lhs2TeX --poly -i lhs2TeX.fmt $< > $@
# /usr/local/share/lhs2tex-1.13/

% :  %.pdf # %.dvi %.ps.gz # %.tar.gz
	cp -p $? $(destdir)/;
	touch $@;

%.dvi : %.tex
	$(latex) $<;
	-bibtex $*;
	$(latex) $<;
	$(latex) $<;

%.pdf : %.dvi
	pdflatex $*.tex;

%.ps  : %.dvi
	dvips -o $@ $<;

%.gz : %
	cat $< | gzip > $@

## does not work since $ is evaluated before %
#%.tar : %.cfg $(shell cat %.cfg)
#	echo $?


#EOF
