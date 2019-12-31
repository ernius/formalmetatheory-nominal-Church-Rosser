# name of agda compiler name
AGDA = agda

LATEX = pdflatex

# agda library location
#AGDALIBRARYFLAGS = -i . -i ~/Documents/NewAgda/agda-stdlib-0.9/src/
# AGDALIBRARYFLAGS = -i . -i /nix/store/fdif0nwphfy56zd16qlkyk0wg54bcqlz-agda-stdlib-2.4.2.3/share/agda

# agda html
AGDAHTMLFLAGS = --html

# agda latex
AGDALATEXFLAGS = --latex

latex/%.tex : %.lagda
	$(AGDA) $(AGDALATEXFLAGS) $(AGDALIBRARYFLAGS) $<

bib : latex/resumen.bib
	cd latex; pdflatex resumen.tex; bibtex resumen;pdflatex resumen.tex;pdflatex resumen.tex; cd ..;

resumen : latex/resumen.tex latex/Substitution.tex latex/FreeVariables.tex latex/Atom.tex latex/Alpha.tex latex/Chi.tex latex/Equivariant.tex latex/ListProperties.tex latex/NaturalProperties.tex latex/Permutation.tex latex/TermAcc.tex latex/Term.tex latex/TermInduction.tex latex/TermRecursion.tex latex/Norrish.tex latex/Parallel.tex latex/Types.tex
	cd latex; $(LATEX) resumen.tex; cd ..;	

diapo : latex/diapositivas.tex latex/Substitution.tex latex/FreeVariables.tex latex/Atom.tex latex/Alpha.tex latex/Chi.tex latex/Equivariant.tex latex/ListProperties.tex latex/NaturalProperties.tex latex/Permutation.tex latex/TermAcc.tex latex/Term.tex latex/TermInduction.tex latex/TermRecursion.tex latex/Norrish.tex 
	cd latex; $(LATEX) diapositivas.tex; cd ..;	

Substitution : Substitution.lagda
	$(AGDA) $(AGDALIBRARYFLAGS) Substitution.lagda

FreeVariables : FreeVariables.lagda
	$(AGDA) $(AGDALIBRARYFLAGS) Substitution.lagda

html : *.lagda
	$(AGDA) $(AGDAHTMLFLAGS) $(AGDALIBRARYFLAGS) Diamond.agda
	$(AGDA) $(AGDAHTMLFLAGS) $(AGDALIBRARYFLAGS) Types.lagda
	$(AGDA) $(AGDAHTMLFLAGS) $(AGDALIBRARYFLAGS) WeakNormalization.lagda

clean :
	rm *.agdai
