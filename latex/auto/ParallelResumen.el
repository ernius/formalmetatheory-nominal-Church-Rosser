(TeX-add-style-hook
 "ParallelResumen"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("hyperref" "hidelinks") ("agda" "references" "links")))
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art10"
    "hyperref"
    "agda"
    "amsmath"
    "amsthm"
    "mathtools"
    "textgreek"
    "catchfilebetweentags"
    "tipa"
    "graphicx"
    "bussproofs")
   (TeX-add-symbols
    '("swap" 3)
    '("var" 1)
    '("ap" 2)
    '("lambAg" 2)
    '("freshin" 2)
    "alp"
    "lamb"
    "alpsym"
    "choice"
    "p"
    "ninb"
    "inAg"
    "ninAg"
    "neqAg"
    "fv"
    "perm"
    "perma"
    "free"
    "choiceAg"
    "choiceAgaux"
    "alpeqAg"
    "betaalpha"
    "betaaster"
    "lam"
    "conc")
   (LaTeX-add-labels
    "alpha"
    "parallel"
    "pequiv"
    "prightalpha"
    "pleftalpha"
    "pfresh"
    "lamelim"
    "betaelim"
    "sec:alphaprinciple"
    "psubst")
   (LaTeX-add-environments
    "lem")))

