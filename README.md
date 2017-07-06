# Machine-checked proof  of the Church-Rosser theorem for the Lambda Calculus using the Barendregt Variable Convention in Constructive Type Theory.

In this work we continue the work started in our previous formalisation [https://github.com/ernius/formalmetatheory-nominal](https://github.com/ernius/formalmetatheory-nominal), deriving in Constructive Type Theory new induction principles for the lambda calculus, using first order syntax with only one sort of names for both bound and free variables, and with alpha-conversion based upon name swapping. The principles provide a flexible framework within which it is possible to mimic pen-and-paper proofs inside the rigorous formal setting of a proof assistant.
We here show one a complete proof of the  Church-Rosser  and the Subject Reduction theorems. The whole development has been machine-checked using the system Agda.

# Principal Results

The Church-Rosser theorem is in the file *Diamond.agda* file, while the Subject Reduction theorem is in the file *Types.lagda*.

The entire code can be browsed in html format here: [https://ernius.github.io/formalmetatheory-nominal-Church-Rosser/html/index.html](https://ernius.github.io/formalmetatheory-nominal-Church-Rosser/html/index.html).

The principal results are in the following links:
* Church-Rosser Theorem: [https://ernius.github.io/formalmetatheory-nominal-Church-Rosser/html/Diamond.html](https://ernius.github.io/formalmetatheory-nominal-Church-Rosser/html/Diamond.html)
* Subject Reduction Theorem: [https://ernius.github.io/formalmetatheory-nominal-Church-Rosser/html/Types.html](https://ernius.github.io/formalmetatheory-nominal-Church-Rosser/html/Types.html)

# Authors

* Ernesto Copello 
* Nora Szasz      
* Álvaro Tasistro 






