Riesz Logic
===========

Implementation of the hypersequent calculii HR and HMR introduced in the article "Proof Theory of Riesz Spaces and Modal Riesz Spaces" (https://arxiv.org/abs/2004.11185).

Working with `Coq 8.12.0`

If you have any trouble or question, please contact `christophe.lucas@ens-lyon.fr` or `matteo.mio@ens-lyon.fr`.

### How to compile
To compile all the coq files and generate the documentation, type the following instruction in a terminal at the root of the project (where the file hr\_main\_results.v is).

	$ ./configure
	$ make gallinahtml

This command generates a .html file for each Coq file, that only have definitions, statements and comments useful for the reader. It also generates a file "toc.html" where all the sections in the files are gathered together as well as a quick explanation of what the reader will find in the files.


### The structure of the depository
There are five folders in the depository:

* QArithSternBrocot - contains the file sqrt2.v from the library [QArithSternBrocot](https://coq.inria.fr/distrib/8.2/contribs/QArithSternBrocot.html) used to prove the irrationality of sqrt 2.
* OLlibs - contains a subset of the library [OLlibs](https://github.com/olaure01/ollibs), a collection of add-ons for the Coq Standard Library.
* Utilities - contains files not connected to Riesz Logic (e.g. a file defining positive real numbers and lemmas about them).
* hr - contains all the files related to the system HR.
* hmr - contains all the files related to the system HMR.

Following is a quick summary of the purpose of each file in the different folders.

#### H(M)R
The files in hr and hmr are quite similar (because the structure of Section 3 and Section 4 of the article are also very similar), here are the files that are in those folders.

##### Terms
* `term.v` : Definitions  ad notations regarding terms of Riesz spaces (with positive real scalars as weights). The type corresponding to those terms is `term`.
* `Rterm.v` : Definitions and notations regarding terms of Riesz spaces (with any real scalars as weights). The type corresponding to those terms is `Rterm`.

##### Semantics
* `semantic.v` : Definition of equational reasoning over the terms defined in `term.v`. The type corresponding to the equality between two `terms` is `eqMALG` and we note `A === B` for `eqMALG A B`. The equalities and properties regarding Riesz spaces are in these files (ex Lemma 2.14 in subsection 2.1 of the article).
* `Rsemantic.v` : The equivalent version of `semantic.v` corresponding to `Rterm.v`. `eqMALG` is here `R_eqMALG` and we note `A =R= B` for `R_eqMALG A B`.
* `semantic_Rsemantic_eq.v` : Definition of `NNF` (a function translating `Rterm` to `term`) and `toRterm` (a function translating a `term` into a `Rterm`). Properties regarding `NNF` and `toRterm` as well as proof of the equivalence between `===` and `=R=`.
* `interpretation.v` : Translation of a hypersequent into a `term` as well as properties regarding this translation.

##### Proof system
* `hseq.v` : Definitions of sequents and hypersequents and some properties (like atomicity and complexity), as well as technical lemmas required to manipulate them in Coq.
* `h(m)r.v` : Definitions of the H(M)R system and some basic lemmas.
* `tech_lemmas.v` : Implementation of the lemmas in Section 3.3/4.2.
* `soundness.v` : Proof of soundness (Section 3.4/4.3)).
* `completeness.v` : Proof of completeness (Section 3.5/4.4).
* `invertibility.v` : Proof of the CAN-free invertibility of the logical rules (Section 3.6/4.5)
* `preproof.v` (for HMR only):
* `M_elim.v` : Proof of the M elimination (Section 3.7/4.6)
* `can_elim.v` : Proof of the CAN elimination (Section 3.8/4.7)
* `p_hseq.v` : Definitions of parametrized sequents and parametrized hypersequents and some properties (like atomicity and complexity), as well as technical lemmas required to manipulate them in Coq.
* `decidability.v` : Proof of decidability (Section 3.10/4.8)

##### Aux
* `tactics.v` : Some tactics used in the other files, for instance a tactic that apply every possible logical rules to get an atomic hypersequent.
* `h(m)r_perm_lemmas.v` : Technical construction and lemmas used to help manipulate lists of lists (instead of multisets of multisets like in the article). For instance, they help deal with the exchange rule cases in the proofs by induction.
* `lambda_prop_tools.v` : some tools to make the proofs of Lemmas 3.32, 3.43, 4.26 and 4.43 easier to implement.

#### Utilities
* `Rpos.v` : definition of positive real numbers and some lemmas used to manipulate them.
* `riesz_logic_List_more.v` : additionnal lemmas for lists.
* `FOL_R.v` : definition of First Order Logic over real numbers.
* `lt_nat_tuples.v` : definition of a well-founded order on N², N³ and N⁴, used to ensure terminations (notably to prove decidability).

---

Many thanks to Olivier Laurent, the main contributor of [OLlibs](https://github.com/olaure01/ollibs) that was very helpful for this project.
