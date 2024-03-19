This repository contains Agda files related to my master's thesis, "A Survey on Homotopy Type Theory with the Proof Assistant Agda".
The below is a description on each file.

* **thesis-1.lagda.md** : Introduces notations for type universes.

* **thesis-2.lagda.md** : Introduces basic type constructors and their related elementary propositions.

* **thesis-3-htpy.lagda.md** : Define the concept of a homotopy between (dependent) functions.

* **thesis-3-equiv.lagda.md** : Define the concept of an equivalence of types.

* **thesis-3-hlvl.lagda.md** : Define the notion of h-level and proves that set is closed under disjoint sum +.

* **thesis-4-fext.lagda.md** : Axiomatize the function extensionality.

* **thesis-4-ua.lagda.md** : Axiomatize the univalence axiom.

* **thesis-4-hit.lagda.md** : Declare the homotopy pushout as a higher inductive type and define n-dimensional circles.

* **thesis-5.lagda.md** : Prove that the fundamental group of the circle is $\mathbb{Z}$ by constructing the universal cover.


# Abstract
Homotopy Type Theory (abbreviated to HoTT) is a new field of mathematics lying on the intersection of homotopy theory in mathematics and type theory in computer science. Type theory is a sort of formal system like first order logic (on which ZFC set theory is based), which originated from Russell’s book, Principia Mathematica, and was developed independently by computer scientists and logicians to present. The word "type theory" may refer to the common framework shared by formal systems belonging to this field, or may refer to each individual formal system. HoTT is a formal system as one of those individual formal systems, and HoTT itself contains various phenomena that can be interpreted homotopically, enabling it to be a new foundation of mathematics related to homotopy theory. In particular, type theory has the advantage of being easy to be transplanted into computers, and through this many proofs of homotopy theory have already been formalized with the language of HoTT in proof assistants such as Agda and Coq. In summary, HoTT is a new formal system with the ease of computer implementation, which can synthetically explore homotopy theory. Since the informal descriptions of this new theory have already been introduced in good textbooks, this paper addresses how the definitions and theorems of this formal system can be formalized in the Agda proof assistant. Especially, it aims to formalize that the fundamental group of $S^1$ is equal to $\mathbb{Z}$.
