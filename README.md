# lambda-metric-space
lambda-metric-space, a Lean project

# The Lean Theorem prover
'Lean' is a proof assistant and 'mathlib' is a large mathematical library for 'Lean', in which notions and proofs for a large part of the undergraduate curriculum has been formalized.
https://leanprover.github.io/

# Formalization of Λ-metric spaces and Λ-trees

This project contains two 'Lean'-files. In the first one, 'lambda_metric_space.lean', we build on the already present notion of ordered ablian groups in 'mathlib', to formalize the definition of Λ-metric spaces and Λ-trees as well as some basic definitions and lemmas, for example including reparametrizations of segments. This includes for example Lemma 3.6 from the excellent 'Introduction to Λ-trees' by Ian Chiswell.

In the second file 'lambda_tree_theorem.lean', we formalize some results from a paper '(In)dependence of the axioms of Λ-trees' https://arxiv.org/abs/2112.02704 by the author.

To be precise, we formalize
- Lemma 2 in the paper (this is Lemma 3.6 in Chiswell's book).
- Lemma 4 in the paper.
- The main direction (a) implies (b) of Theorem 1 in the paper.

 Comments are welcome!

