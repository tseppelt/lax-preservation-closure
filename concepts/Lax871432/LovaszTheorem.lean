import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Lax871432.GraphFamilies
import Lax871432.HomomorphismCounts

/-!
---
title: Lovász's theorem
type: theorem
---
Lovász (1967): two finite graphs are isomorphic if and only if they are homomorphism
indistinguishable over all graphs, i.e. if and only if $\hom(K, G) = \hom(K, H)$ for every
graph $K$.

It suffices to test the graphs $K$ on vertex set $\{0, \dots, m-1\}$, since every finite
graph is isomorphic to one of these and $\hom(-, G)$ is an isomorphism invariant.

The theorem is deduced from the invertibility of the *homomorphism matrix* of a family of
graphs. Let $F_1, \dots, F_N$ be pairwise non-isomorphic graphs on at most $n$ vertices which
represent every isomorphism class of graphs on at most $n$ vertices. Then the matrix
$M_{ij} = \hom(F_i, F_j)$ is invertible over $\mathbb{Q}$.

# Implementation notes

The family $F_1, \dots, F_N$ is a `GraphFamily`, indexed by a type `ι` that then also indexes
the rows and columns of the matrix.
-/

open Lax871432.GraphFamilies Lax871432.HomomorphismCounts

namespace Lax871432.LovaszTheorem

variable {n : ℕ} {ι : Type*}

/-- The *homomorphism matrix* of a graph family, `M i j = hom(F i, F j)`. -/
noncomputable def homMatrix (F : GraphFamily n ι) : Matrix ι ι ℚ :=
  Matrix.of fun i j => (homCount (F.graph i) (F.graph j) : ℚ)

/-- **Lovász's homomorphism matrix lemma.** For a finite family of pairwise non-isomorphic
graphs on at most `n` vertices which represents every isomorphism class of graphs on at most
`n` vertices, the matrix of homomorphism counts between its members is invertible. -/
axiom homMatrix_isUnit [Fintype ι] [DecidableEq ι] (F : GraphFamily n ι)
    (hni : F.PairwiseNonIso) (hF : F.IsExhaustive) : IsUnit (homMatrix F)

/-- **Lovász's theorem.** Finite graphs with equal homomorphism counts from every graph are
isomorphic, and conversely. -/
axiom nonempty_iso_iff_forall_homCount_eq {V W : Type} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    (∀ (m : ℕ) (K : SimpleGraph (Fin m)), homCount K G = homCount K H) ↔ Nonempty (G ≃g H)

end Lax871432.LovaszTheorem
