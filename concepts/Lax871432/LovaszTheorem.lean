import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
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

A *graph family* is an indexed family rather than a set of graphs, so that the index type can
be used to address its members. Its graphs have vertex type `Fin (size i)` for sizes bounded
by `n`; this is no loss of generality, and it keeps the matrix indexed by a single type.
-/

open Lax871432.HomomorphismCounts

namespace Lax871432.LovaszTheorem

/-- An *indexed graph family* of order `n`: a family of simple graphs indexed by `ι`, the
`i`-th of which has vertex set `Fin (size i)` for some `size i ≤ n`. -/
structure GraphFamily (n : ℕ) (ι : Type*) where
  /-- The number of vertices of the `i`-th graph. -/
  size : ι → ℕ
  /-- Every graph in the family has at most `n` vertices. -/
  size_le : ∀ i, size i ≤ n
  /-- The `i`-th graph of the family. -/
  graph : ∀ i, SimpleGraph (Fin (size i))

variable {n : ℕ} {ι : Type*}

/-- Two indices carry isomorphic graphs. -/
def GraphFamily.Iso (F : GraphFamily n ι) (i j : ι) : Prop :=
  Nonempty (F.graph i ≃g F.graph j)

/-- The graphs in the family are pairwise non-isomorphic. -/
def GraphFamily.PairwiseNonIso (F : GraphFamily n ι) : Prop :=
  Pairwise fun i j => ¬ F.Iso i j

/-- The family represents every isomorphism class of graphs on at most `n` vertices. -/
def GraphFamily.IsExhaustive (F : GraphFamily n ι) : Prop :=
  ∀ m ≤ n, ∀ G : SimpleGraph (Fin m), ∃ i, Nonempty (G ≃g F.graph i)

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
