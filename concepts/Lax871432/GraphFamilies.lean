import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
---
title: Graph families
type: definition
---
A finite family of graphs is given by indexing its members: for an index type $\iota$ and a
bound $n$, it assigns to every $i \in \iota$ a graph $F_i$ on at most $n$ vertices. Such a
family is *pairwise non-isomorphic* if $F_i \not\cong F_j$ whenever $i \neq j$, and
*exhaustive* if every graph on at most $n$ vertices is isomorphic to some $F_i$.

# Implementation notes

A *graph family* is an indexed family rather than a set of graphs, so that the index type can
be used to address its members. Its graphs have vertex type `Fin (size i)` for sizes bounded
by `n`; this is no loss of generality, since every finite family of finite graphs has such a
bound, and it keeps matrices over the family indexed by a single type.
-/

namespace Lax871432.GraphFamilies

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

end Lax871432.GraphFamilies
