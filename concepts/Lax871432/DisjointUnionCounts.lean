import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Sum
import Lax871432.HomomorphismCounts

/-!
---
title: Homomorphism counts into a disjoint union
type: lemma
---
For a connected simple graph $K$ and simple graphs $G_1$ and $G_2$,
$$\hom(K, G_1 + G_2) = \hom(K, G_1) + \hom(K, G_2),$$
where $G_1 + G_2$ denotes the disjoint union of $G_1$ and $G_2$.
-/

open Lax871432.HomomorphismCounts

namespace Lax871432.DisjointUnionCounts

/-- A homomorphism from a connected graph into a disjoint union maps into one of its two
parts. -/
axiom homCount_sum_right {U V W : Type*} [Finite U] [Finite V] [Finite W] (K : SimpleGraph U)
    (hK : K.Connected) (G₁ : SimpleGraph V) (G₂ : SimpleGraph W) :
    homCount K (G₁ ⊕g G₂) = homCount K G₁ + homCount K G₂

end Lax871432.DisjointUnionCounts
