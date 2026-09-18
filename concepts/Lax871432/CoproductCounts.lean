import Mathlib.Combinatorics.SimpleGraph.Sum
import Lax871432.HomomorphismCounts

/-!
---
title: Homomorphism counts from a disjoint union
type: lemma
---
For simple graphs $F_1$, $F_2$ and $G$,
$$\hom(F_1 + F_2, G) = \hom(F_1, G) \hom(F_2, G),$$
where $F_1 + F_2$ denotes the disjoint union of $F_1$ and $F_2$.
-/

open Lax871432.HomomorphismCounts

namespace Lax871432.CoproductCounts

/-- A homomorphism from a disjoint union is a pair of homomorphisms from its two parts. -/
axiom homCount_sum_left {U V W : Type*} [Finite U] [Finite V] [Finite W] (F₁ : SimpleGraph U)
    (F₂ : SimpleGraph V) (G : SimpleGraph W) :
    homCount (F₁ ⊕g F₂) G = homCount F₁ G * homCount F₂ G

end Lax871432.CoproductCounts
