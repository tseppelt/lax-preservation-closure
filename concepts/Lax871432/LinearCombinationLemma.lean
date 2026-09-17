import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Lax871432.DistinguishingClosure
import Lax871432.PreservationProperties

/-!
---
title: A determined linear combination determines its constituents
type: lemma
---
Let $\equiv$ be a graph isomorphism relaxation preserved under categorical products, let
$\mathcal{L}$ be a finite family of pairwise non-isomorphic simple graphs, and let
$\alpha_L \neq 0$ for every $L \in \mathcal{L}$. If $\equiv$ determines the linear combination
$\sum_{L \in \mathcal{L}} \alpha_L \hom(L, -)$ — that is, if $G \equiv H$ implies
$$\sum_{L \in \mathcal{L}} \alpha_L \hom(L, G) = \sum_{L \in \mathcal{L}} \alpha_L \hom(L, H)$$
— then it determines each constituent $\hom(L, -)$ separately.
-/

open Lax871432.DistinguishingClosure Lax871432.HomomorphismCounts
open Lax871432.IsomorphismRelaxations Lax871432.PreservationProperties

namespace Lax871432.LinearCombinationLemma

/-- A relaxation preserved under categorical products which determines a linear combination of
homomorphism counts, over pairwise non-isomorphic graphs and with nonzero coefficients,
determines each of its constituents. -/
axiom determines_of_determines_sum (R : GraphIsoRelaxation) (hprod : PreservedUnderCatProd R)
    {ι : Type} [Fintype ι] {size : ι → ℕ} (L : ∀ i, SimpleGraph (Fin (size i)))
    (hL : ∀ i j, i ≠ j → IsEmpty (L i ≃g L j))
    (α : ι → ℚ) (hα : ∀ i, α i ≠ 0)
    (hdet : ∀ {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W),
      R.Rel G H →
        ∑ i, α i * (homCount (L i) G : ℚ) = ∑ i, α i * (homCount (L i) H : ℚ))
    (i : ι) : Determines R (L i)

end Lax871432.LinearCombinationLemma
