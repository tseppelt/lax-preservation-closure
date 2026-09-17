import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Lax871432.DistinguishingClosure

/-!
---
title: Determined linear combinations lie in the closure
type: lemma
---
Let $\mathcal{L}$ be a finite family of pairwise non-isomorphic simple graphs and let
$\alpha_L \neq 0$ for every $L \in \mathcal{L}$. If for all simple graphs $G$ and $H$
$$G \equiv_{\mathcal{F}} H \implies \sum_{L \in \mathcal{L}} \alpha_L \hom(L, G)
= \sum_{L \in \mathcal{L}} \alpha_L \hom(L, H),$$
then $\mathcal{L} \subseteq \mathrm{cl}(\mathcal{F})$.

One says that $\equiv_{\mathcal{F}}$ *determines* the linear combination
$\sum_{L} \alpha_L \hom(L, -)$. Both hypotheses on $\mathcal{L}$ are essential: the members
must be pairwise non-isomorphic and no coefficient may vanish. This lemma is the workhorse
behind the correspondence between closure and preservation properties: a preservation
property of $\equiv_{\mathcal{F}}$ yields a determined linear combination, and the lemma
turns it into a closure property of $\mathrm{cl}(\mathcal{F})$.

Coefficients are taken in $\mathbb{Q}$ rather than $\mathbb{R}$; since homomorphism counts
are natural numbers this is no restriction.
-/

open Lax871432.HomomorphismCounts Lax871432.HomomorphismIndistinguishability
open Lax871432.DistinguishingClosure

open scoped Lax871432.HomomorphismIndistinguishability

namespace Lax871432.LinearCombinationLemma

/-- A linear combination of homomorphism counts over pairwise non-isomorphic graphs, with
nonzero coefficients, that is determined by $\equiv_{\mathcal{F}}$ places every one of those
graphs in $\mathrm{cl}(\mathcal{F})$. -/
axiom mem_cl_of_determines (𝓕 : GraphClass) {ι : Type} [Fintype ι] {size : ι → ℕ}
    (L : ∀ i, SimpleGraph (Fin (size i)))
    (hL : ∀ i j, i ≠ j → IsEmpty (L i ≃g L j))
    (α : ι → ℚ) (hα : ∀ i, α i ≠ 0)
    (hdet : ∀ {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W),
      (G ≡[𝓕] H) →
        ∑ i, α i * (homCount (L i) G : ℚ) = ∑ i, α i * (homCount (L i) H : ℚ))
    (i : ι) : (cl 𝓕).Mem (L i)

end Lax871432.LinearCombinationLemma
