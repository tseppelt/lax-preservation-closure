import Lax871432.HomomorphismIndistinguishability

/-!
---
title: The homomorphism distinguishing closure
type: definition
---
Following Roberson (2022), the *homomorphism distinguishing closure* of a graph class
$\mathcal{F}$ is
$$\mathrm{cl}(\mathcal{F}) \coloneqq \{K \mid \forall G, H.\ G \equiv_{\mathcal{F}} H
\Rightarrow \hom(K, G) = \hom(K, H)\},$$
the largest graph class whose homomorphism indistinguishability relation coincides with that
of $\mathcal{F}$. A class is *homomorphism distinguishing closed* if it equals its own
closure, i.e. if adding any further graph strictly refines its homomorphism
indistinguishability relation.

# Implementation notes

`Determines` is stated for an arbitrary graph isomorphism relaxation, not only for
homomorphism indistinguishability over a class: whether a relation pins down the homomorphism
counts from a given graph makes sense for any of them, and the lemma on determined linear
combinations is proved at that generality. The closure operator is the graph class collecting
the graphs that $\equiv_{\mathcal{F}}$ determines.

Membership in the closure is packaged as the one-field structure `Determines` rather than
left as the underlying universally quantified statement. Both carry the same information;
the structure keeps the quantifier from unfolding when a membership hypothesis is used, which
would otherwise strand the `Finite` instances of the implicit vertex types.
-/

open Lax871432.HomomorphismCounts Lax871432.HomomorphismIndistinguishability
open Lax871432.IsomorphismRelaxations

open scoped Lax871432.HomomorphismIndistinguishability

namespace Lax871432.DistinguishingClosure

/-- The relaxation `R` *determines* the homomorphism counts of `K` if related graphs receive
equally many homomorphisms from `K`. -/
structure Determines (R : GraphIsoRelaxation) {U : Type} [Finite U] (K : SimpleGraph U) :
    Prop where
  /-- Graphs related by `R` receive equally many homomorphisms from `K`. -/
  homCount_eq : ∀ {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W),
    R.Rel G H → homCount K G = homCount K H

/-- $\mathrm{cl}(\mathcal{F})$, the homomorphism distinguishing closure of `𝓕`. -/
def cl (𝓕 : GraphClass) : GraphClass where
  Mem K := Determines (homIndRel 𝓕) K
  mem_congr {_ _ _ _ F F'} he := by
    -- Precomposition with the isomorphism is a bijection between the homomorphisms out of
    -- `F` and those out of `F'`, so the two are counted alike into every target.
    obtain ⟨e⟩ := he
    have key : ∀ {W : Type} (K : SimpleGraph W), homCount F K = homCount F' K := fun K =>
      Nat.card_congr
        { toFun f := f.comp e.symm.toHom
          invFun f := f.comp e.toHom
          left_inv _ := by ext a; exact congrArg _ (e.symm_apply_apply a)
          right_inv _ := by ext a; exact congrArg _ (e.apply_symm_apply a) }
    constructor <;> intro h <;> refine ⟨fun G H hGH => ?_⟩
    · rw [← key G, ← key H]; exact h.homCount_eq G H hGH
    · rw [key G, key H]; exact h.homCount_eq G H hGH

/-- `𝓕` is *homomorphism distinguishing closed* if it contains its own closure, i.e. if
adding any graph to `𝓕` strictly refines $\equiv_{\mathcal{F}}$. -/
def IsHomDistinguishingClosed (𝓕 : GraphClass) : Prop :=
  ∀ ⦃V : Type⦄ [Finite V] (F : SimpleGraph V), (cl 𝓕).Mem F → 𝓕.Mem F

end Lax871432.DistinguishingClosure
