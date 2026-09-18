import Mathlib.SetTheory.Cardinal.NatCard
import Lax871432.GraphClasses
import Lax871432.HomomorphismCounts
import Lax871432.IsomorphismRelaxations

/-!
---
title: Homomorphism indistinguishability
type: definition
---
Two graphs $G$ and $H$ are *homomorphism indistinguishable over a class $\mathcal{F}$*,
written $G \equiv_{\mathcal{F}} H$, if $\hom(F, G) = \hom(F, H)$ for every
$F \in \mathcal{F}$.

Since $\hom(F, -)$ is an isomorphism invariant, this is a graph isomorphism relaxation, and
it is defined as one: `homIndRel 𝓕` is the relaxation itself, and
$G \equiv_{\mathcal{F}} H$ is notation for the relation it carries.
-/

open Lax871432.GraphClasses Lax871432.HomomorphismCounts Lax871432.IsomorphismRelaxations

namespace Lax871432.HomomorphismIndistinguishability

/-- *Homomorphism indistinguishability over `𝓕`*: the graph isomorphism relaxation relating
two graphs when they receive the same number of homomorphisms from every graph of `𝓕`. -/
def homIndRel (𝓕 : GraphClass) : GraphIsoRelaxation where
  Rel := @fun _ _ _ _ G H =>
    ∀ ⦃m : ℕ⦄ (F : SimpleGraph (Fin m)), 𝓕.Mem F → homCount F G = homCount F H
  rel_of_iso := by
    -- Postcomposing with the isomorphism is a bijection between the two hom-sets, so
    -- isomorphic graphs receive equally many homomorphisms from every graph.
    rintro V W _ _ G H ⟨e⟩ m F -
    exact Nat.card_congr
      { toFun f := e.toHom.comp f
        invFun f := e.symm.toHom.comp f
        left_inv _ := by ext a; simp
        right_inv _ := by ext a; simp }
  symm := by
    intro V W _ _ G H h m F hF
    exact (h F hF).symm
  trans := by
    intro U V W _ _ _ G H K h h' m F hF
    exact (h F hF).trans (h' F hF)

@[inherit_doc homIndRel]
scoped notation:50 G " ≡[" 𝓕 "] " H => GraphIsoRelaxation.Rel (homIndRel 𝓕) G H

end Lax871432.HomomorphismIndistinguishability
