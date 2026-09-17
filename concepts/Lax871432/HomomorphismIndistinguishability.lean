import Mathlib.SetTheory.Cardinal.NatCard
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

# Implementation notes

A class of finite simple graphs cannot be a `Set` of graphs, since graphs live over arbitrary
vertex types. The underlying datum is therefore a predicate on the finite simple graphs over
an arbitrary vertex type, together with a proof that it is invariant under isomorphism.

The results below need that invariance — the homomorphism distinguishing closure is defined
by a condition on all graphs of a given isomorphism type — so it is carried in the structure
rather than assumed afresh in every statement.

The vertex types range over `Type` rather than over an arbitrary universe, matching the
quantifiers of `GraphIsoRelaxation`. A universe-polymorphic `Mem` is not available here: a
`Type*` in a structure field is not quantified inside the field, it becomes a parameter of
`GraphClass` itself, so a class would be tied to one fixed universe instead of covering them
all. Fixing `Type` is no loss of generality either, since every finite graph is isomorphic to
a graph on some `Fin n` and membership is invariant under isomorphism.
-/

open Lax871432.HomomorphismCounts Lax871432.IsomorphismRelaxations

namespace Lax871432.HomomorphismIndistinguishability

/-- A class of finite simple graphs, given by an isomorphism-invariant predicate on the
finite simple graphs. -/
structure GraphClass where
  /-- The graphs of the class. -/
  Mem : ∀ {V : Type} [Finite V], SimpleGraph V → Prop
  /-- The class is invariant under isomorphism. -/
  mem_congr : ∀ {V W : Type} [Finite V] [Finite W] {F : SimpleGraph V} {F' : SimpleGraph W},
    Nonempty (F ≃g F') → (Mem F ↔ Mem F')

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
