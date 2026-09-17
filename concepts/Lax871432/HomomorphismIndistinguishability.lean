import Mathlib.SetTheory.Cardinal.NatCard
import Lax199508.GraphClasses
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

Since $\hom(F, -)$ is an isomorphism invariant, $\equiv_{\mathcal{F}}$ is a graph
isomorphism relaxation; that is how it enters the theorems below, which are stated for an
arbitrary relaxation.

# Implementation notes

A class of finite simple graphs cannot be a `Set` of graphs, since graphs live over arbitrary
vertex types in arbitrary universes. The underlying datum is therefore a predicate on the
concrete graphs `SimpleGraph (Fin n)`, one for each `n` — which is exactly
`Lax199508.GraphClasses.GraphClass`, the notion of a graph class of the *Sparsity Lectures*
submission. It is imported and used as is, so a graph class here is one of those together
with a proof that it is invariant under isomorphism.

The results below need that invariance — the homomorphism distinguishing closure is defined
by a condition on all graphs of a given isomorphism type — so it is carried in the structure
rather than assumed afresh in every statement. `GraphClass.Mem` extends a class to a graph
over an arbitrary finite vertex type by transporting along `Finite.equivFin`; this is no loss
of generality, since every finite graph is isomorphic to a graph on some `Fin n`.
-/

open Lax871432.HomomorphismCounts Lax871432.IsomorphismRelaxations

namespace Lax871432.HomomorphismIndistinguishability

/-- A class of finite simple graphs, given by an isomorphism-invariant predicate on the
graphs `SimpleGraph (Fin m)`. -/
structure GraphClass where
  /-- The graphs of the class with vertex type `Fin m`. -/
  mem : Lax199508.GraphClasses.GraphClass
  /-- The class is invariant under isomorphism. -/
  mem_congr : ∀ {m m' : ℕ} {F : SimpleGraph (Fin m)} {F' : SimpleGraph (Fin m')},
    Nonempty (F ≃g F') → (mem _ F ↔ mem _ F')

/-- A graph over an arbitrary finite vertex type belongs to `𝓕` if the corresponding graph
on `Fin (Nat.card V)` does. -/
def GraphClass.Mem (𝓕 : GraphClass) {V : Type*} [Finite V] (G : SimpleGraph V) : Prop :=
  𝓕.mem _ (SimpleGraph.map (Finite.equivFin V) G)

/-- $G \equiv_{\mathcal{F}} H$: the graphs `G` and `H` receive the same number of
homomorphisms from every graph of `𝓕`. -/
def HomIndistinguishable (𝓕 : GraphClass) {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∀ ⦃m : ℕ⦄ (F : SimpleGraph (Fin m)), 𝓕.mem _ F → homCount F G = homCount F H

@[inherit_doc]
scoped notation:50 G " ≡[" 𝓕 "] " H => HomIndistinguishable 𝓕 G H

/-- Homomorphism indistinguishability over `𝓕`, as a graph isomorphism relaxation. -/
def homIndistinguishability (𝓕 : GraphClass) : Relaxation where
  Rel := @fun V W hV hW G H => @HomIndistinguishable 𝓕 V W hV hW G H
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

end Lax871432.HomomorphismIndistinguishability
