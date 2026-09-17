import Mathlib.SetTheory.Cardinal.NatCard
import Lax871432.HomomorphismCounts

/-!
---
title: Homomorphism indistinguishability
type: definition
---
Two graphs $G$ and $H$ are *homomorphism indistinguishable over a class $\mathcal{F}$*,
written $G \equiv_{\mathcal{F}} H$, if $\hom(F, G) = \hom(F, H)$ for every
$F \in \mathcal{F}$.

# Implementation notes

A class of finite simple graphs cannot be a `Set` of graphs, since graphs live over
arbitrary vertex types in arbitrary universes. A `GraphClass` is instead an
isomorphism-invariant predicate on the concrete graphs `SimpleGraph (Fin m)`, and
`GraphClass.Mem` extends it to a graph over an arbitrary finite vertex type by transporting
along `Finite.equivFin`. This is no loss of generality — every finite graph is isomorphic
to one of this form — and it makes isomorphism invariance structural rather than a
hypothesis carried around.
-/

open Lax871432.HomomorphismCounts

namespace Lax871432.HomomorphismIndistinguishability

/-- A class of finite simple graphs, given by an isomorphism-invariant predicate on the
graphs `SimpleGraph (Fin m)`. -/
structure GraphClass where
  /-- The graphs of the class with vertex type `Fin m`. -/
  mem : ∀ ⦃m : ℕ⦄, SimpleGraph (Fin m) → Prop
  /-- The class is invariant under isomorphism. -/
  mem_congr : ∀ {m m' : ℕ} {F : SimpleGraph (Fin m)} {F' : SimpleGraph (Fin m')},
    Nonempty (F ≃g F') → (mem F ↔ mem F')

/-- A graph over an arbitrary finite vertex type belongs to `𝓕` if the corresponding graph
on `Fin (Nat.card V)` does. -/
def GraphClass.Mem (𝓕 : GraphClass) {V : Type*} [Finite V] (G : SimpleGraph V) : Prop :=
  𝓕.mem (SimpleGraph.map (Finite.equivFin V) G)

/-- $G \equiv_{\mathcal{F}} H$: the graphs `G` and `H` receive the same number of
homomorphisms from every graph of `𝓕`. -/
def HomIndistinguishable (𝓕 : GraphClass) {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∀ ⦃m : ℕ⦄ (F : SimpleGraph (Fin m)), 𝓕.mem F → homCount F G = homCount F H

@[inherit_doc]
scoped notation:50 G " ≡[" 𝓕 "] " H => HomIndistinguishable 𝓕 G H

end Lax871432.HomomorphismIndistinguishability
