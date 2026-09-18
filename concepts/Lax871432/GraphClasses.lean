import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
---
title: Graph classes
type: definition
---
A *graph class* is a class $\mathcal{F}$ of finite simple graphs which is closed under
isomorphism: if $F \in \mathcal{F}$ and $F \cong F'$, then $F' \in \mathcal{F}$.

# Implementation notes

A class of finite simple graphs cannot be a `Set` of graphs, since graphs live over arbitrary
vertex types. The underlying datum is therefore a predicate on the finite simple graphs over
an arbitrary vertex type, together with a proof that it is invariant under isomorphism.

The results about graph classes need that invariance — the homomorphism distinguishing
closure is defined by a condition on all graphs of a given isomorphism type — so it is carried
in the structure rather than assumed afresh in every statement.

The vertex types range over `Type` rather than over an arbitrary universe, matching the
quantifiers of `GraphIsoRelaxation`. A universe-polymorphic `Mem` is not available here: a
`Type*` in a structure field is not quantified inside the field, it becomes a parameter of
`GraphClass` itself, so a class would be tied to one fixed universe instead of covering them
all. Fixing `Type` is no loss of generality either, since every finite graph is isomorphic to
a graph on some `Fin n` and membership is invariant under isomorphism.
-/

namespace Lax871432.GraphClasses

/-- A class of finite simple graphs, given by an isomorphism-invariant predicate on the
finite simple graphs. -/
structure GraphClass where
  /-- The graphs of the class. -/
  Mem : ∀ {V : Type} [Finite V], SimpleGraph V → Prop
  /-- The class is invariant under isomorphism. -/
  mem_congr : ∀ {V W : Type} [Finite V] [Finite W] {F : SimpleGraph V} {F' : SimpleGraph W},
    Nonempty (F ≃g F') → (Mem F ↔ Mem F')

end Lax871432.GraphClasses
