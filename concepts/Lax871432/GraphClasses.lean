import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Order.SetNotation

/-!
---
title: Graph classes
type: definition
---
A *graph class* is a class $\mathcal{F}$ of finite simple graphs which is closed under
isomorphism: if $F \in \mathcal{F}$ and $F \cong F'$, then $F' \in \mathcal{F}$.

Graph classes are ordered by inclusion, $\mathcal{F} \subseteq \mathcal{F}'$, written
`𝓕 ≤ 𝓕'`. The intersection $\bigcap_{i \in I} \mathcal{F}_i$ and the union
$\bigcup_{i \in I} \mathcal{F}_i$ of a family of graph classes are again graph classes,
written `⨅ i, 𝓕 i` and `⨆ i, 𝓕 i`.

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

/-- Inclusion of graph classes: `𝓕 ≤ 𝓕'` if every graph in `𝓕` is in `𝓕'`. -/
instance : PartialOrder GraphClass where
  le 𝓕 𝓕' := ∀ ⦃V : Type⦄ [Finite V] (F : SimpleGraph V), 𝓕.Mem F → 𝓕'.Mem F
  le_refl _ _ _ _ hF := hF
  le_trans _ _ _ h h' _ _ F hF := h' F (h F hF)
  le_antisymm := by
    rintro ⟨Mem, _⟩ ⟨Mem', _⟩ h h'
    have : @Mem = @Mem' := by
      funext V _ F
      exact propext ⟨h F, h' F⟩
    subst this
    rfl

/-- The intersection of a set of graph classes: the graphs lying in each of them. The
intersection of a family is written `⨅ i, 𝓕 i`. -/
instance : InfSet GraphClass where
  sInf S :=
    { Mem F := ∀ 𝓕 ∈ S, 𝓕.Mem F
      mem_congr he :=
        forall_congr' fun 𝓕 : GraphClass => imp_congr_right fun _ => 𝓕.mem_congr he }

/-- The union of a set of graph classes: the graphs lying in at least one of them. The union
of a family is written `⨆ i, 𝓕 i`. -/
instance : SupSet GraphClass where
  sSup S :=
    { Mem F := ∃ 𝓕 ∈ S, 𝓕.Mem F
      mem_congr he := exists_congr fun 𝓕 : GraphClass => and_congr_right' (𝓕.mem_congr he) }

end Lax871432.GraphClasses
