import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finite.Sum
import Lax68.GraphMinors
import Lax871432.HomomorphismIndistinguishability

/-!
---
title: Closure properties of graph classes
type: definition
---
Three closure properties of a class $\mathcal{F}$ of finite simple graphs.

$\mathcal{F}$ is *closed under taking summands* if $F_1 + F_2 \in \mathcal{F}$ implies
$F_1 \in \mathcal{F}$ and $F_2 \in \mathcal{F}$, where $+$ denotes disjoint union, and
*union-closed* if conversely $F_1, F_2 \in \mathcal{F}$ implies
$F_1 + F_2 \in \mathcal{F}$. It is *minor-closed* if every minor of a member is a member.

Minors are taken from `Lax68.GraphMinors`: $K$ is a minor of $F$ when the vertices of $K$ can
be represented by pairwise disjoint connected branch sets in $F$, with an edge of $F$ joining
the corresponding branch sets for every edge of $K$.
-/

open Lax871432.HomomorphismIndistinguishability

namespace Lax871432.ClosureProperties

/-- `𝓕` is *closed under taking summands* if both summands of a disjoint union in the class
are themselves in the class. -/
def IsSummandClosed (𝓕 : GraphClass) : Prop :=
  ∀ {V W : Type} [Finite V] [Finite W] (F₁ : SimpleGraph V) (F₂ : SimpleGraph W),
    𝓕.Mem (F₁ ⊕g F₂) → 𝓕.Mem F₁ ∧ 𝓕.Mem F₂

/-- `𝓕` is *union-closed* if the disjoint union of two members is a member. -/
def IsUnionClosed (𝓕 : GraphClass) : Prop :=
  ∀ {V W : Type} [Finite V] [Finite W] (F₁ : SimpleGraph V) (F₂ : SimpleGraph W),
    𝓕.Mem F₁ → 𝓕.Mem F₂ → 𝓕.Mem (F₁ ⊕g F₂)

/-- `𝓕` is *minor-closed* if every minor of a member is a member. -/
def IsMinorClosed (𝓕 : GraphClass) : Prop :=
  ∀ {V W : Type} [Finite V] [Finite W] {F : SimpleGraph V} (K : SimpleGraph W),
    Lax68.GraphMinors.IsMinor K F → 𝓕.Mem F → 𝓕.Mem K

end Lax871432.ClosureProperties
