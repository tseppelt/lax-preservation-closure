import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finite.Sum
import Lax871432.GraphProducts
import Lax871432.IsomorphismRelaxations

/-!
---
title: Preservation properties of a graph isomorphism relaxation
type: definition
---
Five properties an equivalence relation $\equiv$ on finite simple graphs may have.

It is *preserved under disjoint unions* if $G \equiv G'$ and $H \equiv H'$ imply
$G + H \equiv G' + H'$, and *preserved under categorical products* if $G \equiv H$ implies
$G \times K \equiv H \times K$ for every graph $K$. It is *preserved under taking
complements* if $G \equiv H$ implies $\overline{G} \equiv \overline{H}$; since
complementation is an involution and $\equiv$ is symmetric, this one implication already gives
the biconditional of the paper.

It is *preserved under left lexicographic products* if $H \equiv H'$ implies
$G \cdot H \equiv G \cdot H'$ for every graph $G$, and *preserved under right lexicographic
products* if $G \equiv G'$ implies $G \cdot H \equiv G' \cdot H$ for every graph $H$. The
special case $H = \overline{K_n}$ of the latter is preservation under blow-ups, which every
homomorphism indistinguishability relation enjoys; arbitrary right lexicographic products are
a genuine restriction.

No property refers to a graph class. Their interest is that for a relation which happens
to be homomorphism indistinguishability over some class, each corresponds exactly to a closure
property of that class.
-/

open Lax871432.GraphProducts Lax871432.IsomorphismRelaxations

open scoped Lax871432.GraphProducts

namespace Lax871432.PreservationProperties

/-- `R` is *preserved under disjoint unions*. -/
def PreservedUnderDisjointUnion (R : GraphIsoRelaxation) : Prop :=
  ∀ {V V' W W' : Type} [Finite V] [Finite V'] [Finite W] [Finite W']
    (G : SimpleGraph V) (G' : SimpleGraph V') (H : SimpleGraph W) (H' : SimpleGraph W'),
    R.Rel G G' → R.Rel H H' → R.Rel (G ⊕g H) (G' ⊕g H')

/-- `R` is *preserved under categorical products*: multiplying both sides by a fixed graph
keeps them related. -/
def PreservedUnderCatProd (R : GraphIsoRelaxation) : Prop :=
  ∀ {V W X : Type} [Finite V] [Finite W] [Finite X]
    (G : SimpleGraph V) (H : SimpleGraph W) (K : SimpleGraph X),
    R.Rel G H → R.Rel (G ×g K) (H ×g K)

/-- `R` is *preserved under left lexicographic products*: multiplying on the left by a fixed
graph keeps related graphs related. -/
def PreservedUnderLeftLexProd (R : GraphIsoRelaxation) : Prop :=
  ∀ {V W W' : Type} [Finite V] [Finite W] [Finite W']
    (G : SimpleGraph V) (H : SimpleGraph W) (H' : SimpleGraph W'),
    R.Rel H H' → R.Rel (lexProd G H) (lexProd G H')

/-- `R` is *preserved under right lexicographic products*: multiplying on the right by a fixed
graph keeps related graphs related. -/
def PreservedUnderRightLexProd (R : GraphIsoRelaxation) : Prop :=
  ∀ {V V' W : Type} [Finite V] [Finite V'] [Finite W]
    (G : SimpleGraph V) (G' : SimpleGraph V') (H : SimpleGraph W),
    R.Rel G G' → R.Rel (lexProd G H) (lexProd G' H)

/-- `R` is *preserved under taking complements*. -/
def PreservedUnderCompl (R : GraphIsoRelaxation) : Prop :=
  ∀ {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W),
    R.Rel G H → R.Rel Gᶜ Hᶜ

end Lax871432.PreservationProperties
