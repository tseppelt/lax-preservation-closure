import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finite.Sum
import Lax871432.GraphProducts
import Lax871432.IsomorphismRelaxations

/-!
---
title: Preservation properties of a graph isomorphism relaxation
type: definition
---
Three properties an equivalence relation $\equiv$ on finite simple graphs may have.

It is *preserved under disjoint unions* if $G \equiv G'$ and $H \equiv H'$ imply
$G + H \equiv G' + H'$, and *preserved under categorical products* if $G \equiv H$ implies
$G \times K \equiv H \times K$ for every graph $K$. It is *preserved under taking
complements* if $G \equiv H$ implies $\overline{G} \equiv \overline{H}$; since
complementation is an involution and $\equiv$ is symmetric, this one implication already gives
the biconditional of the paper.

Neither property refers to a graph class. Their interest is that for a relation which happens
to be homomorphism indistinguishability over some class, each corresponds exactly to a closure
property of that class.
-/

open Lax871432.GraphProducts Lax871432.IsomorphismRelaxations

open scoped Lax871432.GraphProducts

namespace Lax871432.PreservationProperties

/-- `R` is *preserved under disjoint unions*. -/
def PreservedUnderDisjointUnion (R : Relaxation) : Prop :=
  ∀ {V V' W W' : Type} [Finite V] [Finite V'] [Finite W] [Finite W']
    (G : SimpleGraph V) (G' : SimpleGraph V') (H : SimpleGraph W) (H' : SimpleGraph W'),
    R.Rel G G' → R.Rel H H' → R.Rel (G ⊕g H) (G' ⊕g H')

/-- `R` is *preserved under categorical products*: multiplying both sides by a fixed graph
keeps them related. -/
def PreservedUnderCatProd (R : Relaxation) : Prop :=
  ∀ {V W X : Type} [Finite V] [Finite W] [Finite X]
    (G : SimpleGraph V) (H : SimpleGraph W) (K : SimpleGraph X),
    R.Rel G H → R.Rel (G ×g K) (H ×g K)

/-- `R` is *preserved under taking complements*. -/
def PreservedUnderCompl (R : Relaxation) : Prop :=
  ∀ {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W),
    R.Rel G H → R.Rel Gᶜ Hᶜ

end Lax871432.PreservationProperties
