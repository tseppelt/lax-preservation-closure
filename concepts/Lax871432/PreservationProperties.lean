import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finite.Sum
import Lax871432.HomomorphismIndistinguishability

/-!
---
title: Preservation properties of homomorphism indistinguishability
type: definition
---
Two preservation properties of the relation $\equiv_{\mathcal{F}}$.

It is *preserved under disjoint unions* if $G \equiv_{\mathcal{F}} G'$ and
$H \equiv_{\mathcal{F}} H'$ imply $G + H \equiv_{\mathcal{F}} G' + H'$. It is *preserved
under taking complements* if $G \equiv_{\mathcal{F}} H$ implies
$\overline{G} \equiv_{\mathcal{F}} \overline{H}$; since complementation is an involution,
this one implication already gives the biconditional of the paper.
-/

open Lax871432.HomomorphismIndistinguishability

open scoped Lax871432.HomomorphismIndistinguishability

namespace Lax871432.PreservationProperties

/-- $\equiv_{\mathcal{F}}$ is *preserved under disjoint unions*. -/
def PreservedUnderDisjointUnion (𝓕 : GraphClass) : Prop :=
  ∀ {V V' W W' : Type} [Finite V] [Finite V'] [Finite W] [Finite W']
    (G : SimpleGraph V) (G' : SimpleGraph V') (H : SimpleGraph W) (H' : SimpleGraph W'),
    (G ≡[𝓕] G') → (H ≡[𝓕] H') → ((G ⊕g H) ≡[𝓕] (G' ⊕g H'))

/-- $\equiv_{\mathcal{F}}$ is *preserved under taking complements*. -/
def PreservedUnderCompl (𝓕 : GraphClass) : Prop :=
  ∀ {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W),
    (G ≡[𝓕] H) → (Gᶜ ≡[𝓕] Hᶜ)

end Lax871432.PreservationProperties
