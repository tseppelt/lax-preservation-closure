import Lax871432.ClosureProperties
import Lax871432.DistinguishingClosure

/-!
---
title: Roberson's conjecture
type: conjecture
---
Roberson (2022) conjectured that every graph class closed under taking minors and disjoint
unions is homomorphism distinguishing closed: for such a class $\mathcal{F}$, adding any
further graph to $\mathcal{F}$ strictly refines $\equiv_{\mathcal{F}}$.
-/

open Lax871432.ClosureProperties Lax871432.DistinguishingClosure
open Lax871432.GraphClasses

namespace Lax871432.RobersonConjecture

/-- **Roberson's conjecture.** Every minor-closed, union-closed class of finite simple graphs
is homomorphism distinguishing closed. -/
axiom isHomDistinguishingClosed_of_isMinorClosed_of_isUnionClosed (𝓕 : GraphClass) :
    IsMinorClosed 𝓕 → IsUnionClosed 𝓕 → IsHomDistinguishingClosed 𝓕

end Lax871432.RobersonConjecture
