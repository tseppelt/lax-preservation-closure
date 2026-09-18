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

# Implementation notes

The class is assumed to be nonempty. The empty class is closed under taking minors and
disjoint unions, but it is not homomorphism distinguishing closed: the graph with no vertices
has exactly one homomorphism into every graph, so it lies in $\mathrm{cl}(\emptyset)$. For a
nonempty minor-closed class the question does not arise, since the graph with no vertices is
a minor of every graph and hence belongs to the class.
-/

open Lax871432.ClosureProperties Lax871432.DistinguishingClosure
open Lax871432.GraphClasses

namespace Lax871432.RobersonConjecture

/-- **Roberson's conjecture.** Every nonempty, minor-closed, union-closed class of finite
simple graphs is homomorphism distinguishing closed. -/
axiom isHomDistinguishingClosed_of_isMinorClosed_of_isUnionClosed (𝓕 : GraphClass)
    (hne : ∃ (n : ℕ) (F : SimpleGraph (Fin n)), 𝓕.Mem F) :
    IsMinorClosed 𝓕 → IsUnionClosed 𝓕 → IsHomDistinguishingClosed 𝓕

end Lax871432.RobersonConjecture
