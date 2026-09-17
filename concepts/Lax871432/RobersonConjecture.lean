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

Both hypotheses are needed. Union-closedness is no restriction on the conclusion, since every
homomorphism distinguishing closed class is union-closed; it rules out classes whose closure
is strictly larger for a trivial reason. Minor-closedness is the substantial hypothesis, and
the reason the conjecture is of interest: it asserts that the minor-closed classes are exactly
the ones for which homomorphism indistinguishability cannot be sharpened.

At present the conjecture is known only for particular classes. The theorem on taking minors
and preservation under complements of this submission bears on it from the other side: it
yields unconditionally that $\mathrm{cl}(\mathcal{F})$ is itself minor-closed whenever
$\equiv_{\mathcal{F}}$ is preserved under taking complements, without deciding whether
$\mathrm{cl}(\mathcal{F})$ equals $\mathcal{F}$.

This statement is open; nothing in this submission proves it.
-/

open Lax871432.ClosureProperties Lax871432.DistinguishingClosure
open Lax871432.HomomorphismIndistinguishability

namespace Lax871432.RobersonConjecture

/-- **Roberson's conjecture.** Every minor-closed, union-closed class of finite simple graphs
is homomorphism distinguishing closed. -/
axiom isHomDistinguishingClosed_of_isMinorClosed_of_isUnionClosed (𝓕 : GraphClass) :
    IsMinorClosed 𝓕 → IsUnionClosed 𝓕 → IsHomDistinguishingClosed 𝓕

end Lax871432.RobersonConjecture
