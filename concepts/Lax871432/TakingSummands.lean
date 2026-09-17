import Lax871432.ClosureProperties
import Lax871432.DistinguishingClosure
import Lax871432.PreservationProperties

/-!
---
title: Taking summands and preservation under disjoint unions
type: theorem
---
For a graph class $\mathcal{F}$ and the assertions

1. $\mathcal{F}$ is closed under taking summands,
2. the relaxation $\equiv_{\mathcal{F}}$ is preserved under disjoint unions,
3. $\mathrm{cl}(\mathcal{F})$ is closed under taking summands,

the implications (1) $\Rightarrow$ (2) $\Leftrightarrow$ (3) hold.

This answers a question of Roberson (2022, p. 7) affirmatively. Closure under taking
summands is the mildest of the closure properties considered in this context, and the
equivalence (2) $\Leftrightarrow$ (3) is the first instance of the general correspondence
between closure properties of a graph class and preservation properties of the relaxation it
induces. Read from right to left it says which relations can be homomorphism
indistinguishability over a summand-closed class at all.
-/

open Lax871432.ClosureProperties Lax871432.DistinguishingClosure
open Lax871432.HomomorphismIndistinguishability Lax871432.PreservationProperties

namespace Lax871432.TakingSummands

/-- **(1) $\Rightarrow$ (2).** If `𝓕` is closed under taking summands then
$\equiv_{\mathcal{F}}$ is preserved under disjoint unions. -/
axiom preservedUnderDisjointUnion_of_isSummandClosed (𝓕 : GraphClass) :
    IsSummandClosed 𝓕 → PreservedUnderDisjointUnion (homIndistinguishability 𝓕)

/-- **(2) $\Leftrightarrow$ (3).** $\equiv_{\mathcal{F}}$ is preserved under disjoint unions
if and only if $\mathrm{cl}(\mathcal{F})$ is closed under taking summands. -/
axiom preservedUnderDisjointUnion_iff_cl_isSummandClosed (𝓕 : GraphClass) :
    PreservedUnderDisjointUnion (homIndistinguishability 𝓕) ↔ IsSummandClosed (cl 𝓕)

end Lax871432.TakingSummands
