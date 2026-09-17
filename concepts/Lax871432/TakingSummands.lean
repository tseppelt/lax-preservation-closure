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
-/

open Lax871432.ClosureProperties Lax871432.DistinguishingClosure
open Lax871432.HomomorphismIndistinguishability Lax871432.PreservationProperties

namespace Lax871432.TakingSummands

/-- **(1) $\Rightarrow$ (2).** If `𝓕` is closed under taking summands then
$\equiv_{\mathcal{F}}$ is preserved under disjoint unions. -/
axiom preservedUnderDisjointUnion_of_isSummandClosed (𝓕 : GraphClass) :
    IsSummandClosed 𝓕 → PreservedUnderDisjointUnion (homIndRel 𝓕)

/-- **(2) $\Leftrightarrow$ (3).** $\equiv_{\mathcal{F}}$ is preserved under disjoint unions
if and only if $\mathrm{cl}(\mathcal{F})$ is closed under taking summands. -/
axiom preservedUnderDisjointUnion_iff_cl_isSummandClosed (𝓕 : GraphClass) :
    PreservedUnderDisjointUnion (homIndRel 𝓕) ↔ IsSummandClosed (cl 𝓕)

end Lax871432.TakingSummands
