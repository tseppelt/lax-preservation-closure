import Lax871432.ClosureProperties
import Lax871432.DistinguishingClosure
import Lax871432.PreservationProperties

/-!
---
title: Taking minors and preservation under complements
type: theorem
---
For a graph class $\mathcal{F}$ and the assertions

1. $\mathcal{F}$ is minor-closed,
2. the relaxation $\equiv_{\mathcal{F}}$ is preserved under taking complements,
3. $\mathrm{cl}(\mathcal{F})$ is minor-closed,

the implications (1) $\Rightarrow$ (2) $\Leftrightarrow$ (3) hold.
-/

open Lax871432.ClosureProperties Lax871432.DistinguishingClosure
open Lax871432.GraphClasses
open Lax871432.HomomorphismIndistinguishability Lax871432.PreservationProperties

namespace Lax871432.MinorsComplements

/-- **(1) $\Rightarrow$ (2).** If `𝓕` is minor-closed then $\equiv_{\mathcal{F}}$ is
preserved under taking complements. -/
axiom preservedUnderCompl_of_isMinorClosed (𝓕 : GraphClass) :
    IsMinorClosed 𝓕 → PreservedUnderCompl (homIndRel 𝓕)

/-- **(2) $\Leftrightarrow$ (3).** $\equiv_{\mathcal{F}}$ is preserved under taking
complements if and only if $\mathrm{cl}(\mathcal{F})$ is minor-closed. -/
axiom preservedUnderCompl_iff_cl_isMinorClosed (𝓕 : GraphClass) :
    PreservedUnderCompl (homIndRel 𝓕) ↔ IsMinorClosed (cl 𝓕)

end Lax871432.MinorsComplements
