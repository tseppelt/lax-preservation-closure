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

This answers Question 8 of Roberson (2022) affirmatively: if $\equiv_{\mathcal{F}}$ is
preserved under taking complements then $\equiv_{\mathcal{F}}$ coincides with
$\equiv_{\mathcal{F}'}$ for a minor-closed class $\mathcal{F}'$, namely
$\mathcal{F}' = \mathrm{cl}(\mathcal{F})$. Whereas Roberson's conjecture asserts that
$\mathrm{cl}(\mathcal{F})$ coincides with $\mathcal{F}$ for every minor-closed and
union-closed $\mathcal{F}$, assertion (3) holds unconditionally.

The proof writes $\hom(F, \overline{G})$ as a linear combination of $\hom(F', G)$ over the
minors $F'$ of $F$ obtained by deleting and contracting edges, and applies the lemma on
determined linear combinations.
-/

open Lax871432.ClosureProperties Lax871432.DistinguishingClosure
open Lax871432.HomomorphismIndistinguishability Lax871432.PreservationProperties

namespace Lax871432.ForbiddenMinors

/-- **(1) $\Rightarrow$ (2).** If `𝓕` is minor-closed then $\equiv_{\mathcal{F}}$ is
preserved under taking complements. -/
axiom preservedUnderCompl_of_isMinorClosed (𝓕 : GraphClass) :
    IsMinorClosed 𝓕 → PreservedUnderCompl (homIndistinguishability 𝓕)

/-- **(2) $\Leftrightarrow$ (3).** $\equiv_{\mathcal{F}}$ is preserved under taking
complements if and only if $\mathrm{cl}(\mathcal{F})$ is minor-closed. -/
axiom preservedUnderCompl_iff_cl_isMinorClosed (𝓕 : GraphClass) :
    PreservedUnderCompl (homIndistinguishability 𝓕) ↔ IsMinorClosed (cl 𝓕)

end Lax871432.ForbiddenMinors
