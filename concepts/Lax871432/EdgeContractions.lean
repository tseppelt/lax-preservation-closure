import Lax871432.ClosureProperties
import Lax871432.DistinguishingClosure
import Lax871432.PreservationProperties

/-!
---
title: Contracting edges and right lexicographic products
type: theorem
---
For a graph class $\mathcal{F}$ and the assertions

1. $\mathcal{F}$ is closed under contracting edges,
2. the relaxation $\equiv_{\mathcal{F}}$ is preserved under right lexicographic products,
3. $\mathrm{cl}(\mathcal{F})$ is closed under contracting edges,

the implications (1) $\Rightarrow$ (2) $\Leftrightarrow$ (3) hold.
-/

open Lax871432.ClosureProperties Lax871432.DistinguishingClosure
open Lax871432.HomomorphismIndistinguishability Lax871432.PreservationProperties

namespace Lax871432.EdgeContractions

/-- **(1) $\Rightarrow$ (2).** -/
axiom preservedUnderRightLexProd_of_isContractionClosed (𝓕 : GraphClass) :
    IsContractionClosed 𝓕 → PreservedUnderRightLexProd (homIndRel 𝓕)

/-- **(2) $\Leftrightarrow$ (3).** -/
axiom preservedUnderRightLexProd_iff_cl_isContractionClosed (𝓕 : GraphClass) :
    PreservedUnderRightLexProd (homIndRel 𝓕) ↔ IsContractionClosed (cl 𝓕)

end Lax871432.EdgeContractions
