import Lax871432.ClosureProperties
import Lax871432.DistinguishingClosure
import Lax871432.PreservationProperties

/-!
---
title: Taking induced subgraphs and left lexicographic products
type: theorem
---
For a graph class $\mathcal{F}$ and the assertions

1. $\mathcal{F}$ is closed under taking induced subgraphs,
2. the relaxation $\equiv_{\mathcal{F}}$ is preserved under left lexicographic products,
3. $\mathrm{cl}(\mathcal{F})$ is closed under taking induced subgraphs,

the implications (1) $\Rightarrow$ (2) $\Leftrightarrow$ (3) hold.
-/

open Lax871432.ClosureProperties Lax871432.DistinguishingClosure
open Lax871432.HomomorphismIndistinguishability Lax871432.PreservationProperties

namespace Lax871432.InducedSubgraphs

/-- **(1) $\Rightarrow$ (2).** -/
axiom preservedUnderLeftLexProd_of_isInducedSubgraphClosed (𝓕 : GraphClass) :
    IsInducedSubgraphClosed 𝓕 → PreservedUnderLeftLexProd (homIndRel 𝓕)

/-- **(2) $\Leftrightarrow$ (3).** -/
axiom preservedUnderLeftLexProd_iff_cl_isInducedSubgraphClosed (𝓕 : GraphClass) :
    PreservedUnderLeftLexProd (homIndRel 𝓕) ↔ IsInducedSubgraphClosed (cl 𝓕)

end Lax871432.InducedSubgraphs
