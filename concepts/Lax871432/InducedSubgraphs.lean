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

Both directions run through the formula for homomorphism counts into a lexicographic product.
Forwards, every graph occurring on the right of that formula when the left factor is held
fixed is a disjoint union of induced subgraphs of the source. Backwards, taking the left
factor to be a complete graph on $|V(F)|$ vertices makes every coefficient
$\hom(F/\mathcal{R}, K_n)$ positive, so the lemma on determined linear combinations applies;
the partition whose classes are the connected components of $F[U]$ together with singletons
contributes $F[U]$ itself, up to isolated vertices.
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
