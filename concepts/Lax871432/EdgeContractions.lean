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

Preservation under right lexicographic products is a genuine restriction, unlike its special
case $H = \overline{K_n}$, preservation under blow-ups, which every homomorphism
indistinguishability relation satisfies. Both directions run through the formula for
homomorphism counts into a lexicographic product, read this time as a linear combination in
the counts from the quotients $F/\mathcal{R}$. Backwards, taking the right factor to be a
complete graph on $|V(F)|$ vertices makes every coefficient
$\hom(\coprod_{R \in \mathcal{R}} F[R], K_n)$ positive, so the coefficient of
$\hom(F/\mathcal{R}, -)$ does not vanish and the lemma on determined linear combinations
places $F/\mathcal{R}$ in $\mathrm{cl}(\mathcal{F})$.
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
