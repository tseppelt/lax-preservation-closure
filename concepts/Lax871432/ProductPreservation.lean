import Lax871432.HomomorphismIndistinguishability
import Lax871432.PreservationProperties

/-!
---
title: Homomorphism indistinguishability is preserved under categorical products
type: lemma
---
For every graph class $\mathcal{F}$, the relaxation $\equiv_{\mathcal{F}}$ is preserved under
categorical products: if $G \equiv_{\mathcal{F}} H$ then
$G \times K \equiv_{\mathcal{F}} H \times K$ for every graph $K$.
-/

open Lax871432.GraphClasses
open Lax871432.HomomorphismIndistinguishability Lax871432.PreservationProperties

namespace Lax871432.ProductPreservation

/-- Homomorphism indistinguishability over any graph class is preserved under categorical
products. -/
axiom preservedUnderCatProd (𝓕 : GraphClass) :
    PreservedUnderCatProd (homIndRel 𝓕)

end Lax871432.ProductPreservation
