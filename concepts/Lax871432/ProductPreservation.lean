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

This is immediate from $\hom(F, G \times K) = \hom(F, G)\hom(F, K)$, the identity which says
that $\times$ is the product in the category of graphs and graph homomorphisms. It is the one
property of $\equiv_{\mathcal{F}}$ that the lemma on determined linear combinations needs, and
isolating it is what lets that lemma be stated for an arbitrary relaxation.
-/

open Lax871432.HomomorphismIndistinguishability Lax871432.PreservationProperties

namespace Lax871432.ProductPreservation

/-- Homomorphism indistinguishability over any graph class is preserved under categorical
products. -/
axiom preservedUnderCatProd (𝓕 : GraphClass) :
    PreservedUnderCatProd (homIndRel 𝓕)

end Lax871432.ProductPreservation
