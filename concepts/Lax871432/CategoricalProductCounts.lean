import Lax871432.GraphProducts
import Lax871432.HomomorphismCounts

/-!
---
title: Homomorphism counts into a categorical product
type: lemma
---
For simple graphs $F$, $G_1$ and $G_2$,
$$\hom(F, G_1 \times G_2) = \hom(F, G_1) \hom(F, G_2).$$
-/

open Lax871432.GraphProducts Lax871432.HomomorphismCounts

open scoped Lax871432.GraphProducts

namespace Lax871432.CategoricalProductCounts

/-- A homomorphism into a categorical product is a pair of homomorphisms into its two
factors. -/
axiom homCount_catProd_right {U V W : Type*} [Finite U] [Finite V] [Finite W]
    (F : SimpleGraph U) (G₁ : SimpleGraph V) (G₂ : SimpleGraph W) :
    homCount F (G₁ ×g G₂) = homCount F G₁ * homCount F G₂

end Lax871432.CategoricalProductCounts
