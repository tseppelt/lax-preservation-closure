import Mathlib.Algebra.BigOperators.Ring.Finset
import Lax871432.ConnectedPartitions
import Lax871432.GraphProducts
import Lax871432.HomomorphismCounts

/-!
---
title: Homomorphism counts into a lexicographic product
type: theorem
---
For simple graphs $F$, $G$ and $H$,
$$\hom(F, G \cdot H) = \sum_{\mathcal{R}} \hom(F / \mathcal{R}, G)
  \hom(\textstyle\coprod_{R \in \mathcal{R}} F[R], H),$$
the sum ranging over the partitions $\mathcal{R}$ of $V(F)$ all of whose classes induce
connected subgraphs.
-/

open Lax871432.ConnectedPartitions Lax871432.GraphProducts Lax871432.HomomorphismCounts

namespace Lax871432.LexicographicProductCounts

/-- **Homomorphisms into a lexicographic product**: they are counted by the partitions of the
source into connected parts, a homomorphism from the quotient into the left factor and a
homomorphism from the disjoint union of the parts into the right factor. -/
axiom homCount_lexProd {U V W : Type*} [Finite U] [Finite V] [Finite W] (F : SimpleGraph U)
    (G : SimpleGraph V) (H : SimpleGraph W) :
    homCount F (lexProd G H) =
      ∑ 𝓡 : ConnPart F, homCount 𝓡.quotientGraph G * homCount 𝓡.parts H

end Lax871432.LexicographicProductCounts
