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

A homomorphism $F \to G \cdot H$ is determined by, and determines, such a partition together
with a homomorphism from the quotient into the left factor and one from the disjoint union of
the classes into the right factor. The identity is of independent interest, and it is what
turns closure of a graph class under induced subgraphs, respectively under edge contractions,
into preservation of homomorphism indistinguishability under lexicographic products on one
side, respectively the other.
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
