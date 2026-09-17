import Lax871432.HomomorphismCounts

/-!
---
title: Lovász's theorem
type: theorem
---
Lovász (1967): two finite graphs are isomorphic if and only if they are homomorphism
indistinguishable over all graphs, i.e. if and only if $\hom(K, G) = \hom(K, H)$ for every
graph $K$.

It suffices to test the graphs $K$ on vertex set $\{0, \dots, m-1\}$, since every finite
graph is isomorphic to one of these and $\hom(-, G)$ is an isomorphism invariant.
-/

open Lax871432.HomomorphismCounts

namespace Lax871432.LovaszTheorem

/-- **Lovász's theorem.** Finite graphs with equal homomorphism counts from every graph are
isomorphic, and conversely. -/
axiom nonempty_iso_iff_forall_homCount_eq {V W : Type} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    (∀ (m : ℕ) (K : SimpleGraph (Fin m)), homCount K G = homCount K H) ↔ Nonempty (G ≃g H)

end Lax871432.LovaszTheorem
