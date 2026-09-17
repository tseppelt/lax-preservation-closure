import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.SetTheory.Cardinal.Finite

/-!
---
title: Homomorphism counts
type: definition
---
A *homomorphism* from a graph $F$ to a graph $G$ is a map $V(F) \to V(G)$ sending adjacent
vertices to adjacent vertices. We write $\hom(F, G)$ for the number of such maps.

The count is defined as the cardinality of the type of homomorphisms, so it carries no
finiteness hypothesis; for infinite graphs it is $0$. All graphs occurring in the results of
this submission are finite.

Isomorphic graphs receive and send equally many homomorphisms. The invariance in the source
argument is recorded here because it is what makes the graph classes of this submission, and
their distinguishing closure, isomorphism-invariant by construction.
-/

namespace Lax871432.HomomorphismCounts

/-- $\hom(F, G)$, the number of homomorphisms from `F` to `G`. -/
noncomputable def homCount {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W) : ℕ :=
  Nat.card (F →g G)

/-- $\hom(-, K)$ is invariant under isomorphism of its source. -/
theorem homCount_congr_left {U V W : Type*} {F : SimpleGraph U} {G : SimpleGraph V}
    (e : F ≃g G) (K : SimpleGraph W) : homCount F K = homCount G K :=
  Nat.card_congr
    { toFun f := f.comp e.symm.toHom
      invFun f := f.comp e.toHom
      left_inv _ := by ext a; exact congrArg _ (e.symm_apply_apply a)
      right_inv _ := by ext a; exact congrArg _ (e.apply_symm_apply a) }

end Lax871432.HomomorphismCounts
