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
-/

namespace Lax871432.HomomorphismCounts

/-- $\hom(F, G)$, the number of homomorphisms from `F` to `G`. -/
noncomputable def homCount {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W) : ℕ :=
  Nat.card (F →g G)

end Lax871432.HomomorphismCounts
