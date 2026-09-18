import Mathlib.Algebra.BigOperators.Ring.Finset
import Lax871432.LoopGraphs

/-!
---
title: Homomorphism counts into a looped graph
type: theorem
---
For finite simple graphs $F$ and $G$,
$$\hom(F, G^\circ) = \sum_{L \subseteq E(F)} \hom(F \oslash L, G),$$
where $G^\circ$ carries a loop at every vertex and $F \oslash L$ is the contraction quotient
of $F$ by the edge set $L$.
-/

open Lax871432.LoopGraphs

open scoped Lax871432.LoopGraphs

namespace Lax871432.LoopedGraphCounts

/-- **Homomorphisms into a looped graph**: a homomorphism from `F` to `G°` is the same thing
as a set `L` of edges of `F`, those it collapses to loops, together with a homomorphism from
the contraction quotient `F ⊘ L` to `G`. -/
axiom homCount_looped {V W : Type*} [Finite V] [Finite W] (F : SimpleGraph V)
    (G : SimpleGraph W) :
    letI : Fintype F.edgeSet := Fintype.ofFinite _
    LoopGraph.homCount (toLoopGraph F) (looped G) =
      ∑ L : Finset F.edgeSet, LoopGraph.homCount (F ⊘ (edgeSetOf F) L) (toLoopGraph G)

end Lax871432.LoopedGraphCounts
