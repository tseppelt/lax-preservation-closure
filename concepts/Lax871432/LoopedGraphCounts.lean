import Mathlib.Algebra.BigOperators.Ring.Finset
import Lax871432.LoopGraphs

/-!
---
title: Homomorphism counts into a looped graph
type: theorem
---
For simple graphs $F$ and $G$,
$$\hom(F, G^\circ) = \sum_{L \subseteq E(F)} \hom(F \oslash L, G),$$
where $G^\circ$ carries a loop at every vertex and $F \oslash L$ is the contraction quotient
of $F$ by the edge set $L$.

A homomorphism $F \to G^\circ$ is the same thing as a pair consisting of the set $L$ of edges
of $F$ whose endpoints it identifies and a homomorphism $F \oslash L \to G$: the quotient by
$L$ is exactly what remains once the collapsed edges are contracted, and an edge outside $L$
is sent to a genuine edge of $G$.

This is the second of the two steps expanding homomorphism counts into a complement.
-/

open Lax871432.LoopGraphs

open scoped Lax871432.LoopGraphs

namespace Lax871432.LoopedGraphCounts

/-- **Homomorphisms into a looped graph**: a homomorphism from `F` to `G°` is the same thing
as a set `L` of edges of `F`, those it collapses to loops, together with a homomorphism from
the contraction quotient `F ⊘ L` to `G`. -/
axiom homCount_looped {V W : Type*} [Finite V] [Finite W] (F : SimpleGraph V)
    [Fintype F.edgeSet] (G : SimpleGraph W) :
    LoopGraph.homCount (toLoopGraph F) (looped G) =
      ∑ L : Finset F.edgeSet, LoopGraph.homCount (F ⊘ (edgeSetOf F) L) (toLoopGraph G)

end Lax871432.LoopedGraphCounts
