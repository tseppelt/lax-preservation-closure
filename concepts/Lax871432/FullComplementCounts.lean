import Mathlib.Algebra.BigOperators.Ring.Finset
import Lax871432.LoopGraphs

/-!
---
title: Homomorphism counts into a full complement
type: theorem
---
For a simple graph $F$ with finitely many edges and a graph $X$,
$$\hom(F, \widehat{X}) = \sum_{s \subseteq E(F)} (-1)^{|s|} \hom(F_s, X),$$
where $F_s$ is the spanning subgraph of $F$ with edge set $s$ (Lovász, *Large Networks and
Graph Limits*, equation (5.23)).

A map $V(F) \to V(X)$ is a homomorphism into the full complement exactly when it avoids, for
every edge of $F$, the event that the edge's endpoints are sent to an adjacent pair;
inclusion–exclusion over those events gives the alternating sum, the maps satisfying the
events of a set $s$ of edges being the homomorphisms out of $F_s$.

This is the first of the two steps expanding homomorphism counts into a complement.
-/

open Lax871432.LoopGraphs

namespace Lax871432.FullComplementCounts

/-- **Homomorphisms into a full complement**, Lovász's equation (5.23): by inclusion–exclusion
over the edges of `F`, the number of homomorphisms from `F` to the full complement of `X` is
the alternating sum, over the subsets `s` of `E(F)`, of the numbers of homomorphisms from the
spanning subgraph `F_s` to `X`. -/
axiom homCount_fullCompl {V W : Type*} [Finite V] [Finite W] (F : SimpleGraph V)
    [Fintype F.edgeSet] (X : LoopGraph W) :
    (LoopGraph.homCount (toLoopGraph F) X.fullCompl : ℤ) =
      ∑ s : Finset F.edgeSet, (-1 : ℤ) ^ s.card *
        (LoopGraph.homCount (toLoopGraph ((spanningSubgraph F) ((edgeSetOf F) s))) X : ℤ)

end Lax871432.FullComplementCounts
