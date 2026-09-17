import Mathlib.Algebra.BigOperators.Ring.Finset
import Lax871432.LoopGraphs

/-!
---
title: Homomorphism counts into a full complement
type: theorem
---
For a simple graph $F$ with finitely many edges and a graph $X$,
$$\hom(F, \widehat{X}) = \sum_{S \subseteq E(F)} (-1)^{|S|} \hom(F_S, X),$$
where $F_S$ is the spanning subgraph of $F$ with edge set $S$ (Lovász, *Large Networks and
Graph Limits*, equation (5.23)).
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
