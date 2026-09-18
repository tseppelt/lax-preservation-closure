import Mathlib.Algebra.BigOperators.Ring.Finset
import Lax871432.HomomorphismCounts
import Lax871432.LoopGraphs

/-!
---
title: Homomorphism counts into a complement
type: theorem
---
For finite simple graphs $F$ and $G$,
$$\hom(F, \overline{G}) = \sum_{S \subseteq E(F)} (-1)^{|S|}
  \sum_{L \subseteq S} \hom(F_S \oslash L, G),$$
where $F_S$ is the spanning subgraph of $F$ with edge set $S$
and $F \oslash L$ is the graph obtained from $F_S$ by contracting the edges in $L$.

-/

open Lax871432.HomomorphismCounts Lax871432.LoopGraphs

open scoped Lax871432.LoopGraphs

namespace Lax871432.ComplementCounts

/-- **Homomorphisms into a complement**: the number of homomorphisms from `F` to `Gᶜ` is a
signed sum of the numbers of homomorphisms into `G` from the graphs obtained from `F` by
deleting the edges outside a set `S` and contracting those in a subset `L` of `S` — all of
them minors of `F`. -/
axiom homCount_compl {V W : Type*} [Finite V] [Finite W] (F : SimpleGraph V)
    (G : SimpleGraph W) :
    letI : Fintype F.edgeSet := Fintype.ofFinite _
    (homCount F Gᶜ : ℤ) =
      ∑ s : Finset F.edgeSet, (-1 : ℤ) ^ s.card *
        ∑ L ∈ s.powerset,
          (LoopGraph.homCount
            (((spanningSubgraph F) ((edgeSetOf F) s)) ⊘ (edgeSetOf F) L) (toLoopGraph G) : ℤ)

end Lax871432.ComplementCounts
