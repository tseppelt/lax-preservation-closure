import Mathlib.Algebra.BigOperators.Ring.Finset
import Lax871432.HomomorphismCounts
import Lax871432.LoopGraphs

/-!
---
title: Homomorphism counts into a complement
type: theorem
---
For a simple graph $F$ with finitely many edges and a simple graph $G$,
$$\hom(F, \overline{G}) = \sum_{s \subseteq E(F)} (-1)^{|s|}
  \sum_{L \subseteq s} \hom(F_s \oslash L, G),$$
where $F_s$ is the spanning subgraph of $F$ with edge set $s$. Every graph occurring on the
right is obtained from $F$ by deleting the edges outside $s$ and then contracting those in
$L$, hence is a minor of $F$.

The identity is assembled from the two steps through $\overline{G} = \widehat{G^\circ}$:
inclusion–exclusion over the edges of $F$ expands the count into a full complement, and each
resulting count into the looped graph is expanded over the sets of edges collapsed to loops.
It is the identity from which the correspondence between minor-closedness and preservation
under complements is read off.

# Implementation notes

The identity is stated over `ℤ` because of the alternating signs, and with loop graphs on the
right: a contraction quotient may have loops even when nothing else does, and the terms whose
quotient does are exactly the ones that contribute nothing.
-/

open Lax871432.HomomorphismCounts Lax871432.LoopGraphs

open scoped Lax871432.LoopGraphs

namespace Lax871432.ComplementCounts

/-- **Homomorphisms into a complement**: the number of homomorphisms from `F` to `Gᶜ` is a
signed sum of the numbers of homomorphisms into `G` from the graphs obtained from `F` by
deleting the edges outside a set `s` and contracting those in a subset `L` of `s` — all of
them minors of `F`. -/
axiom homCount_compl {V W : Type*} [Finite V] [Finite W] (F : SimpleGraph V)
    [Fintype F.edgeSet] (G : SimpleGraph W) :
    (homCount F Gᶜ : ℤ) =
      ∑ s : Finset F.edgeSet, (-1 : ℤ) ^ s.card *
        ∑ L ∈ s.powerset,
          (LoopGraph.homCount
            (((spanningSubgraph F) ((edgeSetOf F) s)) ⊘ (edgeSetOf F) L) (toLoopGraph G) : ℤ)

end Lax871432.ComplementCounts
