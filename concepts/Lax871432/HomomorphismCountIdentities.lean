import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finite.Card
import Lax871432.ConnectedPartitions
import Lax871432.GraphProducts
import Lax871432.HomomorphismCounts
import Lax871432.LoopGraphs

/-!
---
title: Homomorphism count identities
type: theorem
---
Two expansions of homomorphism counts, each of independent interest. Both write the number of
homomorphisms into a composite graph as a linear combination of the numbers of homomorphisms
into its constituents, out of graphs derived from the source; this is what turns a closure
property of a graph class into a preservation property of homomorphism indistinguishability
over it, and back.

**Lexicographic products.** For simple graphs $F$, $G$ and $H$,
$$\hom(F, G \cdot H) = \sum_{\mathcal{R}} \hom(F / \mathcal{R}, G)
  \hom(\textstyle\coprod_{R \in \mathcal{R}} F[R], H),$$
the sum ranging over the partitions $\mathcal{R}$ of $V(F)$ all of whose classes induce
connected subgraphs. A homomorphism $F \to G \cdot H$ is determined by, and determines, such a
partition together with a homomorphism from the quotient into $G$ and one from the disjoint
union of the classes into $H$.

**Complements.** For a simple graph $F$ with finitely many edges and a graph $G$,
$$\hom(F, \overline{G}) = \sum_{s \subseteq E(F)} (-1)^{|s|}
  \sum_{L \subseteq s} \hom(F_s \oslash L, G),$$
where $F_s$ is the spanning subgraph of $F$ with edge set $s$. Every graph occurring on the
right is obtained from $F$ by deleting and then contracting edges, i.e. is a minor of $F$.
The identity is assembled from two steps, each stated here as well: inclusion–exclusion over
the edges of $F$ expands homomorphism counts into a full complement, and homomorphisms into a
looped graph correspond to pairs consisting of a set of edges collapsed to loops and a
homomorphism out of the resulting contraction quotient.

# Implementation notes

Edge sets are indexed by `Finset F.edgeSet` rather than by sets of unordered pairs, so that
the sums are finite sums over a fintype; `edgeSetOf` turns such a `Finset` back into the set
of unordered pairs the graph operations take.

The complement identity is stated over `ℤ` because of the alternating signs. The two steps
leading to it are stated for loop graphs, since a full complement has loops wherever the
original had none, and a contraction quotient may have loops even when nothing else does.
-/

open Lax871432.ConnectedPartitions Lax871432.GraphProducts Lax871432.HomomorphismCounts
open Lax871432.LoopGraphs

open scoped Lax871432.LoopGraphs

namespace Lax871432.HomomorphismCountIdentities

/-- **Homomorphisms into a lexicographic product**: they are counted by the partitions of the
source into connected parts, a homomorphism from the quotient into the left factor and a
homomorphism from the disjoint union of the parts into the right factor. -/
axiom homCount_lexProd {U V W : Type*} [Finite U] [Finite V] [Finite W] (F : SimpleGraph U)
    (G : SimpleGraph V) (H : SimpleGraph W) :
    homCount F (lexProd G H) =
      ∑ 𝓡 : ConnPart F, homCount 𝓡.quotientGraph G * homCount 𝓡.parts H

/-- **Homomorphisms into a full complement** (Lovász, *Large Networks and Graph Limits*,
equation (5.23)): by inclusion–exclusion over the edges of `F`, the number of homomorphisms
from `F` to the full complement of `X` is the alternating sum, over the subsets `s` of `E(F)`,
of the numbers of homomorphisms from the spanning subgraph `F_s` to `X`. -/
axiom homCount_fullCompl {V W : Type*} [Finite V] [Finite W] (F : SimpleGraph V)
    [Fintype F.edgeSet] (X : LoopGraph W) :
    (LoopGraph.homCount (toLoopGraph F) X.fullCompl : ℤ) =
      ∑ s : Finset F.edgeSet, (-1 : ℤ) ^ s.card *
        (LoopGraph.homCount (toLoopGraph ((spanningSubgraph F) ((edgeSetOf F) s))) X : ℤ)

/-- **Homomorphisms into a looped graph**: a homomorphism from `F` to `G°` is the same thing
as a set `L` of edges of `F`, those it collapses to loops, together with a homomorphism from
the contraction quotient `F ⊘ L` to `G`. -/
axiom homCount_looped {V W : Type*} [Finite V] [Finite W] (F : SimpleGraph V)
    [Fintype F.edgeSet] (G : SimpleGraph W) :
    LoopGraph.homCount (toLoopGraph F) (looped G) =
      ∑ L : Finset F.edgeSet, LoopGraph.homCount (F ⊘ (edgeSetOf F) L) (toLoopGraph G)

/-- **Homomorphisms into a complement**: combining the two identities above through
`Gᶜ = (G°)^`, the number of homomorphisms from `F` to `Gᶜ` is a signed sum of the numbers of
homomorphisms into `G` from the graphs obtained from `F` by deleting the edges outside a set
`s` and contracting those in a subset `L` of `s` — all of them minors of `F`. -/
axiom homCount_compl {V W : Type*} [Finite V] [Finite W] (F : SimpleGraph V)
    [Fintype F.edgeSet] (G : SimpleGraph W) :
    (homCount F Gᶜ : ℤ) =
      ∑ s : Finset F.edgeSet, (-1 : ℤ) ^ s.card *
        ∑ L ∈ s.powerset,
          (LoopGraph.homCount
            (((spanningSubgraph F) ((edgeSetOf F) s)) ⊘ (edgeSetOf F) L) (toLoopGraph G) : ℤ)

end Lax871432.HomomorphismCountIdentities
