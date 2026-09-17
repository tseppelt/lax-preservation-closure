/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Lax871432Proofs.Hom.LexProd
import Lax871432Proofs.HomInd.Closure

/-!
# Induced subgraphs, edge contractions, and lexicographic products

**`prop:lexprod-indsub`** and **`prop:lexprod-contract`**.  Both read the formula
`SimpleGraph.homCount_lexProd` as a linear combination: in the counts from the quotients
`F / 𝓡` for the second, and in the counts from the disjoint unions of the classes for the
first.

This file proves the implications (1) ⇒ (2) of both; the equivalences (2) ⇔ (3) follow the
pattern of `PreservationClosure/Summands.lean`.
-/

namespace Lax871432Proofs

open _root_.SimpleGraph
open Lax871432.ClosureProperties Lax871432.DistinguishingClosure
open Lax871432.GraphProducts Lax871432.HomomorphismCounts
open Lax871432.HomomorphismIndistinguishability Lax871432.IsomorphismRelaxations
open Lax871432.PreservationProperties

open scoped Lax871432.GraphProducts
open scoped Lax871432.HomomorphismIndistinguishability

namespace SimpleGraph

namespace GraphClass

variable {𝓕 : GraphClass}

/-- **`prop:lexprod-indsub`, (1) ⇒ (2)**: if `𝓕` is closed under taking induced subgraphs then
`≡[𝓕]` is preserved under left lexicographic products.

In the formula for `hom(F, G ⋅ H)` the second factor of each summand counts homomorphisms out
of a disjoint union of subgraphs of `F` induced by the classes of a partition; each of those
lies in `𝓕`, so none of them tells `H` from `H'`. -/
theorem IsInducedSubgraphClosed.preservedUnderLeftLexProd (h : IsInducedSubgraphClosed 𝓕) :
    PreservedUnderLeftLexProd (homIndRel 𝓕) := by
  intro V W W' _ _ _ G H H' hHH' m F hF
  have hFmem : 𝓕.Mem F := (GraphClass.Mem_fin 𝓕 F).2 hF
  rw [homCount_lexProd, homCount_lexProd]
  refine Finset.sum_congr rfl fun 𝓡 _ => ?_
  rw [homCount_partsGraph_congr 𝓡 H H' fun a =>
    (homIndistinguishable_iff_forall_mem 𝓕 H H').1 hHH' _ (h F _ hFmem)]

/-- **`prop:lexprod-contract`, (1) ⇒ (2)**: if `𝓕` is closed under contracting edges then
`≡[𝓕]` is preserved under right lexicographic products.

In the formula for `hom(F, G ⋅ H)` the first factor of each summand counts homomorphisms out
of a quotient `F / 𝓡`, which is a contraction of `F` and so lies in `𝓕`. -/
theorem IsContractionClosed.preservedUnderRightLexProd (h : IsContractionClosed 𝓕) :
    PreservedUnderRightLexProd (homIndRel 𝓕) := by
  intro V V' W _ _ _ G G' H hGG' m F hF
  have hFmem : 𝓕.Mem F := (GraphClass.Mem_fin 𝓕 F).2 hF
  rw [homCount_lexProd, homCount_lexProd]
  refine Finset.sum_congr rfl fun 𝓡 _ => ?_
  rw [(homIndistinguishable_iff_forall_mem 𝓕 G G').1 hGG' _
    (h 𝓡.quotientGraph 𝓡.isContraction hFmem)]

end GraphClass

end SimpleGraph

end Lax871432Proofs
