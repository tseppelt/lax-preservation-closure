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

/-! ### The coefficient analyses -/

/-- Every quotient by a partition into connected parts is positively weighted in the formula,
because the disjoint union of the classes maps into a complete graph on the vertices of `F`. -/
theorem homCount_partsGraph_top_pos {V : Type} [Finite V] {F : SimpleGraph V}
    (𝓡 : ConnPart F) :
    0 < homCount 𝓡.partsGraph (⊤ : SimpleGraph V) :=
  homCount_pos_iff.2 ⟨⟨id, fun {_ _} h => h.1.ne⟩⟩

/-- Likewise every disjoint union of classes is positively weighted, because each quotient
maps into a complete graph on the vertices of `F`. -/
theorem homCount_quotientGraph_top_pos {V : Type} [Finite V] {F : SimpleGraph V}
    (𝓡 : ConnPart F) : 0 < homCount 𝓡.quotientGraph (⊤ : SimpleGraph V) := by
  classical
  haveI : Finite (Quotient 𝓡.setoid) := Quotient.finite _
  haveI : Fintype V := Fintype.ofFinite _
  haveI : Fintype (Quotient 𝓡.setoid) := Fintype.ofFinite _
  obtain ⟨e⟩ : Nonempty (Quotient 𝓡.setoid ↪ V) := by
    refine Function.Embedding.nonempty_of_card_le ?_
    simpa [Nat.card_eq_fintype_card] using
      Nat.card_le_card_of_surjective (Quotient.mk 𝓡.setoid) Quotient.mk_surjective
  exact homCount_pos_iff.2 ⟨⟨e, fun {_ _} h => e.injective.ne h.ne⟩⟩

theorem card_quotient_le {V : Type} [Finite V] {F : SimpleGraph V} (𝓡 : ConnPart F) :
    Nat.card (Quotient 𝓡.setoid) ≤ Nat.card V := by
  simpa using Nat.card_le_card_of_surjective (Quotient.mk 𝓡.setoid) Quotient.mk_surjective

/-- **`prop:lexprod-contract`, the heart of (2) ⇒ (3)**: if `≡[𝓕]` is preserved under right
lexicographic products then every quotient of a member of `cl 𝓕` by a partition into connected
parts is again in `cl 𝓕`.

Taking the right factor to be a complete graph on the vertices of `F` makes every coefficient
`hom(∐ R ∈ 𝓡, F[R], K)` positive, so the formula exhibits a linear combination of the counts
from the quotients that `≡[𝓕]` determines. -/
theorem PreservedUnderRightLexProd.cl_mem_quotientGraph
    (hp : PreservedUnderRightLexProd (homIndRel 𝓕)) {V : Type} [Finite V] {F : SimpleGraph V}
    (hF : (cl 𝓕).Mem F) (𝓡 : ConnPart F) : (cl 𝓕).Mem 𝓡.quotientGraph := by
  classical
  haveI : ∀ 𝓢 : ConnPart F, Finite (Quotient 𝓢.setoid) := fun 𝓢 => Quotient.finite _
  have hLiso : ∀ 𝓢 : ConnPart F,
      Nonempty (𝓢.quotientGraph ≃g SimpleGraph.map (Finite.equivFin (Quotient 𝓢.setoid)) 𝓢.quotientGraph) :=
    fun 𝓢 => ⟨Iso.map (Finite.equivFin (Quotient 𝓢.setoid)) _⟩
  obtain ⟨κ, _, M, β, hMni, hβ, hMhit, hMsum⟩ :=
    exists_graphFamily_of_pos (n := Nat.card V) (fun 𝓢 => card_quotient_le 𝓢)
      (fun 𝓢 : ConnPart F => SimpleGraph.map (Finite.equivFin (Quotient 𝓢.setoid)) 𝓢.quotientGraph)
      (α := fun 𝓢 => (homCount 𝓢.partsGraph (⊤ : SimpleGraph V) : ℚ))
      (fun 𝓢 => by exact_mod_cast homCount_partsGraph_top_pos 𝓢)
  have hdet : ∀ {X Y : Type} [Finite X] [Finite Y] (G : SimpleGraph X) (G' : SimpleGraph Y),
      (G ≡[𝓕] G') →
        ∑ k, β k * (homCount (M.graph k) G : ℚ) = ∑ k, β k * (homCount (M.graph k) G' : ℚ) := by
    intro X Y _ _ G G' hGG'
    rw [← hMsum G, ← hMsum G']
    have key : homCount F (lexProd G (⊤ : SimpleGraph V)) =
        homCount F (lexProd G' (⊤ : SimpleGraph V)) :=
      homCount_eq_of_Mem_cl hF (hp G G' (⊤ : SimpleGraph V) hGG')
    rw [homCount_lexProd, homCount_lexProd] at key
    have key' : ∑ 𝓢 : ConnPart F, (homCount 𝓢.quotientGraph G : ℚ) *
          (homCount 𝓢.partsGraph (⊤ : SimpleGraph V) : ℚ) =
        ∑ 𝓢 : ConnPart F, (homCount 𝓢.quotientGraph G' : ℚ) *
          (homCount 𝓢.partsGraph (⊤ : SimpleGraph V) : ℚ) := by
      exact_mod_cast congrArg (Nat.cast (R := ℚ)) key
    calc ∑ 𝓢 : ConnPart F, (homCount 𝓢.partsGraph (⊤ : SimpleGraph V) : ℚ) *
          (homCount (SimpleGraph.map (Finite.equivFin (Quotient 𝓢.setoid)) 𝓢.quotientGraph) G : ℚ)
        = ∑ 𝓢 : ConnPart F, (homCount 𝓢.quotientGraph G : ℚ) *
            (homCount 𝓢.partsGraph (⊤ : SimpleGraph V) : ℚ) := by
          refine Finset.sum_congr rfl fun 𝓢 _ => ?_
          rw [← homCount_congr_left (hLiso 𝓢).some G, mul_comm]
      _ = _ := key'
      _ = ∑ 𝓢 : ConnPart F, (homCount 𝓢.partsGraph (⊤ : SimpleGraph V) : ℚ) *
            (homCount (SimpleGraph.map (Finite.equivFin (Quotient 𝓢.setoid)) 𝓢.quotientGraph) G' : ℚ) := by
          refine Finset.sum_congr rfl fun 𝓢 _ => ?_
          rw [← homCount_congr_left (hLiso 𝓢).some G', mul_comm]
  have hMmem : ∀ k, (cl 𝓕).mem _ (M.graph k) := fun k =>
    mem_cl_of_determines 𝓕 M hMni β hβ (fun G H h => hdet G H h) k
  obtain ⟨k, hk⟩ := hMhit 𝓡
  exact (GraphClass.Mem_congr (cl 𝓕) ((hLiso 𝓡).some.trans hk.some)).2
    ((GraphClass.Mem_fin (cl 𝓕) (M.graph k)).2 (hMmem k))

/-- **`prop:lexprod-contract`, (2) ⇒ (3)**: every contraction is a quotient by a partition
into connected parts, and those stay in `cl 𝓕`. -/
theorem PreservedUnderRightLexProd.cl_isContractionClosed
    (hp : PreservedUnderRightLexProd (homIndRel 𝓕)) : IsContractionClosed (cl 𝓕) := by
  intro V W _ _ F K hKF hF
  obtain ⟨c⟩ := hKF
  exact (GraphClass.Mem_congr (cl 𝓕) (Contraction.isoQuotientGraph c)).2
    (PreservedUnderRightLexProd.cl_mem_quotientGraph hp hF (Contraction.connPart c))

/-- **`prop:lexprod-contract`, (3) ⇒ (2)**: this follows from (1) ⇒ (2) applied to `cl 𝓕`,
since `≡[𝓕]` and `≡[cl 𝓕]` coincide. -/
theorem PreservedUnderRightLexProd.of_cl_isContractionClosed (h : IsContractionClosed (cl 𝓕)) :
    PreservedUnderRightLexProd (homIndRel 𝓕) := by
  intro V V' W _ _ _ G G' H hGG'
  replace hGG' : G ≡[𝓕] G' := hGG'
  show (lexProd G H) ≡[𝓕] (lexProd G' H)
  rw [← homIndistinguishable_cl_iff] at hGG' ⊢
  exact IsContractionClosed.preservedUnderRightLexProd h G G' H hGG'

/-- **`prop:lexprod-contract`, (2) ⇔ (3)**. -/
theorem preservedUnderRightLexProd_iff_cl_isContractionClosed (𝓕 : GraphClass) :
    PreservedUnderRightLexProd (homIndRel 𝓕) ↔ IsContractionClosed (cl 𝓕) :=
  ⟨fun h => PreservedUnderRightLexProd.cl_isContractionClosed h,
    PreservedUnderRightLexProd.of_cl_isContractionClosed⟩

end GraphClass

end SimpleGraph

end Lax871432Proofs
