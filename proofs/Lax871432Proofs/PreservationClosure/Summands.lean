/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Lax871432Proofs.HomInd.Closure

/-!
# Taking summands and preservation under disjoint unions

**`thm:taking-summands`.**  For a class `𝓕` of finite simple graphs and the assertions

1. `𝓕` is *closed under taking summands*: `F₁ ⊕g F₂ ∈ 𝓕` implies `F₁ ∈ 𝓕` and `F₂ ∈ 𝓕`;
2. `≡[𝓕]` is *preserved under disjoint unions*: `G ≡[𝓕] G'` and `H ≡[𝓕] H'` imply
   `G ⊕g H ≡[𝓕] G' ⊕g H'`;
3. `cl 𝓕` is closed under taking summands,

the implications (1) ⇒ (2) ⇔ (3) hold.  This answers a question of Roberson,
*Oddomorphisms and homomorphism indistinguishability over graph classes* (2022), p. 7.

The properties themselves are defined in `HomInd/Closure.lean`.

## Proof outline

The central computation is `eq:disjunion` (`SimpleGraph.homCount_sigma_sum_right`): for a
disjoint union of connected graphs `D i`,

  `hom(∐ i, D i, G ⊕g H) = ∑_{t ⊆ ι} hom(∐_{i ∈ t} D i, G) · hom(∐_{i ∉ t} D i, H)`.

* (1) ⇒ (2): every `∐_{i ∈ t} D i` occurring on the right-hand side is a summand of `F`, so
  it lies in `𝓕`, and both sides are determined by `≡[𝓕]`.
* (2) ⇒ (3): apply `eq:disjunion` with `H := F`.  Then `≡[𝓕]` determines the linear
  combination `∑_t hom(∐_{i ∈ t} D i, -) · hom(∐_{i ∉ t} D i, F)`, whose coefficients are
  positive because `∐_{i ∉ t} D i` maps into `F`.  Distinct `t` may give isomorphic unions,
  so the summands are first grouped by isomorphism type
  (`SimpleGraph.exists_graphFamily_of_pos`); then `SimpleGraph.mem_cl_of_determines` applies.
  Splitting `F₁ ⊕g F₂` into the components of `F₁` and of `F₂` separately exhibits `F₁` and
  `F₂` as two such sub-unions.
* (3) ⇒ (2): apply (1) ⇒ (2) to `cl 𝓕` and use `SimpleGraph.homIndistinguishable_cl_iff`.

## Main declarations

* `SimpleGraph.GraphClass.preservedUnderDisjointUnion_iff_cl_isSummandClosed`:
  **`thm:taking-summands`**.

## References

* Roberson, *Oddomorphisms and homomorphism indistinguishability over graph classes* (2022).
-/

namespace Lax871432Proofs

open _root_.SimpleGraph
open Lax871432.HomomorphismCounts
open Lax871432.HomomorphismIndistinguishability Lax871432.DistinguishingClosure
open scoped Lax871432.HomomorphismIndistinguishability
open Lax871432.ClosureProperties Lax871432.PreservationProperties
open Lax68.GraphMinors

open Function

namespace SimpleGraph

variable {𝓕 : GraphClass}

namespace GraphClass

/-- **`thm:taking-summands`, (1) ⇒ (2)**: if `𝓕` is closed under taking summands then `≡[𝓕]`
is preserved under disjoint unions. -/
theorem IsSummandClosed.preservedUnderDisjointUnion (h : IsSummandClosed 𝓕) :
    PreservedUnderDisjointUnion (homIndistinguishability 𝓕) := by
  classical
  intro V V' W W' _ _ _ _ G G' H H' hG hH _ F hF
  haveI : Fintype F.ConnectedComponent := Fintype.ofFinite _
  have hFmem : 𝓕.Mem F := (GraphClass.Mem_fin 𝓕 F).2 hF
  rw [homCount_sum_right_eq_sum_powerset F G H, homCount_sum_right_eq_sum_powerset F G' H']
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [(homIndistinguishable_iff_forall_mem 𝓕 G G').1 hG _
      ((GraphClass.IsSummandClosed.mem_sigmaOn_connectedComponent h) hFmem _),
    (homIndistinguishable_iff_forall_mem 𝓕 H H').1 hH _
      ((GraphClass.IsSummandClosed.mem_sigmaOn_connectedComponent h) hFmem _)]

/-- If `≡[𝓕]` is preserved under disjoint unions and a disjoint union of connected graphs lies
in `cl 𝓕`, then so does every sub-union.

This is the technical heart of (2) ⇒ (3): `eq:disjunion` with `H := ∐ i, D i` exhibits a
linear combination determined by `≡[𝓕]`, whose coefficients are positive by
`SimpleGraph.homCount_sigmaOn_sigma_pos`. -/
theorem PreservedUnderDisjointUnion.mem_cl_sigmaOn (hp : PreservedUnderDisjointUnion (homIndistinguishability 𝓕))
    {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, Finite (V i)] {D : ∀ i, SimpleGraph (V i)}
    (hD : ∀ i, (D i).Connected) (hmem : (cl 𝓕).Mem (SimpleGraph.sigma D)) (s : Set ι) :
    (cl 𝓕).Mem (sigmaOn s D) := by
  classical
  -- Each sub-union has at most as many vertices as the whole union.
  have hsize : ∀ t : Finset ι,
      Nat.card (Σ i : (↑t : Set ι), V ↑i) ≤ Nat.card (Σ i, V i) := by
    intro t
    refine Nat.card_le_card_of_injective
      (fun p : Σ i : (↑t : Set ι), V ↑i => (⟨↑p.1, p.2⟩ : Σ i, V i)) ?_
    rintro ⟨i, x⟩ ⟨j, y⟩ h
    obtain rfl : i = j := Subtype.ext (congrArg Sigma.fst h)
    simpa using h
  have hLiso : ∀ t : Finset ι, Nonempty (sigmaOn (↑t) D ≃g
      SimpleGraph.map (Finite.equivFin _) (sigmaOn (↑t) D)) :=
    fun t => ⟨Iso.map (Finite.equivFin _) _⟩
  -- The coefficients are the homomorphism counts of the complementary sub-unions.
  have hα : ∀ t : Finset ι,
      (0 : ℚ) < (homCount (sigmaOn (↑tᶜ) D) (SimpleGraph.sigma D) : ℚ) := fun t => by
    exact_mod_cast homCount_sigmaOn_sigma_pos D (↑tᶜ)
  obtain ⟨κ, _, M, β, hMni, hβ, hMhit, hMsum⟩ :=
    exists_graphFamily_of_pos hsize
      (fun t => SimpleGraph.map (Finite.equivFin _) (sigmaOn (↑t) D)) hα
  -- `≡[𝓕]` determines the grouped linear combination, by `eq:disjunion` with `H := ∐ i, D i`.
  have hdet : ∀ {X Y : Type} [Finite X] [Finite Y] (G : SimpleGraph X) (H : SimpleGraph Y),
      (G ≡[𝓕] H) →
        ∑ k, β k * (homCount (M.graph k) G : ℚ) = ∑ k, β k * (homCount (M.graph k) H : ℚ) := by
    intro X Y _ _ G H hGH
    rw [← hMsum G, ← hMsum H]
    have key : homCount (SimpleGraph.sigma D) (G ⊕g SimpleGraph.sigma D) =
        homCount (SimpleGraph.sigma D) (H ⊕g SimpleGraph.sigma D) :=
      homCount_eq_of_Mem_cl hmem
        (hp G H (SimpleGraph.sigma D) (SimpleGraph.sigma D) hGH
          (HomIndistinguishable.refl 𝓕 _))
    rw [homCount_sigma_sum_right hD G (SimpleGraph.sigma D),
      homCount_sigma_sum_right hD H (SimpleGraph.sigma D)] at key
    have key' : ∑ t : Finset ι, (homCount (sigmaOn (↑t) D) G : ℚ) *
          (homCount (sigmaOn (↑tᶜ) D) (SimpleGraph.sigma D) : ℚ) =
        ∑ t : Finset ι, (homCount (sigmaOn (↑t) D) H : ℚ) *
          (homCount (sigmaOn (↑tᶜ) D) (SimpleGraph.sigma D) : ℚ) := by
      exact_mod_cast congrArg (Nat.cast (R := ℚ)) key
    calc ∑ t : Finset ι, (homCount (sigmaOn (↑tᶜ) D) (SimpleGraph.sigma D) : ℚ) *
          (homCount (SimpleGraph.map (Finite.equivFin _) (sigmaOn (↑t) D)) G : ℚ)
        = ∑ t : Finset ι, (homCount (sigmaOn (↑t) D) G : ℚ) *
            (homCount (sigmaOn (↑tᶜ) D) (SimpleGraph.sigma D) : ℚ) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [← homCount_congr_left (hLiso t).some G, mul_comm]
      _ = ∑ t : Finset ι, (homCount (sigmaOn (↑t) D) H : ℚ) *
            (homCount (sigmaOn (↑tᶜ) D) (SimpleGraph.sigma D) : ℚ) := key'
      _ = ∑ t : Finset ι, (homCount (sigmaOn (↑tᶜ) D) (SimpleGraph.sigma D) : ℚ) *
            (homCount (SimpleGraph.map (Finite.equivFin _)
              (sigmaOn (↑t) D)) H : ℚ) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [← homCount_congr_left (hLiso t).some H, mul_comm]
  -- Hence every member of the grouped family lies in `cl 𝓕`, and so does every sub-union.
  have hMmem : ∀ k, (cl 𝓕).mem _ (M.graph k) := by
    intro k
    refine mem_cl_of_determines 𝓕 M hMni β hβ ?_ k
    intro X Y _ _ G H hGH
    exact hdet G H hGH
  obtain ⟨k, hk⟩ := hMhit s.toFinset
  have hiso : sigmaOn s D ≃g M.graph k := by
    have h1 : sigmaOn (↑s.toFinset) D ≃g M.graph k := (hLiso s.toFinset).some.trans hk.some
    rwa [Set.coe_toFinset] at h1
  have h2 : (cl 𝓕).Mem (M.graph k) := ((GraphClass.Mem_fin (cl 𝓕)) (M.graph k)).2 (hMmem k)
  rw [(GraphClass.Mem_congr (cl 𝓕)) hiso]
  exact h2

/-- The family of connected components of `F₁ ⊕g F₂`, indexed by the components of `F₁` and
of `F₂` separately. -/
private def sumComponentFamily {V W : Type} (F₁ : SimpleGraph V) (F₂ : SimpleGraph W) :
    ∀ k : F₁.ConnectedComponent ⊕ F₂.ConnectedComponent,
      SimpleGraph (Sum.elim (fun c : F₁.ConnectedComponent => (↥c : Type))
        (fun d : F₂.ConnectedComponent => (↥d : Type)) k)
  | .inl c => c.toSimpleGraph
  | .inr d => d.toSimpleGraph

/-- **`thm:taking-summands`, (2) ⇒ (3)**: if `≡[𝓕]` is preserved under disjoint unions then
`cl 𝓕` is closed under taking summands. -/
theorem PreservedUnderDisjointUnion.cl_isSummandClosed (hp : PreservedUnderDisjointUnion (homIndistinguishability 𝓕)) :
    IsSummandClosed (cl 𝓕) := by
  classical
  intro V W _ _ F₁ F₂ hmem
  haveI : Fintype F₁.ConnectedComponent := Fintype.ofFinite _
  haveI : Fintype F₂.ConnectedComponent := Fintype.ofFinite _
  haveI : ∀ k : F₁.ConnectedComponent ⊕ F₂.ConnectedComponent,
      Finite (Sum.elim (fun c : F₁.ConnectedComponent => (↥c : Type))
        (fun d : F₂.ConnectedComponent => (↥d : Type)) k) := by
    rintro (c | d)
    · exact inferInstanceAs (Finite ↥c)
    · exact inferInstanceAs (Finite ↥d)
  have hD : ∀ k, (sumComponentFamily F₁ F₂ k).Connected := by
    rintro (c | d) <;> exact ConnectedComponent.connected_toSimpleGraph _
  -- `F₁ ⊕g F₂` is the disjoint union of the components of `F₁` and those of `F₂`.
  have hsplit : (F₁ ⊕g F₂) ≃g SimpleGraph.sigma (sumComponentFamily F₁ F₂) :=
    (Iso.sumCongr (Iso.sigmaConnectedComponent F₁).symm
      (Iso.sigmaConnectedComponent F₂).symm).trans (Iso.sigmaSum (sumComponentFamily F₁ F₂)).symm
  -- Each of `F₁`, `F₂` is the sub-union over one side of the index type.
  have e₁ : (SimpleGraph.sigma fun c : F₁.ConnectedComponent => c.toSimpleGraph) ≃g
      sigmaOn (Set.range Sum.inl) (sumComponentFamily F₁ F₂) :=
    Iso.sigmaCongrLeft (Equiv.ofInjective Sum.inl Sum.inl_injective)
      (fun i : Set.range (Sum.inl : F₁.ConnectedComponent →
        F₁.ConnectedComponent ⊕ F₂.ConnectedComponent) => sumComponentFamily F₁ F₂ ↑i)
  have e₂ : (SimpleGraph.sigma fun d : F₂.ConnectedComponent => d.toSimpleGraph) ≃g
      sigmaOn (Set.range Sum.inr) (sumComponentFamily F₁ F₂) :=
    Iso.sigmaCongrLeft (Equiv.ofInjective Sum.inr Sum.inr_injective)
      (fun i : Set.range (Sum.inr : F₂.ConnectedComponent →
        F₁.ConnectedComponent ⊕ F₂.ConnectedComponent) => sumComponentFamily F₁ F₂ ↑i)
  have hmem' : (cl 𝓕).Mem (SimpleGraph.sigma (sumComponentFamily F₁ F₂)) :=
    ((GraphClass.Mem_congr (cl 𝓕)) hsplit).1 hmem
  exact ⟨((GraphClass.Mem_congr (cl 𝓕)) ((Iso.sigmaConnectedComponent F₁).symm.trans e₁)).2
      ((GraphClass.PreservedUnderDisjointUnion.mem_cl_sigmaOn hp) hD hmem' _),
    ((GraphClass.Mem_congr (cl 𝓕)) ((Iso.sigmaConnectedComponent F₂).symm.trans e₂)).2
      ((GraphClass.PreservedUnderDisjointUnion.mem_cl_sigmaOn hp) hD hmem' _)⟩

/-- **`thm:taking-summands`, (3) ⇒ (2)**: this follows from (1) ⇒ (2) applied to `cl 𝓕`,
since `≡[𝓕]` and `≡[cl 𝓕]` coincide. -/
theorem PreservedUnderDisjointUnion.of_cl_isSummandClosed (h : IsSummandClosed (cl 𝓕)) :
    PreservedUnderDisjointUnion (homIndistinguishability 𝓕) := by
  intro V V' W W' _ _ _ _ G G' H H' hG hH
  replace hG : G ≡[𝓕] G' := hG
  replace hH : H ≡[𝓕] H' := hH
  show (G ⊕g H) ≡[𝓕] (G' ⊕g H')
  rw [← homIndistinguishable_cl_iff] at hG hH ⊢
  exact (GraphClass.IsSummandClosed.preservedUnderDisjointUnion h) G G' H H' hG hH

/-- **`thm:taking-summands`**: `≡[𝓕]` is preserved under disjoint unions if and only if
`cl 𝓕` is closed under taking summands; and this holds whenever `𝓕` itself is closed under
taking summands (`SimpleGraph.GraphClass.IsSummandClosed.preservedUnderDisjointUnion`). -/
theorem preservedUnderDisjointUnion_iff_cl_isSummandClosed (𝓕 : GraphClass) :
    PreservedUnderDisjointUnion (homIndistinguishability 𝓕) ↔ IsSummandClosed (cl 𝓕) :=
  ⟨fun h => (GraphClass.PreservedUnderDisjointUnion.cl_isSummandClosed h), PreservedUnderDisjointUnion.of_cl_isSummandClosed⟩

end GraphClass

end SimpleGraph

end Lax871432Proofs
