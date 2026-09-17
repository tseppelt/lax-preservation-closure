/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Lax871432Proofs.Hom.Complement
import Lax871432Proofs.HomInd.Closure

/-!
# Taking minors and preservation under complements

**`thm:complement`.**  For a class `𝓕` of finite simple graphs and the assertions

1. `𝓕` is closed under edge contraction and deletion;
2. `≡[𝓕]` is *preserved under taking complements*: `G ≡[𝓕] H` if and only if `Gᶜ ≡[𝓕] Hᶜ`;
3. `cl 𝓕` is minor-closed,

the implications (1) ⇒ (2) ⇔ (3) hold.  This answers Question 8 of Roberson,
*Oddomorphisms and homomorphism indistinguishability over graph classes* (2022), and yields
unconditionally that `cl 𝓕` is minor-closed — the first general evidence for Roberson's
conjecture.

The properties themselves are defined in `HomInd/Closure.lean`.

## Proof outline

The engine is `SimpleGraph.homCount_compl` (`eq:del-contr`) from `Hom/Complement.lean`:

  `hom(F, Gᶜ) = ∑_{s ⊆ E(F)} (-1)^{|s|} ∑_{L ⊆ s} hom(F_s ⊘ L, G)`,

a signed linear combination of homomorphism counts into `G` whose graphs `F_s ⊘ L` are all
minors of `F`.

* (1) ⇒ (2): if `𝓕` is closed under edge deletion and contraction then every `F_s ⊘ L` above
  lies in `𝓕`, so both sides are determined by `≡[𝓕]`.
* (2) ⇒ (3): fix `F ∈ cl 𝓕` and a minor `K` of `F` obtained by one deletion or one
  contraction.  Group the summands of `eq:del-contr` by isomorphism type
  (`SimpleGraph.exists_graphFamily`, the *signed* grouping step) and show that the coefficient
  of `hom(K, -)` does not vanish; `SimpleGraph.mem_cl_of_determines` then gives `K ∈ cl 𝓕`.
  The coefficient computation uses `SimpleGraph.card_edgeSet_spanningSubgraph` and
  `SimpleGraph.card_edgeSet_contractionQuotient_singleton_of_isEmpty` (`obs:edges-contract`):
  - for a *deletion* `K = F - e`, the only pairs `(s, L)` with `F_s ⊘ L ≅ K` have `L = ∅` and
    `|s| = |E(K)|`, so the coefficient is a nonzero multiple of `(-1)^{|E(K)|}`;
  - for a *contraction* `K = F ⊘ {e}` (after deleting edges so that no vertex forms a triangle
    with `e`), the only such pairs have `s = E(F)` and `L` a single edge, each contributing
    `(-1)^{|E(F)|}`, so the coefficient is a nonzero multiple of `(-1)^{|E(F)|}`.
  Closure under vertex deletion is supplied by `lem:minors`, and minor-closedness then follows
  from `SimpleGraph.GraphClass.isMinorClosed_of_atomic_single` — the single-edge form, since
  that is all the coefficient analysis yields directly.
* (3) ⇒ (2): apply (1) ⇒ (2) to `cl 𝓕` and use `SimpleGraph.homIndistinguishable_cl_iff`.

## Main declarations

* `SimpleGraph.GraphClass.preservedUnderCompl_iff_cl_isMinorClosed`: **`thm:complement`**.

## References

* Roberson, *Oddomorphisms and homomorphism indistinguishability over graph classes* (2022).
* Lovász, *Large Networks and Graph Limits* (2012), equation (5.23).
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

open scoped LoopGraph

variable {𝓕 : GraphClass}

/-! ### The coefficient analysis -/

/-- Deleting an edge of `F` gives a graph with the same vertices and one edge fewer.  Hence in
`eq:del-contr` a summation index `(s, L)` can only produce it when nothing is contracted and
`|s| = |E(F)| - 1`; every such term therefore carries the *same* sign `(-1)^{|E(F)| - 1}`, and
the coefficient of `hom(F - e, -)` cannot vanish.

The index `(E(F) \ {e}, ∅)` does produce `F - e`, so the coefficient is a nonzero multiple of
that sign. -/
theorem eq_empty_and_card_succ_of_iso_deleteEdges {V : Type*} [Finite V] {F : SimpleGraph V}
    {e : Sym2 V} (he : e ∈ F.edgeSet) {s L : Finset F.edgeSet}
    (h : Nonempty ((toLoopGraph (F.deleteEdges {e})) ≃lg
      (((spanningSubgraph F) ((edgeSetOf F) s)) ⊘ (edgeSetOf F) L))) :
    L = ∅ ∧ s.card + 1 = Nat.card F.edgeSet := by
  -- Contracting anything would lose a vertex, but `F - e` has all of them.
  have hvert : Nat.card V =
      Nat.card (fromEdgeSet ((edgeSetOf F) L)).ConnectedComponent := Nat.card_congr h.some.toEquiv
  have hL : L = ∅ := by
    by_contra hne
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hne
    obtain ⟨f, hf⟩ := a
    induction f using Sym2.ind with
    | h x y =>
      rw [mem_edgeSet] at hf
      exact absurd (card_connectedComponent_lt (L := (edgeSetOf F) L) hf.ne
        ((mem_edgeSetOf_iff F L ⟨s(x, y), hf⟩).2 ha)) (by omega)
  subst hL
  -- With nothing contracted the quotient is the spanning subgraph itself.
  refine ⟨rfl, ?_⟩
  have h0 : (edgeSetOf F) (∅ : Finset F.edgeSet) = (∅ : Set (Sym2 V)) := by
    simp [SimpleGraph.edgeSetOf]
  rw [h0] at h
  have hiso : (F.deleteEdges {e}) ≃g ((spanningSubgraph F) ((edgeSetOf F) s)) :=
    h.some.trans (nonempty_iso_contractionQuotient_empty _).some
  have hedges : Nat.card (F.deleteEdges {e}).edgeSet =
      Nat.card ((spanningSubgraph F) ((edgeSetOf F) s)).edgeSet := Nat.card_congr hiso.mapEdgeSet
  rw [card_edgeSet_spanningSubgraph] at hedges
  have := card_edgeSet_deleteEdges_singleton_add_one he
  omega

/-- Contracting a single edge `uv` of `F`, when no vertex forms a triangle with `uv`, gives a
graph with one vertex and one edge fewer.  Hence in `eq:del-contr` a summation index `(s, L)`
can only produce it when `s = E(F)` and exactly one edge is contracted; every such term
therefore carries the same sign `(-1)^{|E(F)|}`, and the coefficient of `hom(F ⊘ uv, -)` cannot
vanish.

Losing a vertex forces `L` to be nonempty, and losing only one edge forces it to be a
singleton, since contracting `L` destroys at least `|L|` edges
(`SimpleGraph.card_edgeSet_contractionQuotient_add_card_le`). -/
theorem eq_univ_and_card_eq_one_of_iso_contract {V : Type*} [Finite V] {F : SimpleGraph V}
    [Fintype F.edgeSet] {u v : V} (huv : F.Adj u v)
    (htri : IsEmpty {w : V // F.Adj u w ∧ F.Adj v w}) {s L : Finset F.edgeSet} (hL : L ⊆ s)
    (h : Nonempty ((F ⊘ ({s(u, v)} : Set (Sym2 V))) ≃lg
      (((spanningSubgraph F) ((edgeSetOf F) s)) ⊘ (edgeSetOf F) L))) :
    s = Finset.univ ∧ L.card = 1 := by
  -- What the two sides of the isomorphism know about vertices and edges.
  have hVpos : 0 < Nat.card V := Nat.card_pos_iff.2 ⟨⟨u⟩, ‹Finite V›⟩
  have hEpos : 0 < Nat.card F.edgeSet :=
    Nat.card_pos_iff.2 ⟨⟨⟨s(u, v), huv⟩⟩, inferInstance⟩
  have hVK := card_contractionQuotient_singleton huv
  have hEK := card_edgeSet_contractionQuotient_singleton_of_isEmpty huv htri
  have hViso : Nat.card (fromEdgeSet ({s(u, v)} : Set (Sym2 V))).ConnectedComponent =
      Nat.card (fromEdgeSet ((edgeSetOf F) L)).ConnectedComponent := Nat.card_congr h.some.toEquiv
  have hEiso : Nat.card (F ⊘ ({s(u, v)} : Set (Sym2 V))).edgeSet =
      Nat.card (((spanningSubgraph F) ((edgeSetOf F) s)) ⊘ (edgeSetOf F) L).edgeSet :=
    Nat.card_congr h.some.mapEdgeSet
  -- Contracting `L` destroys at least `|L|` of the `|s|` remaining edges.
  have hbound := card_edgeSet_contractionQuotient_add_card_le
    ((spanningSubgraph F) ((edgeSetOf F) s)) ((edgeSetOf_subset_edgeSet_spanningSubgraph F) hL)
  rw [card_edgeSet_spanningSubgraph, card_edgeSetOf] at hbound
  have hcard : Nat.card F.edgeSet = Fintype.card F.edgeSet := Nat.card_eq_fintype_card
  have hscard : s.card ≤ Fintype.card F.edgeSet := Finset.card_le_univ s
  -- A vertex is lost, so something is contracted.
  have hLpos : 0 < L.card := by
    rcases Nat.eq_zero_or_pos L.card with hzero | hpos
    · exfalso
      have h0 : (edgeSetOf F) L = (∅ : Set (Sym2 V)) := by
        rw [Finset.card_eq_zero] at hzero
        simp [hzero, SimpleGraph.edgeSetOf]
      rw [h0] at hViso
      have := Nat.card_congr
        (nonempty_iso_contractionQuotient_empty (V := V) ⊥).some.toEquiv
      omega
    · exact hpos
  refine ⟨Finset.eq_univ_of_card s ?_, ?_⟩ <;> omega

/-! ### `thm:complement` -/

namespace GraphClass

/-- Complementation is an involution, so preservation under complements is automatically an
equivalence. -/
theorem PreservedUnderCompl.iff (hp : PreservedUnderCompl (homIndistinguishability 𝓕)) {V W : Type} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) : (G ≡[𝓕] H) ↔ (Gᶜ ≡[𝓕] Hᶜ) := by
  refine ⟨hp G H, fun h => ?_⟩
  have hc := hp Gᶜ Hᶜ h
  rwa [compl_compl, compl_compl] at hc

/-- **`thm:complement`, (1) ⇒ (2)**: if `𝓕` is closed under deleting and contracting edges then
`≡[𝓕]` is preserved under taking complements.

Every graph `F_s ⊘ L` occurring in `SimpleGraph.homCount_compl` is obtained from `F` by such
operations, so all its homomorphism counts are determined by `≡[𝓕]`.  The terms whose
contraction quotient carries a loop vanish on both sides and need no hypothesis. -/
theorem IsEdgeContractionClosed.preservedUnderCompl (hd : IsEdgeDeletionClosed 𝓕)
    (hc : IsEdgeContractionClosed 𝓕) : PreservedUnderCompl (homIndistinguishability 𝓕) := by
  classical
  intro V W _ _ G H hGH m F hF
  haveI : Fintype F.edgeSet := Fintype.ofFinite _
  have hFmem : 𝓕.Mem F := (GraphClass.Mem_fin 𝓕 F).2 hF
  -- Each summand of `eq:del-contr` is a homomorphism count from a member of `𝓕`, unless it
  -- vanishes on both sides.
  have key : ∀ s L : Finset F.edgeSet, L ⊆ s →
      LoopGraph.homCount (((spanningSubgraph F) ((edgeSetOf F) s)) ⊘ (edgeSetOf F) L) (toLoopGraph G) =
        LoopGraph.homCount (((spanningSubgraph F) ((edgeSetOf F) s)) ⊘ (edgeSetOf F) L)
          (toLoopGraph H) := by
    intro s L hL
    set X := ((spanningSubgraph F) ((edgeSetOf F) s)) ⊘ (edgeSetOf F) L with hXdef
    by_cases hloop : X.IsLoopless
    · -- `X` is a simple graph, obtained from `F` by deleting and then contracting edges.
      have hmem : 𝓕.Mem (X.toSimpleGraph hloop) :=
        hc ((edgeSetOf_subset_edgeSet_spanningSubgraph F) hL)
          (hd.mem_spanningSubgraph F _ hFmem) _ ⟨RelIso.refl _⟩
      have heq := (homIndistinguishable_iff_forall_mem 𝓕 G H).1 hGH (X.toSimpleGraph hloop) hmem
      rw [← homCount_toLoopGraph, ← homCount_toLoopGraph] at heq
      simpa using heq
    · rw [LoopGraph.homCount_eq_zero_of_not_isLoopless hloop (toLoopGraph_isLoopless G),
        LoopGraph.homCount_eq_zero_of_not_isLoopless hloop (toLoopGraph_isLoopless H)]
  rw [← Nat.cast_inj (R := ℤ), homCount_compl F G, homCount_compl F H]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun L hL => by rw [key s L (Finset.mem_powerset.1 hL)]

/-- **`thm:complement`, (2) ⇒ (3), one edge deletion.**

Group the summands of `eq:del-contr` by isomorphism type.  By
`SimpleGraph.eq_empty_and_card_succ_of_iso_deleteEdges` every index producing `F - e` carries
the sign `(-1)^{|E(F)| - 1}`, so the coefficient of `hom(F - e, -)` is that sign times the
number of such indices, which is at least one. -/
theorem PreservedUnderCompl.cl_mem_deleteEdges_singleton (hp : PreservedUnderCompl (homIndistinguishability 𝓕))
    {V : Type} [Finite V] {F : SimpleGraph V} (hF : (cl 𝓕).Mem F) (e : Sym2 V) :
    (cl 𝓕).Mem (F.deleteEdges {e}) := by
  classical
  haveI : Fintype F.edgeSet := Fintype.ofFinite _
  by_cases he : e ∈ F.edgeSet
  swap
  · rwa [deleteEdges_eq_self.2 (Set.disjoint_singleton_right.2 he)]
  -- The distinguished summation index: keep every edge but `e`, contract nothing.
  set s₀ : Finset F.edgeSet := Finset.univ.erase ⟨e, he⟩ with hs₀def
  have hs₀set : (edgeSetOf F) s₀ = F.edgeSet \ {e} := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.2, fun hx => (Finset.mem_erase.1 ha).1 (Subtype.ext hx)⟩
    · rintro ⟨hx, hxe⟩
      exact ⟨⟨x, hx⟩, Finset.mem_erase.2
        ⟨fun hc => hxe (congrArg (Subtype.val : F.edgeSet → Sym2 V) hc), Finset.mem_univ _⟩, rfl⟩
  have hs₀ : (spanningSubgraph F) ((edgeSetOf F) s₀) = F.deleteEdges {e} := by
    rw [hs₀set]
    ext u v
    simp only [spanningSubgraph_adj, deleteEdges_adj, Set.mem_diff, Set.mem_singleton_iff,
      mem_edgeSet]
    tauto
  have hempty : (edgeSetOf F) (∅ : Finset F.edgeSet) = (∅ : Set (Sym2 V)) := by
    simp [SimpleGraph.edgeSetOf]
  have hloop : (((spanningSubgraph F) ((edgeSetOf F) s₀)) ⊘ (edgeSetOf F) ∅).IsLoopless := by
    rw [hs₀, hempty]; exact contractionQuotient_empty_isLoopless _
  set i₀ : (DelContrIndex F) := ⟨(s₀, ∅), Finset.empty_subset _, hloop⟩ with hi₀def
  have hi₀iso : Nonempty ((toLoopGraph (F.deleteEdges {e})) ≃lg
      (((spanningSubgraph F) ((edgeSetOf F) i₀.1.1)) ⊘ (edgeSetOf F) i₀.1.2)) := by
    change Nonempty (_ ≃lg (((spanningSubgraph F) ((edgeSetOf F) s₀)) ⊘ (edgeSetOf F) ∅))
    rw [hs₀, hempty]
    exact ⟨(nonempty_iso_contractionQuotient_empty _).some.symm⟩
  have hcard₀ : s₀.card + 1 = Nat.card F.edgeSet := by
    rw [hs₀def, Finset.card_erase_of_mem (Finset.mem_univ _), Nat.card_eq_fintype_card,
      Finset.card_univ]
    have : 0 < Fintype.card F.edgeSet := Fintype.card_pos_iff.2 ⟨⟨e, he⟩⟩
    omega
  -- Group the summands of `eq:del-contr` by isomorphism type.
  obtain ⟨κ, _, _, M, β, ρ, hMni, hMiso, hβdef, hsum⟩ :=
    exists_graphFamily (n := Nat.card V) (fun i : (DelContrIndex F) => i.size_le)
      (fun i => i.graph) (fun i => (-1 : ℚ) ^ i.1.1.card)
  -- `≡[𝓕]` determines the linear combination, because it determines `hom(F, -ᶜ)`.
  have hdet : ∀ {X Y : Type} [Finite X] [Finite Y] (G : SimpleGraph X) (H : SimpleGraph Y),
      (G ≡[𝓕] H) → ∑ k, β k * (homCount (M.graph k) G : ℚ) =
        ∑ k, β k * (homCount (M.graph k) H : ℚ) := by
    intro X Y _ _ G H hGH
    rw [← hsum (V := X) G, ← hsum (V := Y) H]
    have hZ : (∑ i : (DelContrIndex F), (-1 : ℤ) ^ i.1.1.card * (homCount i.graph G : ℤ)) =
        ∑ i : (DelContrIndex F), (-1 : ℤ) ^ i.1.1.card * (homCount i.graph H : ℤ) := by
      rw [← homCount_compl_delContr F G, ← homCount_compl_delContr F H,
        homCount_eq_of_Mem_cl hF (hp G H hGH)]
    exact_mod_cast hZ
  -- Every index producing `F - e` carries the same sign.
  have hKiso : Nonempty (F.deleteEdges {e} ≃g M.graph (ρ i₀)) :=
    ⟨(hi₀iso.some.trans (i₀.nonempty_iso).some.symm).trans (hMiso i₀).some⟩
  have hβ : β (ρ i₀) ≠ 0 := by
    have hfib : ∀ i : (DelContrIndex F), ρ i = ρ i₀ →
        (-1 : ℚ) ^ i.1.1.card = (-1 : ℚ) ^ i₀.1.1.card := by
      intro i hρ
      have hiso : Nonempty ((toLoopGraph (F.deleteEdges {e})) ≃lg
          (((spanningSubgraph F) ((edgeSetOf F) i.1.1)) ⊘ (edgeSetOf F) i.1.2)) :=
        ⟨((hKiso.some.trans (hρ ▸ (hMiso i).some.symm)).trans
          (i.nonempty_iso).some)⟩
      obtain ⟨-, hcard⟩ := eq_empty_and_card_succ_of_iso_deleteEdges he hiso
      have hcards : i.1.1.card = s₀.card := by omega
      rw [hcards]
    have hsimp : ∀ i : (DelContrIndex F),
        (if ρ i = ρ i₀ then (-1 : ℚ) ^ i.1.1.card else 0) =
          (if ρ i = ρ i₀ then (-1 : ℚ) ^ i₀.1.1.card else 0) := by
      intro i
      by_cases hρ : ρ i = ρ i₀
      · rw [if_pos hρ, if_pos hρ, hfib i hρ]
      · rw [if_neg hρ, if_neg hρ]
    rw [hβdef, Finset.sum_congr rfl (fun i _ => hsimp i), ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul]
    refine mul_ne_zero (Nat.cast_ne_zero.2 ?_) (pow_ne_zero _ (by norm_num))
    exact Finset.card_ne_zero_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
  -- Conclude by `lem:lincomb`.
  have hmem : (cl 𝓕).mem _ (M.graph (ρ i₀)) := by
    refine mem_cl_of_determines_of_ne_zero 𝓕 M hMni β ?_ hβ
    intro X Y _ _ G H hGH
    exact hdet G H hGH
  rw [(GraphClass.Mem_congr (cl 𝓕)) hKiso.some]
  exact ((GraphClass.Mem_fin (cl 𝓕)) (M.graph (ρ i₀))).2 hmem

/-- **`thm:complement`, (2) ⇒ (3), edge deletion**: deleting a set of edges one at a time. -/
theorem PreservedUnderCompl.cl_isEdgeDeletionClosed (hp : PreservedUnderCompl (homIndistinguishability 𝓕)) :
    IsEdgeDeletionClosed (cl 𝓕) := by
  classical
  intro V _ F₀ t₀ hF₀
  have key : ∀ (n : ℕ) (F : SimpleGraph V), Nat.card F.edgeSet ≤ n →
      ∀ t : Set (Sym2 V), (cl 𝓕).Mem F → (cl 𝓕).Mem (F.deleteEdges t) := by
    intro n
    induction n with
    | zero =>
      intro F hn t hF
      have hemp : F.edgeSet = ∅ := by
        by_contra hne
        obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
        have hpos : 0 < Nat.card F.edgeSet :=
          Nat.card_pos_iff.2 ⟨⟨⟨x, hx⟩⟩, Subtype.finite⟩
        omega
      have hself : F.deleteEdges t = F :=
        deleteEdges_eq_self.2 (by rw [hemp]; exact disjoint_bot_left)
      rwa [hself]
    | succ n ih =>
      intro F hn t hF
      by_cases hdisj : Disjoint F.edgeSet t
      · rwa [deleteEdges_eq_self.2 hdisj]
      · obtain ⟨e, he, het⟩ := Set.not_disjoint_iff.1 hdisj
        have hsub : F.deleteEdges t = (F.deleteEdges {e}).deleteEdges t := by
          ext u v
          simp only [deleteEdges_adj, Set.mem_singleton_iff]
          exact ⟨fun h => ⟨⟨h.1, fun hc => h.2 (hc ▸ het)⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
        rw [hsub]
        have hcard : Nat.card (F.deleteEdges {e}).edgeSet ≤ n := by
          have := card_edgeSet_deleteEdges_singleton_add_one he
          omega
        exact ih (F.deleteEdges {e}) hcard t ((GraphClass.PreservedUnderCompl.cl_mem_deleteEdges_singleton hp) hF e)
  exact key (Nat.card F₀.edgeSet) F₀ le_rfl t₀ hF₀

/-- **`thm:complement`, (2) ⇒ (3), one edge contraction.**

First delete the edges `uw` for the vertices `w` forming a triangle with `uv`; this leaves the
contraction unchanged (`SimpleGraph.contractionQuotient_deleteEdges_triangleEdges`) and puts us
in the situation of `SimpleGraph.eq_univ_and_card_eq_one_of_iso_contract`, where every index of
`eq:del-contr` producing `F ⊘ uv` carries the sign `(-1)^{|E(F)|}`. -/
theorem PreservedUnderCompl.cl_mem_contractionQuotient_singleton (hp : PreservedUnderCompl (homIndistinguishability 𝓕))
    {V : Type} [Finite V] {F : SimpleGraph V} (hF : (cl 𝓕).Mem F) {u v : V} (huv : F.Adj u v)
    {W : Type} [Finite W] (K : SimpleGraph W)
    (hK : Nonempty ((toLoopGraph K) ≃lg (F ⊘ ({s(u, v)} : Set (Sym2 V))))) : (cl 𝓕).Mem K := by
  classical
  -- Delete the triangle edges; this changes neither the contraction nor membership in `cl 𝓕`.
  set F' := F.deleteEdges ((triangleEdges F) u v) with hF'def
  have hF' : (cl 𝓕).Mem F' := (GraphClass.PreservedUnderCompl.cl_isEdgeDeletionClosed hp) F _ hF
  have huv' : F'.Adj u v := adj_deleteEdges_triangleEdges huv
  have htri : IsEmpty {w : V // F'.Adj u w ∧ F'.Adj v w} := isEmpty_triangle_deleteEdges F u v
  rw [← contractionQuotient_deleteEdges_triangleEdges (F := F) huv] at hK
  haveI : Fintype F'.edgeSet := Fintype.ofFinite _
  -- The distinguished summation index: keep every edge, contract `uv`.
  have huvE : s(u, v) ∈ F'.edgeSet := huv'
  set L₀ : Finset F'.edgeSet := {⟨s(u, v), huvE⟩} with hL₀def
  have hunivset : (edgeSetOf F') (Finset.univ : Finset F'.edgeSet) = F'.edgeSet := by
    ext x
    constructor
    · rintro ⟨a, -, rfl⟩
      exact a.2
    · intro hx
      exact ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
  have hspan : (spanningSubgraph F') ((edgeSetOf F') (Finset.univ : Finset F'.edgeSet)) = F' := by
    rw [hunivset]; ext a b; simp [mem_edgeSet]
  have hL₀set : (edgeSetOf F') L₀ = ({s(u, v)} : Set (Sym2 V)) := by
    rw [hL₀def]
    ext x
    simp [SimpleGraph.edgeSetOf]
  have hloop : (((spanningSubgraph F') ((edgeSetOf F') (Finset.univ : Finset F'.edgeSet))) ⊘
      (edgeSetOf F') L₀).IsLoopless := by
    rw [hspan, hL₀set]; exact contractionQuotient_singleton_isLoopless u v
  set i₀ : (DelContrIndex F') := ⟨(Finset.univ, L₀), Finset.subset_univ _, hloop⟩ with hi₀def
  have hi₀iso : Nonempty ((toLoopGraph K) ≃lg
      (((spanningSubgraph F') ((edgeSetOf F') i₀.1.1)) ⊘ (edgeSetOf F') i₀.1.2)) := by
    change Nonempty (_ ≃lg
      (((spanningSubgraph F') ((edgeSetOf F') (Finset.univ : Finset F'.edgeSet))) ⊘ (edgeSetOf F') L₀))
    rw [hspan, hL₀set]
    exact hK
  -- Group the summands of `eq:del-contr` by isomorphism type.
  obtain ⟨κ, _, _, M, β, ρ, hMni, hMiso, hβdef, hsum⟩ :=
    exists_graphFamily (n := Nat.card V) (fun i : (DelContrIndex F') => i.size_le)
      (fun i => i.graph) (fun i => (-1 : ℚ) ^ i.1.1.card)
  have hdet : ∀ {X Y : Type} [Finite X] [Finite Y] (G : SimpleGraph X) (H : SimpleGraph Y),
      (G ≡[𝓕] H) → ∑ k, β k * (homCount (M.graph k) G : ℚ) =
        ∑ k, β k * (homCount (M.graph k) H : ℚ) := by
    intro X Y _ _ G H hGH
    rw [← hsum (V := X) G, ← hsum (V := Y) H]
    have hZ : (∑ i : (DelContrIndex F'), (-1 : ℤ) ^ i.1.1.card * (homCount i.graph G : ℤ)) =
        ∑ i : (DelContrIndex F'), (-1 : ℤ) ^ i.1.1.card * (homCount i.graph H : ℤ) := by
      rw [← homCount_compl_delContr F' G, ← homCount_compl_delContr F' H,
        homCount_eq_of_Mem_cl hF' (hp G H hGH)]
    exact_mod_cast hZ
  have hKiso : Nonempty (K ≃g M.graph (ρ i₀)) :=
    ⟨(hi₀iso.some.trans (i₀.nonempty_iso).some.symm).trans (hMiso i₀).some⟩
  have hβ : β (ρ i₀) ≠ 0 := by
    have hfib : ∀ i : (DelContrIndex F'), ρ i = ρ i₀ →
        (-1 : ℚ) ^ i.1.1.card = (-1 : ℚ) ^ i₀.1.1.card := by
      intro i hρ
      have hiso : Nonempty ((F' ⊘ ({s(u, v)} : Set (Sym2 V))) ≃lg
          (((spanningSubgraph F') ((edgeSetOf F') i.1.1)) ⊘ (edgeSetOf F') i.1.2)) :=
        ⟨hK.some.symm.trans
          ((hKiso.some.trans (hρ ▸ (hMiso i).some.symm)).trans (i.nonempty_iso).some)⟩
      obtain ⟨huniv, -⟩ := eq_univ_and_card_eq_one_of_iso_contract huv' htri i.2.1 hiso
      rw [huniv]
    have hsimp : ∀ i : (DelContrIndex F'),
        (if ρ i = ρ i₀ then (-1 : ℚ) ^ i.1.1.card else 0) =
          (if ρ i = ρ i₀ then (-1 : ℚ) ^ i₀.1.1.card else 0) := by
      intro i
      by_cases hρ : ρ i = ρ i₀
      · rw [if_pos hρ, if_pos hρ, hfib i hρ]
      · rw [if_neg hρ, if_neg hρ]
    rw [hβdef, Finset.sum_congr rfl (fun i _ => hsimp i), ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul]
    refine mul_ne_zero (Nat.cast_ne_zero.2 ?_) (pow_ne_zero _ (by norm_num))
    exact Finset.card_ne_zero_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
  have hmem : (cl 𝓕).mem _ (M.graph (ρ i₀)) := by
    refine mem_cl_of_determines_of_ne_zero 𝓕 M hMni β ?_ hβ
    intro X Y _ _ G H hGH
    exact hdet G H hGH
  rw [(GraphClass.Mem_congr (cl 𝓕)) hKiso.some]
  exact ((GraphClass.Mem_fin (cl 𝓕)) (M.graph (ρ i₀))).2 hmem

/-- **`thm:complement`, (2) ⇒ (3), edge contraction**, in single-edge form. -/
theorem PreservedUnderCompl.cl_isSingleEdgeContractionClosed (hp : PreservedUnderCompl (homIndistinguishability 𝓕)) :
    IsSingleEdgeContractionClosed (cl 𝓕) := by
  intro V _ F u v huv hF W _ K he
  exact (GraphClass.PreservedUnderCompl.cl_mem_contractionQuotient_singleton hp) hF huv K he

/-- **`thm:complement`, (2) ⇒ (3)**: if `≡[𝓕]` is preserved under taking complements then
`cl 𝓕` is minor-closed.

Closure under deleting edges and under contracting a single edge are the two coefficient
computations above; closure under deleting vertices is `lem:minors`; and
`SimpleGraph.GraphClass.isMinorClosed_of_atomic_single` assembles them. -/
theorem PreservedUnderCompl.cl_isMinorClosed (hp : PreservedUnderCompl (homIndistinguishability 𝓕)) :
    IsMinorClosed (cl 𝓕) :=
  isMinorClosed_of_atomic_single (GraphClass.PreservedUnderCompl.cl_isEdgeDeletionClosed hp)
    (IsEdgeDeletionClosed.cl_isSubgraphClosed (GraphClass.PreservedUnderCompl.cl_isEdgeDeletionClosed hp)).2
    (GraphClass.PreservedUnderCompl.cl_isSingleEdgeContractionClosed hp)

/-- **`thm:complement`, (2) ⇒ (3), edge contraction**: contracting any set of edges, which
follows from minor-closedness. -/
theorem PreservedUnderCompl.cl_isEdgeContractionClosed (hp : PreservedUnderCompl (homIndistinguishability 𝓕)) :
    IsEdgeContractionClosed (cl 𝓕) := by
  have h : IsMinorClosed (cl 𝓕) := (GraphClass.PreservedUnderCompl.cl_isMinorClosed hp)
  intro V _ F L hL hF W _ K he
  exact h K (isMinor_of_iso_contractionQuotient hL he.some) hF

/-- **`thm:complement`, (3) ⇒ (2)**: this follows from (1) ⇒ (2) applied to `cl 𝓕`, since
`≡[𝓕]` and `≡[cl 𝓕]` coincide. -/
theorem PreservedUnderCompl.of_cl_isMinorClosed (h : IsMinorClosed (cl 𝓕)) :
    PreservedUnderCompl (homIndistinguishability 𝓕) := by
  intro V W _ _ G H hGH
  replace hGH : G ≡[𝓕] H := hGH
  show Gᶜ ≡[𝓕] Hᶜ
  rw [← homIndistinguishable_cl_iff] at hGH ⊢
  exact IsEdgeContractionClosed.preservedUnderCompl (GraphClass.IsMinorClosed.isEdgeDeletionClosed h)
    (GraphClass.IsMinorClosed.isEdgeContractionClosed h) G H hGH

/-- **`thm:complement`**: `≡[𝓕]` is preserved under taking complements if and only if `cl 𝓕`
is minor-closed; and this holds whenever `𝓕` itself is closed under deleting and contracting
edges (`SimpleGraph.GraphClass.IsEdgeContractionClosed.preservedUnderCompl`). -/
theorem preservedUnderCompl_iff_cl_isMinorClosed (𝓕 : GraphClass) :
    PreservedUnderCompl (homIndistinguishability 𝓕) ↔ IsMinorClosed (cl 𝓕) :=
  ⟨fun h => (GraphClass.PreservedUnderCompl.cl_isMinorClosed h), PreservedUnderCompl.of_cl_isMinorClosed⟩

end GraphClass

end SimpleGraph

end Lax871432Proofs
