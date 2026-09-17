/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Lax871432Proofs.GraphTheory.Minor
import Lax871432Proofs.Hom.DisjUnion
import Lax871432Proofs.HomInd.Basic
import Lax871432.ClosureProperties
import Lax871432.PreservationProperties

/-!
# Closure and preservation properties of graph classes

This file collects the properties of a graph class `𝓕` and of its homomorphism
indistinguishability relation `≡[𝓕]` that the theorems of the paper relate to one another, and
the general lemmas about them.  The theorems themselves are in the `PreservationClosure`
library.

Two kinds of property occur:

* *closure properties* of `𝓕` — closure under taking summands, deleting edges or vertices,
  contracting edges, taking minors;
* *preservation properties* of `≡[𝓕]` — preservation under disjoint unions and under taking
  complements.

Also here are the two *grouping* lemmas, which turn a linear combination of homomorphism
counts into one indexed by pairwise non-isomorphic graphs, as required by
`SimpleGraph.mem_cl_of_determines`.

## Main declarations

* `SimpleGraph.GraphClass.IsSummandClosed`, `IsEdgeDeletionClosed`, `IsVertexDeletionClosed`,
  `IsEdgeContractionClosed`, `IsSubgraphClosed`, `IsMinorClosed`.
* `SimpleGraph.GraphClass.PreservedUnderDisjointUnion`, `PreservedUnderCompl`.
* `SimpleGraph.exists_graphFamily_of_pos`, `SimpleGraph.exists_graphFamily`: grouping.
* `SimpleGraph.GraphClass.IsEdgeDeletionClosed.isVertexDeletionClosed`: `lem:minors`.
* `SimpleGraph.GraphClass.isMinorClosed_of_atomic`: minor-closedness from the three atomic
  closure operations.
* `SimpleGraph.GraphClass.isMinorClosed_of_atomic_single`: the same, needing only *single*-edge
  contraction.

## Implementation notes

Deleting edges, deleting vertices and contracting edges are all stated for *sets*, matching
the way they occur in `SimpleGraph.homCount_compl`.  This makes
`SimpleGraph.GraphClass.isMinorClosed_of_atomic` a direct consequence of
`SimpleGraph.isMinor_iff_exists_induce_spanningSubgraph_contraction`.

`thm:complement`, however, only produces closure under contracting a *single* edge, so
`IsSingleEdgeContractionClosed` is provided as well.  It is not weaker in the presence of the
other two closure properties: `SimpleGraph.GraphClass.isMinorClosed_of_atomic_single` derives
minor-closedness from it by induction on the number of vertices, and minor-closedness gives
back the set-valued form.

The contraction quotient is a `LoopGraph`, so neither property can simply assert that it lies
in the class; both quantify over all simple graphs isomorphic to it instead.
-/

namespace Lax871432Proofs

open _root_.SimpleGraph
open Lax871432.HomomorphismCounts Lax871432.LovaszTheorem
open Lax871432.HomomorphismIndistinguishability Lax871432.DistinguishingClosure
open scoped Lax871432.HomomorphismIndistinguishability
open Lax871432.ClosureProperties Lax871432.PreservationProperties
open Lax68.GraphMinors

open Function

namespace SimpleGraph

open scoped LoopGraph

namespace GraphClass

variable {𝓕 : GraphClass}

/-! ### Closure properties -/

/-- A graph class is *closed under deleting edges* if removing a set of edges from a member
gives a member. -/
def IsEdgeDeletionClosed (𝓕 : GraphClass) : Prop :=
  ∀ {V : Type} [Finite V] (F : SimpleGraph V) (s : Set (Sym2 V)), 𝓕.Mem F →
    𝓕.Mem (F.deleteEdges s)

/-- Deleting the edges outside `s` keeps a member in the class. -/
theorem IsEdgeDeletionClosed.mem_spanningSubgraph (h : IsEdgeDeletionClosed 𝓕) {V : Type}
    [Finite V] (F : SimpleGraph V) (s : Set (Sym2 V)) (hF : 𝓕.Mem F) :
    𝓕.Mem ((spanningSubgraph F) s) := by
  rw [spanningSubgraph_eq_deleteEdges]
  exact h F sᶜ hF

/-- A graph class is *closed under deleting vertices* if every induced subgraph of a member is
a member. -/
def IsVertexDeletionClosed (𝓕 : GraphClass) : Prop :=
  ∀ {V : Type} [Finite V] (F : SimpleGraph V) (s : Set V), 𝓕.Mem F → 𝓕.Mem (F.induce s)

/-- A graph class is *closed under contracting edges* if contracting a set of edges of a member
gives a member.  The contraction quotient is a `LoopGraph`, so membership is asserted for every
simple graph isomorphic to it — for a set of edges whose contraction creates a loop there is no
such graph and the condition is vacuous.

Contracting a *single* edge never creates a loop
(`SimpleGraph.contractionQuotient_singleton_isLoopless`), so the single-edge instance of this
property is never vacuous; see `SimpleGraph.GraphClass.IsEdgeContractionClosed.mem_singleton`. -/
def IsEdgeContractionClosed (𝓕 : GraphClass) : Prop :=
  ∀ {V : Type} [Finite V] {F : SimpleGraph V} {L : Set (Sym2 V)}, L ⊆ F.edgeSet → 𝓕.Mem F →
    ∀ {W : Type} [Finite W] (K : SimpleGraph W),
      Nonempty ((toLoopGraph K) ≃lg (F ⊘ L)) → 𝓕.Mem K

/-- The single-edge instance of `SimpleGraph.GraphClass.IsEdgeContractionClosed`. -/
theorem IsEdgeContractionClosed.mem_singleton (h : IsEdgeContractionClosed 𝓕) {V : Type}
    [Finite V] {F : SimpleGraph V} {u v : V} (huv : F.Adj u v) (hF : 𝓕.Mem F) {W : Type}
    [Finite W] (K : SimpleGraph W)
    (he : Nonempty ((toLoopGraph K) ≃lg (F ⊘ ({s(u, v)} : Set (Sym2 V))))) : 𝓕.Mem K :=
  h (Set.singleton_subset_iff.2 (F.mem_edgeSet.2 huv)) hF K he

/-- A graph class is *closed under contracting a single edge* if contracting one edge of a
member gives a member.  This is the form of edge-contraction closure that the proof of
`thm:complement` establishes for `cl 𝓕`; by
`SimpleGraph.GraphClass.isMinorClosed_of_atomic_single` it already implies minor-closedness,
and hence the apparently stronger `SimpleGraph.GraphClass.IsEdgeContractionClosed`. -/
def IsSingleEdgeContractionClosed (𝓕 : GraphClass) : Prop :=
  ∀ {V : Type} [Finite V] {F : SimpleGraph V} {u v : V}, F.Adj u v → 𝓕.Mem F →
    ∀ {W : Type} [Finite W] (K : SimpleGraph W),
      Nonempty ((toLoopGraph K) ≃lg (F ⊘ ({s(u, v)} : Set (Sym2 V)))) → 𝓕.Mem K

theorem IsEdgeContractionClosed.isSingleEdgeContractionClosed
    (h : IsEdgeContractionClosed 𝓕) : IsSingleEdgeContractionClosed 𝓕 := by
  intro V _ F u v huv hF W _ K he
  exact h.mem_singleton huv hF K he

/-- A graph class is *closed under taking subgraphs* if it is closed under deleting edges and
vertices. -/
def IsSubgraphClosed (𝓕 : GraphClass) : Prop :=
  IsEdgeDeletionClosed 𝓕 ∧ IsVertexDeletionClosed 𝓕

end GraphClass

variable {𝓕 : GraphClass}

/-! ### Grouping summands by isomorphism type -/

/-- **Grouping step.**  A linear combination `∑ i, α i * hom(L i, -)` with strictly positive
coefficients can be rewritten as a linear combination over a family of *pairwise
non-isomorphic* graphs with nonzero coefficients, by summing the coefficients of isomorphic
members.  Every `L i` is isomorphic to a member of the new family.

This is what makes `SimpleGraph.mem_cl_of_determines` applicable to `eq:disjunion`: distinct
subsets of the parts of `F` may well give isomorphic unions. -/
theorem exists_graphFamily_of_pos {ι : Type} [Fintype ι] {n : ℕ} {size : ι → ℕ}
    (hsize : ∀ i, size i ≤ n) (L : ∀ i, SimpleGraph (Fin (size i))) {α : ι → ℚ}
    (hα : ∀ i, 0 < α i) :
    ∃ (κ : Type) (_ : Fintype κ) (M : GraphFamily n κ) (β : κ → ℚ),
      M.PairwiseNonIso ∧ (∀ k, β k ≠ 0) ∧ (∀ i, ∃ k, Nonempty (L i ≃g M.graph k)) ∧
        ∀ {V : Type} [Finite V] (G : SimpleGraph V),
          ∑ i, α i * (homCount (L i) G : ℚ) = ∑ k, β k * (homCount (M.graph k) G : ℚ) := by
  classical
  set R := repFamily n with hRdef
  have hRni : R.PairwiseNonIso := repFamily_pairwiseNonIso n
  have hRex : R.IsExhaustive := repFamily_isExhaustive n
  haveI : Fintype (Quotient (boundedGraphSetoid n)) := Fintype.ofFinite _
  -- The isomorphism class of `L i` inside the family of all representatives.
  have hiso : ∀ i, ∃ k, Nonempty (L i ≃g R.graph k) := fun i =>
    GraphFamily.exists_iso R hRex (L i) (by simpa using hsize i)
  set ρ : ι → Quotient (boundedGraphSetoid n) := fun i => (hiso i).choose with hρdef
  have hρ : ∀ i, Nonempty (L i ≃g R.graph (ρ i)) := fun i => (hiso i).choose_spec
  -- Keep only the classes that actually occur, and add up their coefficients.
  refine ⟨{k // ∃ i, ρ i = k}, inferInstance,
    { size := fun k => R.size k.1
      size_le := fun k => R.size_le k.1
      graph := fun k => R.graph k.1 },
    fun k => ∑ i, if ρ i = k.1 then α i else 0, ?_, ?_,
    fun i => ⟨⟨ρ i, ⟨i, rfl⟩⟩, hρ i⟩, ?_⟩
  · exact fun k k' hne hiso' => hne (Subtype.ext (GraphFamily.PairwiseNonIso.eq hRni hiso'))
  · intro k
    obtain ⟨i₀, hi₀⟩ := k.2
    have hpos : (0 : ℚ) < ∑ i, if ρ i = k.1 then α i else 0 := by
      refine Finset.sum_pos' (fun i _ => ?_) ⟨i₀, Finset.mem_univ _, ?_⟩
      · split_ifs with h
        · exact (hα i).le
        · exact le_rfl
      · rw [if_pos hi₀]; exact hα i₀
    exact ne_of_gt hpos
  · intro V _ G
    have hswap : ∀ i : ι, (homCount (L i) G : ℚ) = (homCount (R.graph (ρ i)) G : ℚ) := by
      intro i; rw [homCount_congr_left (hρ i).some G]
    simp_rw [hswap, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Eq.symm ?_
    -- Only the isomorphism class of `L i` contributes to the inner sum.
    refine (Finset.sum_eq_single_of_mem
      (f := fun k : {k // ∃ i, ρ i = k} =>
        (if ρ i = ↑k then α i else 0) * (homCount (R.graph ↑k) G : ℚ))
      ⟨ρ i, ⟨i, rfl⟩⟩ (Finset.mem_univ _) fun k _ hk => ?_).trans ?_
    · change (if ρ i = ↑k then α i else 0) * (homCount (R.graph ↑k) G : ℚ) = 0
      rw [if_neg fun h : ρ i = ↑k => hk (Subtype.ext h.symm), zero_mul]
    · change (if ρ i = ρ i then α i else 0) * (homCount (R.graph (ρ i)) G : ℚ) = _
      rw [if_pos rfl]
/-- **Grouping step, signed version.**  Any linear combination `∑ i, α i * hom(L i, -)` can be
rewritten as a linear combination over a family of *pairwise non-isomorphic* graphs, the new
coefficient of a graph being the sum of the `α i` over all `i` with `L i ≅ M.graph k`.

This generalises `SimpleGraph.exists_graphFamily_of_pos`, which additionally concludes that the
new coefficients are nonzero from positivity of the old ones.  With signs present that is false
in general, so `SimpleGraph.mem_cl_of_determines` can only be applied after checking
non-vanishing by hand — which is precisely the coefficient analysis in the proof of
`thm:complement`. -/
theorem exists_graphFamily {ι : Type} [Fintype ι] {n : ℕ} {size : ι → ℕ}
    (hsize : ∀ i, size i ≤ n) (L : ∀ i, SimpleGraph (Fin (size i))) (α : ι → ℚ) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (M : GraphFamily n κ) (β : κ → ℚ)
        (ρ : ι → κ),
      M.PairwiseNonIso ∧
      (∀ i, Nonempty (L i ≃g M.graph (ρ i))) ∧
      (∀ k, β k = ∑ i, if ρ i = k then α i else 0) ∧
      ∀ {V : Type} [Finite V] (G : SimpleGraph V),
        ∑ i, α i * (homCount (L i) G : ℚ) = ∑ k, β k * (homCount (M.graph k) G : ℚ) := by
  classical
  set R := repFamily n with hRdef
  have hRni : R.PairwiseNonIso := repFamily_pairwiseNonIso n
  have hRex : R.IsExhaustive := repFamily_isExhaustive n
  haveI : Fintype (Quotient (boundedGraphSetoid n)) := Fintype.ofFinite _
  have hiso : ∀ i, ∃ k, Nonempty (L i ≃g R.graph k) := fun i =>
    GraphFamily.exists_iso R hRex (L i) (by simpa using hsize i)
  set r : ι → Quotient (boundedGraphSetoid n) := fun i => (hiso i).choose with hrdef
  have hr : ∀ i, Nonempty (L i ≃g R.graph (r i)) := fun i => (hiso i).choose_spec
  -- The index type is the set of isomorphism classes that actually occur.
  refine ⟨{k // ∃ i, r i = k}, inferInstance, inferInstance,
    { size := fun k => R.size k.1
      size_le := fun k => R.size_le k.1
      graph := fun k => R.graph k.1 },
    fun k => ∑ i, if (⟨r i, ⟨i, rfl⟩⟩ : {k // ∃ i, r i = k}) = k then α i else 0,
    fun i => ⟨r i, ⟨i, rfl⟩⟩, ?_, fun i => hr i, fun _ => rfl, ?_⟩
  · exact fun k k' hne hiso' => hne (Subtype.ext (GraphFamily.PairwiseNonIso.eq hRni hiso'))
  · intro V _ G
    have hswap : ∀ i : ι, (homCount (L i) G : ℚ) = (homCount (R.graph (r i)) G : ℚ) := by
      intro i; rw [homCount_congr_left (hr i).some G]
    simp_rw [hswap, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Eq.symm ?_
    -- Only the isomorphism class of `L i` contributes to the inner sum.
    refine (Finset.sum_eq_single_of_mem
      (f := fun k : {k // ∃ i, r i = k} =>
        (if (⟨r i, ⟨i, rfl⟩⟩ : {k // ∃ i, r i = k}) = k then α i else 0) *
          (homCount (R.graph ↑k) G : ℚ))
      ⟨r i, ⟨i, rfl⟩⟩ (Finset.mem_univ _) fun k _ hk => ?_).trans ?_
    · change (if (⟨r i, ⟨i, rfl⟩⟩ : {k // ∃ i, r i = k}) = k then α i else 0) *
        (homCount (R.graph ↑k) G : ℚ) = 0
      rw [if_neg fun h => hk h.symm, zero_mul]
    · change (if (⟨r i, ⟨i, rfl⟩⟩ : {k // ∃ i, r i = k}) = ⟨r i, ⟨i, rfl⟩⟩ then α i else 0) *
        (homCount (R.graph (r i)) G : ℚ) = _
      rw [if_pos rfl]

/-! ### `lem:minors` -/

/-- Deleting every edge that meets `sᶜ` isolates the vertices outside `s`; if the result and
the edgeless graph both lie in a homomorphism distinguishing closed class, so does `F[s]`.

The edgeless graph on `α` sees the number of vertices of a target, and splitting off the
isolated vertices via `SimpleGraph.homCount_deleteIncidence` multiplies the count by a power of
that number, which may therefore be cancelled. -/
theorem GraphClass.mem_induce_of_mem_deleteIncidence (hcl : IsHomDistinguishingClosed 𝓕)
    {α : Type} [Finite α] {F : SimpleGraph α} {s : Set α}
    (hbot : 𝓕.Mem (⊥ : SimpleGraph α))
    (hisol : 𝓕.Mem (F.deleteEdges (incidenceEdges s))) : 𝓕.Mem (F.induce s) := by
  refine hcl _ ((GraphClass.Mem_cl_of_forall 𝓕) fun {V W} _ _ G H hGH => ?_)
  have htest : ∀ {β : Type} [Finite β] (F : SimpleGraph β), 𝓕.Mem F →
      homCount F G = homCount F H := (homIndistinguishable_iff_forall_mem 𝓕 G H).1 hGH
  rcases isEmpty_or_nonempty α with hα | ⟨⟨v⟩⟩
  · -- With no vertices at all there is nothing to delete.
    haveI : IsEmpty ↥s := ⟨fun x => hα.elim x.1⟩
    have e : (F.induce s) ≃g (⊥ : SimpleGraph α) :=
      ⟨Equiv.equivOfIsEmpty (↥s) α, fun {a _} => isEmptyElim a⟩
    rw [homCount_congr_left e G, homCount_congr_left e H]
    exact htest _ hbot
  -- The edgeless graph on `α` sees the number of vertices of the target.
  have hcard : Nat.card V = Nat.card W := by
    have hpow := htest _ hbot
    rw [homCount_bot, homCount_bot] at hpow
    exact Nat.pow_left_injective (Nat.card_pos_iff.2 ⟨⟨v⟩, ‹Finite α›⟩).ne' hpow
  -- Splitting off the isolated vertices multiplies by a power of that number.
  have hsplit := htest _ hisol
  rw [homCount_deleteIncidence, homCount_deleteIncidence, hcard] at hsplit
  rcases Nat.eq_zero_or_pos (Nat.card W) with hzero | hpos
  · -- Both targets are empty, hence isomorphic.
    haveI : IsEmpty W := not_nonempty_iff.1 fun hne =>
      absurd (Nat.card_pos_iff.2 ⟨hne, ‹Finite W›⟩) (by omega)
    haveI : IsEmpty V := not_nonempty_iff.1 fun hne =>
      absurd (Nat.card_pos_iff.2 ⟨hne, ‹Finite V›⟩) (by omega)
    exact homCount_congr_right _ ⟨Equiv.equivOfIsEmpty V W, fun {a _} => isEmptyElim a⟩
  · exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos hpos) hsplit

/-- **`lem:minors`**: a homomorphism distinguishing closed graph class which is closed under
deleting edges is closed under deleting vertices, hence under taking subgraphs.

Deleting all edges of a member `F` on `n` vertices puts `n • K₁` into the class, so
`≡[𝓕]` determines the vertex count; splitting off an isolated vertex via
`SimpleGraph.homCount_sum_left` then transfers membership from `F` to `F - v`. -/
theorem GraphClass.IsEdgeDeletionClosed.isVertexDeletionClosed
    (hcl : IsHomDistinguishingClosed 𝓕) (h : IsEdgeDeletionClosed 𝓕) :
    IsVertexDeletionClosed 𝓕 := by
  intro α _ F s hF
  have hbot : 𝓕.Mem (⊥ : SimpleGraph α) := by
    have := h F Set.univ hF; rwa [deleteEdges_univ] at this
  exact GraphClass.mem_induce_of_mem_deleteIncidence hcl hbot (h F _ hF)

/-- `cl 𝓕` version of `lem:minors`: the distinguishing closure is always homomorphism
distinguishing closed (`SimpleGraph.GraphClass.cl_cl`), so `lem:minors` applies to it. -/
theorem GraphClass.IsEdgeDeletionClosed.cl_isSubgraphClosed (h : IsEdgeDeletionClosed (cl 𝓕)) :
    IsSubgraphClosed (cl 𝓕) :=
  ⟨h, GraphClass.IsEdgeDeletionClosed.isVertexDeletionClosed (GraphClass.cl_cl 𝓕) h⟩

/-! ### Minor-closedness -/

namespace GraphClass

/-- Closure under deleting edges and vertices and under contracting edges implies
minor-closedness, since every minor arises from such operations
(`SimpleGraph.isMinor_iff_exists_induce_spanningSubgraph_contraction`). -/
theorem isMinorClosed_of_atomic (hd : IsEdgeDeletionClosed 𝓕) (hv : IsVertexDeletionClosed 𝓕)
    (hc : IsEdgeContractionClosed 𝓕) : IsMinorClosed 𝓕 := by
  intro V W _ _ F K hKF hF
  obtain ⟨s, t, L, hL, he⟩ := isMinor_iff_exists_induce_spanningSubgraph_contraction.1 hKF
  exact hc hL (hd.mem_spanningSubgraph _ t (hv F s hF)) K he

/-- **Minor-closedness from single-edge contraction.**  Closure under deleting edges and
vertices and under contracting a *single* edge already implies minor-closedness.

The proof is by induction on the number of vertices.  Given a minor model of `K` in `F`, either
every branch set is a singleton — and then `K` is a spanning subgraph of an induced subgraph
(`SimpleGraph.MinorModel.exists_iso_of_forall_subsingleton`) — or some branch set contains two
vertices, hence an edge of `F`, which may be contracted: pushing the model forward
(`SimpleGraph.MinorModel.contractEdge`) leaves a minor model over one vertex fewer. -/
theorem isMinorClosed_of_atomic_single (hd : IsEdgeDeletionClosed 𝓕)
    (hv : IsVertexDeletionClosed 𝓕) (hc : IsSingleEdgeContractionClosed 𝓕) :
    IsMinorClosed 𝓕 := by
  classical
  have hsubcase : ∀ {V W : Type} [Finite V] [Finite W] {F : SimpleGraph V} {K : SimpleGraph W}
      (C : MinorModel K F), (∀ w, (C.branchSet w).Subsingleton) → 𝓕.Mem F → 𝓕.Mem K := by
    intro V W _ _ F K C hsub hF
    obtain ⟨s, t, ⟨e⟩⟩ := (MinorModel.exists_iso_of_forall_subsingleton C) hsub
    rw [(GraphClass.Mem_congr 𝓕) e]
    exact hd.mem_spanningSubgraph _ t (hv F s hF)
  have key : ∀ (n : ℕ) {V W : Type} [Finite V] [Finite W] (F : SimpleGraph V)
      (K : SimpleGraph W), Nat.card V ≤ n → IsMinor K F → 𝓕.Mem F → 𝓕.Mem K := by
    intro n
    induction n with
    | zero =>
      intro V W _ _ F K hn hKF hF
      obtain ⟨C⟩ := hKF
      haveI : IsEmpty V := not_nonempty_iff.1 fun hne =>
        absurd (Nat.card_pos_iff.2 ⟨hne, ‹Finite V›⟩) (by omega)
      exact hsubcase C (fun _ x _ _ _ => isEmptyElim x) hF
    | succ n ih =>
      intro V W _ _ F K hn hKF hF
      obtain ⟨C⟩ := hKF
      by_cases hsub : ∀ w : W, (C.branchSet w).Subsingleton
      · exact hsubcase C hsub hF
      · -- Some branch set has two vertices, hence contains an edge of `F`.
        obtain ⟨w₀, hw₀⟩ := not_forall.1 hsub
        obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.1 hw₀
        obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := exists_adj_of_connected_of_ne (C.connected w₀)
          (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) fun hc => hxy (congrArg Subtype.val hc)
        have hab' : F.Adj a b := hab
        have hF' : 𝓕.Mem ((contractEdge F) a b) :=
          hc hab' hF ((contractEdge F) a b) ⟨RelIso.refl _⟩
        refine ih ((contractEdge F) a b) K ?_ ⟨MinorModel.contractEdge C hab' ha hb⟩ hF'
        have hcard := card_contractionQuotient_singleton hab'
        have hpos : 0 < Nat.card V := Nat.card_pos_iff.2 ⟨⟨a⟩, ‹Finite V›⟩
        omega
  intro V W _ _ F K hKF hF
  exact key (Nat.card V) F K le_rfl hKF hF

theorem IsMinorClosed.isEdgeDeletionClosed (h : IsMinorClosed 𝓕) : IsEdgeDeletionClosed 𝓕 :=
  fun F s hF => h _ (isMinor_deleteEdges F s) hF

theorem IsMinorClosed.isVertexDeletionClosed (h : IsMinorClosed 𝓕) : IsVertexDeletionClosed 𝓕 :=
  fun F s hF => h _ (isMinor_induce F s) hF

theorem IsMinorClosed.isEdgeContractionClosed (h : IsMinorClosed 𝓕) :
    IsEdgeContractionClosed 𝓕 := by
  intro V _ F L hL hF W _ K he
  exact h K (isMinor_of_iso_contractionQuotient hL he.some) hF

theorem IsMinorClosed.isSubgraphClosed (h : IsMinorClosed 𝓕) : IsSubgraphClosed 𝓕 :=
  ⟨(GraphClass.IsMinorClosed.isEdgeDeletionClosed h), (GraphClass.IsMinorClosed.isVertexDeletionClosed h)⟩

/-! ### Summands -/

/-- If `𝓕` is closed under taking summands then it contains every union of a subfamily of the
connected components of any of its members. -/
theorem IsSummandClosed.mem_sigmaOn_connectedComponent (h : IsSummandClosed 𝓕) {α : Type}
    [Finite α] {F : SimpleGraph α} (hF : 𝓕.Mem F) (s : Set F.ConnectedComponent) :
    𝓕.Mem (sigmaOn s fun c : F.ConnectedComponent => c.toSimpleGraph) :=
  (h _ _ (((GraphClass.Mem_congr 𝓕)
    ((Iso.sigmaConnectedComponent F).symm.trans (Iso.sigmaSplit s _))).1 hF)).1

end GraphClass

end SimpleGraph

end Lax871432Proofs
