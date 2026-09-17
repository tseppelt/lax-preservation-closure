/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Lax871432Proofs.GraphTheory.LoopGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.SetTheory.Cardinal.Finite
import Lax68.GraphMinors

/-!
# Spanning subgraphs and contraction quotients

This file defines what it means for one graph to be a *minor* of another, and provides the two
constructions out of which the minors appearing in `Hom/Complement.lean` are built.

* `SimpleGraph.spanningSubgraph F s` keeps the vertices of `F` and only those edges lying in
  `s`.  These are exactly the subgraphs `F' ⊆ F` with `V(F') = V(F)` indexed in equation
  (5.23).
* `SimpleGraph.contractionQuotient F L`, written `F ⊘ L`, contracts the edges in `L`: its
  vertices are the connected components of the graph `(V(F), L)` and `[v]` is adjacent to `[w]`
  when some edge of `E(F) \ L` joins the two classes.

Contracting *may create loops* — if `x` and `y` lie in one class but `xy ∉ L` then `[x]` gets
a loop — which is why `F ⊘ L` is a `LoopGraph` and not a `SimpleGraph`.  This is harmless for
the counting identities: by `LoopGraph.homCount_eq_zero_of_not_isLoopless` the terms with a
loop contribute nothing.

Both constructions are indexed by *sets* of unordered pairs, while the sums in
`Hom/Complement.lean` range over *finite subsets of `F.edgeSet`*; `SimpleGraph.edgeSetOf`
mediates between the two.

A minor is described by a *model*: a family of pairwise disjoint connected *branch sets* in
`F`, one per vertex of `K`, joined by edges of `F` whenever the corresponding vertices of `K`
are adjacent.  This is the standard formulation and is equivalent to obtaining `K` from `F` by
deleting vertices and edges and contracting edges; see
`SimpleGraph.isMinor_iff_exists_induce_spanningSubgraph_contraction`.

## Main declarations

* `SimpleGraph.MinorModel`, `SimpleGraph.IsMinor`: minors.
* `SimpleGraph.spanningSubgraph`: the spanning subgraph with a prescribed edge set.
* `SimpleGraph.edgeSetOf`: a `Finset F.edgeSet` viewed as a set of unordered pairs.
* `SimpleGraph.contractionQuotient`, `F ⊘ L`: the contraction quotient.
* `SimpleGraph.isMinor_iff_exists_induce_spanningSubgraph_contraction`: a minor is exactly what
  the three atomic operations produce.
* `SimpleGraph.contractEdge`: the simple graph obtained by contracting a single edge.
* `SimpleGraph.MinorModel.contractEdge`: a minor model survives the contraction of an edge
  lying inside one of its branch sets.
* `SimpleGraph.MinorModel.exists_iso_of_forall_subsingleton`: a model with singleton branch
  sets needs no contraction at all.

## Notation

* `F ⊘ L`: the contraction quotient of `F` by the edge set `L`.
-/

namespace Lax871432Proofs

open _root_.SimpleGraph
open Lax68.GraphMinors

open Function

namespace SimpleGraph

variable {V W : Type*}

/-! ### Spanning subgraphs -/

/-- The spanning subgraph of `F` whose edges are those of `F` lying in `s`.  It has the same
vertex type as `F`. -/
def spanningSubgraph (F : SimpleGraph V) (s : Set (Sym2 V)) : SimpleGraph V where
  Adj u v := F.Adj u v ∧ s(u, v) ∈ s
  symm := ⟨fun _ _ h => ⟨h.1.symm, Sym2.eq_swap ▸ h.2⟩⟩
  loopless := ⟨fun _ h => F.irrefl h.1⟩

@[simp]
theorem spanningSubgraph_adj (F : SimpleGraph V) (s : Set (Sym2 V)) (u v : V) :
    ((spanningSubgraph F) s).Adj u v ↔ F.Adj u v ∧ s(u, v) ∈ s := Iff.rfl

/-- The set of unordered pairs selected by a finite set of edges of `F`. -/
def edgeSetOf (F : SimpleGraph V) (s : Finset F.edgeSet) : Set (Sym2 V) :=
  Subtype.val '' (s : Set F.edgeSet)

/-! ### Contraction quotients -/

/-- The *contraction quotient* `F ⊘ L`: its vertices are the connected components of the graph
on `V(F)` with edge set `L`, and `[v]` is adjacent to `[w]` when some edge of `E(F) \ L` joins
a vertex of `[v]` to a vertex of `[w]`.

The result may have loops, so it is a `LoopGraph`. -/
def contractionQuotient (F : SimpleGraph V) (L : Set (Sym2 V)) :
    LoopGraph (fromEdgeSet L).ConnectedComponent where
  Adj c d := ∃ x y, F.Adj x y ∧ s(x, y) ∉ L ∧
    (fromEdgeSet L).connectedComponentMk x = c ∧ (fromEdgeSet L).connectedComponentMk y = d
  symm := ⟨fun _ _ ⟨x, y, hxy, hL, hx, hy⟩ =>
    ⟨y, x, hxy.symm, Sym2.eq_swap ▸ hL, hy, hx⟩⟩

@[inherit_doc] scoped notation:70 F:70 " ⊘ " L:71 => SimpleGraph.contractionQuotient F L

@[simp]
theorem contractionQuotient_adj (F : SimpleGraph V) (L : Set (Sym2 V))
    {c d : (fromEdgeSet L).ConnectedComponent} :
    (F ⊘ L).Adj c d ↔ ∃ x y, F.Adj x y ∧ s(x, y) ∉ L ∧
      (fromEdgeSet L).connectedComponentMk x = c ∧
      (fromEdgeSet L).connectedComponentMk y = d := Iff.rfl

/-! ### Minors -/

/-! Minor models and the minor relation are the concept `Lax68.GraphMinors`. -/

end SimpleGraph

namespace SimpleGraph

open scoped LoopGraph

variable {V W : Type*} {F : SimpleGraph V}

/-! ### Spanning subgraphs -/

theorem spanningSubgraph_le (F : SimpleGraph V) (s : Set (Sym2 V)) :
    (spanningSubgraph F) s ≤ F := fun _ _ h => h.1

@[simp]
theorem spanningSubgraph_univ (F : SimpleGraph V) : (spanningSubgraph F) Set.univ = F := by
  ext u v; simp

@[simp]
theorem spanningSubgraph_empty (F : SimpleGraph V) : (spanningSubgraph F) ∅ = ⊥ := by
  ext u v; simp

theorem edgeSet_spanningSubgraph (F : SimpleGraph V) (s : Set (Sym2 V)) :
    ((spanningSubgraph F) s).edgeSet = F.edgeSet ∩ s := by
  ext e
  induction e using Sym2.ind with
  | h u v => simp [mem_edgeSet]

/-- The pairs selected by a subset of the edges of `F` are edges of `F`. -/
theorem edgeSetOf_subset_edgeSet (F : SimpleGraph V) (s : Finset F.edgeSet) :
    (edgeSetOf F) s ⊆ F.edgeSet := by
  rintro _ ⟨e, -, rfl⟩; exact e.2

/-- The pairs selected by a finite set of edges are as many as those edges. -/
theorem card_edgeSetOf (F : SimpleGraph V) (s : Finset F.edgeSet) :
    Nat.card ((edgeSetOf F) s) = s.card := by
  rw [edgeSetOf, ← Nat.card_eq_finsetCard, ← Finset.coe_sort_coe]
  exact Nat.card_congr (Equiv.Set.image (Subtype.val : F.edgeSet → Sym2 V)
    (↑s : Set F.edgeSet) Subtype.val_injective).symm

/-- The number of edges of a spanning subgraph is the size of the selecting set. -/
theorem card_edgeSet_spanningSubgraph (F : SimpleGraph V) (s : Finset F.edgeSet) :
    Nat.card ((spanningSubgraph F) ((edgeSetOf F) s)).edgeSet = s.card := by
  have hsub : F.edgeSet ∩ (edgeSetOf F) s = (edgeSetOf F) s :=
    Set.inter_eq_right.2 (edgeSetOf_subset_edgeSet F s)
  rw [edgeSet_spanningSubgraph, hsub, card_edgeSetOf]

/-- Keeping the edges in `s` is the same as deleting the edges outside `s`. -/
theorem spanningSubgraph_eq_deleteEdges (F : SimpleGraph V) (s : Set (Sym2 V)) :
    (spanningSubgraph F) s = F.deleteEdges sᶜ := by
  ext u v; simp [deleteEdges_adj]

/-- Deleting a single edge is the spanning subgraph on the complement of that edge. -/
theorem deleteEdges_singleton (F : SimpleGraph V) (e : Sym2 V) :
    F.deleteEdges {e} = (spanningSubgraph F) {e}ᶜ := by
  rw [spanningSubgraph_eq_deleteEdges, compl_compl]

/-- The pairs selected by `L` are edges of the spanning subgraph selected by any larger `s`.
This is the hypothesis needed to contract `L` inside `F_s`. -/
theorem edgeSetOf_subset_edgeSet_spanningSubgraph (F : SimpleGraph V) {s L : Finset F.edgeSet}
    (hL : L ⊆ s) :
    (edgeSetOf F) L ⊆ ((spanningSubgraph F) ((edgeSetOf F) s)).edgeSet := by
  rw [edgeSet_spanningSubgraph]
  rintro _ ⟨e, he, rfl⟩
  exact ⟨e.2, ⟨e, hL he, rfl⟩⟩

/-! ### Contraction quotients -/

/-- Reachability in a graph with a single edge: two vertices are reachable exactly when they
are equal or form that edge. -/
theorem reachable_fromEdgeSet_singleton {u v x y : V}
    (h : (fromEdgeSet ({s(u, v)} : Set (Sym2 V))).Reachable x y) :
    x = y ∨ s(x, y) = s(u, v) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Or.inl rfl
  | @cons a b c hab _ ih =>
    rw [fromEdgeSet_adj] at hab
    obtain ⟨hab1, hab2⟩ := hab
    rw [Set.mem_singleton_iff] at hab1
    rcases ih with rfl | hbc
    · exact Or.inr hab1
    · rcases Sym2.eq_iff.1 (hab1.trans hbc.symm) with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 hab2
      · exact Or.inl h1

/-- Contracting no edges changes nothing. -/
theorem nonempty_iso_contractionQuotient_empty (F : SimpleGraph V) :
    Nonempty (F ⊘ (∅ : Set (Sym2 V)) ≃lg (toLoopGraph F)) := by
  have hre : ∀ {x y : V}, (fromEdgeSet (∅ : Set (Sym2 V))).Reachable x y → x = y := by
    intro x y h; rw [fromEdgeSet_empty] at h; exact reachable_bot.1 h
  refine ⟨{
    toEquiv :=
      { toFun := ConnectedComponent.lift id fun _ _ p _ => hre ⟨p⟩
        invFun := connectedComponentMk _
        left_inv := by rintro ⟨x⟩; rfl
        right_inv := fun _ => rfl }
    map_rel_iff' := ?_ }⟩
  rintro ⟨x⟩ ⟨y⟩
  refine ⟨fun hadj => ⟨x, y, hadj, Set.notMem_empty _, rfl, rfl⟩, ?_⟩
  rintro ⟨a, b, hab, -, ha, hb⟩
  rw [← hre (ConnectedComponent.eq.1 ha), ← hre (ConnectedComponent.eq.1 hb)]
  exact hab

/-- Contracting nothing creates no loop. -/
theorem contractionQuotient_empty_isLoopless (F : SimpleGraph V) :
    (F ⊘ (∅ : Set (Sym2 V))).IsLoopless := by
  rintro c ⟨x, y, hxy, -, hx, hy⟩
  refine hxy.ne ?_
  have hr := ConnectedComponent.eq.1 (hx.trans hy.symm)
  rw [fromEdgeSet_empty] at hr
  exact reachable_bot.1 hr

/-- Contracting a single edge of a simple graph never creates a loop: the only edge of `F`
inside the contracted class is the contracted edge itself, and it is not an edge of the
quotient. -/
theorem contractionQuotient_singleton_isLoopless (u v : V) :
    (F ⊘ ({s(u, v)} : Set (Sym2 V))).IsLoopless := by
  rintro c ⟨x, y, hxy, hL, hx, hy⟩
  rcases reachable_fromEdgeSet_singleton (ConnectedComponent.eq.1 (hx.trans hy.symm)) with
    rfl | he
  · exact hxy.ne rfl
  · exact hL he

/-- Contracting a single edge removes exactly one vertex. -/
theorem card_contractionQuotient_singleton [Finite V] {u v : V} (h : F.Adj u v) :
    Nat.card (fromEdgeSet ({s(u, v)} : Set (Sym2 V))).ConnectedComponent = Nat.card V - 1 := by
  classical
  haveI := Fintype.ofFinite V
  have huv : u ≠ v := h.ne
  have hadj : (fromEdgeSet ({s(u, v)} : Set (Sym2 V))).Adj u v := by
    rw [fromEdgeSet_adj]; exact ⟨rfl, huv⟩
  -- Collapse `v` onto `u`; this is constant on the components of `fromEdgeSet {s(u, v)}`.
  set f : V → {w : V // w ≠ v} := fun w => if hw : w = v then ⟨u, huv⟩ else ⟨w, hw⟩ with hfdef
  have hfv : f v = ⟨u, huv⟩ := by simp [hfdef]
  have hfne : ∀ {w : V} (hw : w ≠ v), f w = ⟨w, hw⟩ := fun hw => by simp [hfdef, hw]
  have hconst : ∀ x y : V, (fromEdgeSet ({s(u, v)} : Set (Sym2 V))).Reachable x y → f x = f y := by
    intro x y hr
    rcases reachable_fromEdgeSet_singleton hr with rfl | he
    · rfl
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hfne huv, hfv]
      · rw [hfne huv, hfv]
  have hcard : Nat.card (fromEdgeSet ({s(u, v)} : Set (Sym2 V))).ConnectedComponent =
      Nat.card {w : V // w ≠ v} := by
    refine Nat.card_congr
      { toFun := ConnectedComponent.lift f fun x y p _ => hconst x y ⟨p⟩
        invFun := fun w => connectedComponentMk _ w.1
        left_inv := ?_
        right_inv := ?_ }
    · rintro ⟨x⟩
      by_cases hx : x = v
      · subst hx
        change connectedComponentMk _ (f x).1 = _
        rw [hfv]
        exact ConnectedComponent.eq.2 hadj.reachable
      · change connectedComponentMk _ (f x).1 = _
        rw [hfne hx]
        rfl
    · intro w
      change f w.1 = w
      rw [hfne w.2]
  rw [hcard]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

/-- Two vertices lie in the same class of the contraction of a single edge exactly when they
are equal or form that edge. -/
theorem connectedComponentMk_eq_iff {u v : V} (huv : u ≠ v) {x y : V} :
    (fromEdgeSet ({s(u, v)} : Set (Sym2 V))).connectedComponentMk x =
        (fromEdgeSet ({s(u, v)} : Set (Sym2 V))).connectedComponentMk y ↔
      x = y ∨ s(x, y) = s(u, v) := by
  refine ⟨fun hc => reachable_fromEdgeSet_singleton (ConnectedComponent.eq.1 hc), ?_⟩
  rintro (rfl | he)
  · rfl
  · refine ConnectedComponent.eq.2 (Adj.reachable ?_)
    rw [fromEdgeSet_adj]
    refine ⟨he, fun hxy => ?_⟩
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact huv (hxy ▸ rfl)

/-- The image in the contraction of an edge of `F` that is not contracted is an edge of the
contraction. -/
theorem map_mem_edgeSet_contractionQuotient_of_notMem {L : Set (Sym2 V)} {e : Sym2 V}
    (he : e ∈ F.edgeSet) (hne : e ∉ L) :
    Sym2.map (fromEdgeSet L).connectedComponentMk e ∈ (F ⊘ L).edgeSet := by
  induction e using Sym2.ind with
  | h x y =>
    rw [mem_edgeSet] at he
    rw [Sym2.map_mk, LoopGraph.edgeSet, Sym2.fromRel_prop]
    exact ⟨x, y, he, hne, rfl, rfl⟩

/-- The image in the contraction of an edge of `F` other than the contracted one is an edge of
the contraction. -/
theorem map_mem_edgeSet_contractionQuotient {u v : V} {e : Sym2 V} (he : e ∈ F.edgeSet)
    (hne : e ≠ s(u, v)) :
    Sym2.map (fromEdgeSet ({s(u, v)} : Set (Sym2 V))).connectedComponentMk e ∈
      (F ⊘ ({s(u, v)} : Set (Sym2 V))).edgeSet :=
  map_mem_edgeSet_contractionQuotient_of_notMem he hne

/-- Contracting `L` maps the edges of `F` outside `L` to the edges of the quotient. -/
noncomputable def contractMap (F : SimpleGraph V) (L : Set (Sym2 V)) :
    {e : F.edgeSet // (e : Sym2 V) ∉ L} → (F ⊘ L).edgeSet := fun e =>
  ⟨Sym2.map _ e.1.1, map_mem_edgeSet_contractionQuotient_of_notMem e.1.2 e.2⟩

theorem contractMap_surjective (F : SimpleGraph V) (L : Set (Sym2 V)) :
    Function.Surjective (contractMap F L) := by
  rintro ⟨f, hf⟩
  induction f using Sym2.ind with
  | h c d =>
    rw [LoopGraph.edgeSet, Sym2.fromRel_prop] at hf
    obtain ⟨x, y, hxy, hL, hx, hy⟩ := hf
    exact ⟨⟨⟨s(x, y), hxy⟩, hL⟩,
      Subtype.ext (by simp [contractMap, Sym2.map_mk, hx, hy])⟩

/-- **Contracting `L` removes at least `|L|` edges**: the edges of `F` outside `L` cover those
of the quotient.  This is the general form of `obs:edges-contract` used to pin down the
summation indices of `eq:del-contr` producing a given contraction. -/
theorem card_edgeSet_contractionQuotient_add_card_le [Finite V] (F : SimpleGraph V)
    {L : Set (Sym2 V)} (hL : L ⊆ F.edgeSet) :
    Nat.card (F ⊘ L).edgeSet + Nat.card L ≤ Nat.card F.edgeSet := by
  classical
  haveI : Fintype F.edgeSet := Fintype.ofFinite _
  haveI : Fintype ↥L := Fintype.ofFinite _
  have h1 : Nat.card (F ⊘ L).edgeSet ≤ Nat.card {e : F.edgeSet // (e : Sym2 V) ∉ L} :=
    Nat.card_le_card_of_surjective _ (contractMap_surjective F L)
  have h2 : Nat.card {e : F.edgeSet // (e : Sym2 V) ∈ L} = Nat.card L :=
    Nat.card_congr
      { toFun x := ⟨x.1.1, x.2⟩
        invFun x := ⟨⟨x.1, hL x.2⟩, x.2⟩
        left_inv _ := rfl
        right_inv _ := rfl }
  haveI : Fintype {e : F.edgeSet // (e : Sym2 V) ∈ L} := Fintype.ofFinite _
  have h3 : Nat.card {e : F.edgeSet // (e : Sym2 V) ∉ L} =
      Nat.card F.edgeSet - Nat.card {e : F.edgeSet // (e : Sym2 V) ∈ L} := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have h4 : Nat.card {e : F.edgeSet // (e : Sym2 V) ∈ L} ≤ Nat.card F.edgeSet := by
    simp only [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  omega

/-- Contracting `uv` maps the edges of `F` other than `uv` to the edges of the quotient. -/
noncomputable def contractEdgeMap (F : SimpleGraph V) {u v : V} (h : F.Adj u v) :
    {e : F.edgeSet // e ≠ ⟨s(u, v), h⟩} → (F ⊘ ({s(u, v)} : Set (Sym2 V))).edgeSet := fun e =>
  ⟨Sym2.map _ e.1.1,
    map_mem_edgeSet_contractionQuotient e.1.2 fun hc => e.2 (Subtype.ext hc)⟩

theorem contractEdgeMap_surjective [Finite V] {u v : V} (h : F.Adj u v) :
    Function.Surjective (contractEdgeMap F h) := by
  rintro ⟨f, hf⟩
  induction f using Sym2.ind with
  | h c d =>
    rw [LoopGraph.edgeSet, Sym2.fromRel_prop] at hf
    obtain ⟨x, y, hxy, hL, hx, hy⟩ := hf
    refine ⟨⟨⟨s(x, y), hxy⟩, fun hc => hL (congrArg Subtype.val hc)⟩, ?_⟩
    exact Subtype.ext (by simp [contractEdgeMap, Sym2.map_mk, hx, hy])

/-- Removing one element of a finite type. -/
private theorem card_ne_add_one {α : Type*} [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} + 1 = Nat.card α := by
  classical
  haveI := Fintype.ofFinite α
  have h1 : Nat.card {x : α // x ≠ a} = Nat.card α - 1 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have h2 : 0 < Nat.card α := Nat.card_pos_iff.2 ⟨⟨a⟩, inferInstance⟩
  omega

/-- The number of edges of `F` other than `uv`. -/
private theorem card_edgeSet_sub_one [Finite V] {u v : V} (h : F.Adj u v) :
    Nat.card {e : F.edgeSet // e ≠ ⟨s(u, v), h⟩} + 1 = Nat.card F.edgeSet :=
  card_ne_add_one _

/-- Deleting an edge removes exactly one edge. -/
theorem card_edgeSet_deleteEdges_singleton_add_one [Finite V] {e : Sym2 V} (he : e ∈ F.edgeSet) :
    Nat.card (F.deleteEdges {e}).edgeSet + 1 = Nat.card F.edgeSet := by
  rw [← card_ne_add_one (⟨e, he⟩ : F.edgeSet)]
  congr 1
  rw [edgeSet_deleteEdges]
  exact Nat.card_congr
    { toFun x := ⟨⟨x.1, x.2.1⟩, fun hc => x.2.2 (congrArg Subtype.val hc)⟩
      invFun x := ⟨x.1.1, x.1.2, fun hc => x.2 (Subtype.ext hc)⟩
      left_inv _ := rfl
      right_inv _ := rfl }

/-- Contracting edges never increases the number of vertices. -/
theorem card_connectedComponent_le [Finite V] (L : Set (Sym2 V)) :
    Nat.card (fromEdgeSet L).ConnectedComponent ≤ Nat.card V :=
  Nat.card_le_card_of_surjective _ (ConnectedComponent.ind fun v => ⟨v, rfl⟩)

/-- Contracting a nonempty set of edges strictly decreases the number of vertices. -/
theorem card_connectedComponent_lt [Finite V] {L : Set (Sym2 V)} {x y : V} (hne : x ≠ y)
    (hxy : s(x, y) ∈ L) :
    Nat.card (fromEdgeSet L).ConnectedComponent < Nat.card V := by
  have hsurj : Function.Surjective (fromEdgeSet L).connectedComponentMk :=
    ConnectedComponent.ind fun v => ⟨v, rfl⟩
  rcases lt_or_eq_of_le (Nat.card_le_card_of_surjective _ hsurj) with hlt | heq
  · exact hlt
  · refine absurd ((Nat.bijective_iff_surjective_and_card _).2 ⟨hsurj, heq.symm⟩).1 ?_
    intro hinj
    exact hne (hinj (ConnectedComponent.eq.2
      (Adj.reachable ((fromEdgeSet_adj ..).2 ⟨hxy, hne⟩))))

/-- Contracting the edge `uv` maps the remaining edges of `F` *onto* the edges of the
quotient, so the quotient has at least one edge fewer.  Equality holds exactly when no vertex
forms a triangle with `uv`; see
`SimpleGraph.card_edgeSet_contractionQuotient_singleton_of_isEmpty`.

This is the half of `obs:edges-contract` used in the proof of `thm:complement`. -/
theorem card_edgeSet_contractionQuotient_singleton_le [Finite V] {u v : V} (h : F.Adj u v) :
    Nat.card (F ⊘ ({s(u, v)} : Set (Sym2 V))).edgeSet + 1 ≤ Nat.card F.edgeSet := by
  have hle := Nat.card_le_card_of_surjective _ (contractEdgeMap_surjective h)
  have := card_edgeSet_sub_one h
  omega

/-- If no vertex forms a triangle with `uv` then distinct edges of `F` other than `uv` stay
distinct after contracting `uv`: two edges could only be identified by collapsing `u` with `v`,
which needs a common neighbour. -/
theorem contractEdgeMap_injective [Finite V] {u v : V} (h : F.Adj u v)
    (htri : IsEmpty {w : V // F.Adj u w ∧ F.Adj v w}) :
    Function.Injective (contractEdgeMap F h) := by
  have hΔ : ∀ w : V, F.Adj u w → F.Adj v w → False := fun w h1 h2 => htri.false ⟨w, h1, h2⟩
  -- A vertex adjacent to both endpoints of a collapsed pair would form a triangle.
  have hcontra : ∀ {a b b' : V}, F.Adj a b → F.Adj a b' → s(b, b') = s(u, v) → False := by
    intro a b b' hab hab' hbb'
    rcases Sym2.eq_iff.1 hbb' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hΔ a hab.symm hab'.symm
    · exact hΔ a hab'.symm hab.symm
  -- If both endpoints collapse then the edge was `uv` itself.
  have hboth : ∀ {x y x' y' : V}, F.Adj x y → s(x, x') = s(u, v) → s(y, y') = s(u, v) →
      s(x, y) = s(u, v) := by
    intro x y x' y' hxy hxx' hyy'
    rcases Sym2.eq_iff.1 hxx' with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      rcases Sym2.eq_iff.1 hyy' with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact absurd hxy F.irrefl
    · rfl
    · exact Sym2.eq_swap
    · exact absurd hxy F.irrefl
  rintro ⟨⟨e, he⟩, hne⟩ ⟨⟨e', he'⟩, hne'⟩ hmap
  have hne₁ : e ≠ s(u, v) := fun hc => hne (Subtype.ext hc)
  have hne₂ : e' ≠ s(u, v) := fun hc => hne' (Subtype.ext hc)
  have hmap' : Sym2.map (fromEdgeSet ({s(u, v)} : Set (Sym2 V))).connectedComponentMk e =
      Sym2.map (fromEdgeSet ({s(u, v)} : Set (Sym2 V))).connectedComponentMk e' :=
    congrArg Subtype.val hmap
  refine Subtype.ext (Subtype.ext ?_)
  induction e using Sym2.ind with
  | h x y =>
  induction e' using Sym2.ind with
  | h x' y' =>
  rw [mem_edgeSet] at he he'
  rw [Sym2.map_mk, Sym2.map_mk] at hmap'
  have hpi : ∀ {a b : V},
      (fromEdgeSet ({s(u, v)} : Set (Sym2 V))).connectedComponentMk a =
        (fromEdgeSet ({s(u, v)} : Set (Sym2 V))).connectedComponentMk b →
      a = b ∨ s(a, b) = s(u, v) := fun hc => (connectedComponentMk_eq_iff h.ne).1 hc
  rcases Sym2.eq_iff.1 hmap' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases hpi h1 with rfl | hxx' <;> rcases hpi h2 with rfl | hyy'
    · rfl
    · exact absurd hyy' fun hc => hcontra he he' hc
    · exact absurd hxx' fun hc => hcontra he.symm he'.symm hc
    · exact absurd (hboth he hxx' hyy') hne₁
  · rcases hpi h1 with rfl | hxy' <;> rcases hpi h2 with rfl | hyx'
    · exact Sym2.eq_swap
    · exact absurd hyx' fun hc => hcontra he he'.symm hc
    · exact absurd hxy' fun hc => hcontra he.symm he' hc
    · exact absurd (hboth he hxy' hyx') hne₁

/-- The edges joining `u` to a vertex forming a triangle with `uv`. -/
def triangleEdges (F : SimpleGraph V) (u v : V) : Set (Sym2 V) :=
  {f | ∃ w, F.Adj u w ∧ F.Adj v w ∧ f = s(u, w)}

/-- Deleting the edges of `SimpleGraph.triangleEdges` leaves the contraction of `uv`
unchanged: a deleted edge `uw` and the surviving edge `vw` have the same image, because `u`
and `v` are identified. -/
theorem contractionQuotient_deleteEdges_triangleEdges {u v : V} (huv : F.Adj u v) :
    (F.deleteEdges (F.triangleEdges u v)) ⊘ ({s(u, v)} : Set (Sym2 V)) =
      F ⊘ ({s(u, v)} : Set (Sym2 V)) := by
  have huv' : (fromEdgeSet ({s(u, v)} : Set (Sym2 V))).connectedComponentMk u =
      (fromEdgeSet ({s(u, v)} : Set (Sym2 V))).connectedComponentMk v :=
    (connectedComponentMk_eq_iff huv.ne).2 (Or.inr rfl)
  ext c d
  refine ⟨fun ⟨x, y, hxy, hL, hx, hy⟩ => ⟨x, y, ((deleteEdges_adj ..).1 hxy).1, hL, hx, hy⟩, ?_⟩
  rintro ⟨x, y, hxy, hL, hx, hy⟩
  rcases Classical.em (s(x, y) ∈ F.triangleEdges u v) with hT | hT
  swap
  · exact ⟨x, y, (deleteEdges_adj ..).2 ⟨hxy, hT⟩, hL, hx, hy⟩
  obtain ⟨w, huw, hvw, hf⟩ := hT
  have hnotT : s(v, w) ∉ F.triangleEdges u v := by
    rintro ⟨w', -, hv', hw'⟩
    rcases Sym2.eq_iff.1 hw' with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact huv.ne h1.symm
    · exact hv'.ne h1
  have hnotL : s(v, w) ∉ ({s(u, v)} : Set (Sym2 V)) := by
    rw [Set.mem_singleton_iff]
    intro hc
    rcases Sym2.eq_iff.1 hc with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact huv.ne h1.symm
    · exact huw.ne h2.symm
  have hadj : (F.deleteEdges (F.triangleEdges u v)).Adj v w :=
    (deleteEdges_adj ..).2 ⟨hvw, hnotT⟩
  rcases Sym2.eq_iff.1 hf with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨v, w, hadj, hnotL, ?_, ?_⟩
    · rw [h1] at hx; rw [← huv']; exact hx
    · rw [h2] at hy; exact hy
  · refine ⟨w, v, hadj.symm, ?_, ?_, ?_⟩
    · rw [Set.mem_singleton_iff] at hnotL ⊢
      rw [Sym2.eq_swap]
      exact hnotL
    · rw [h1] at hx; exact hx
    · rw [h2] at hy; rw [← huv']; exact hy

/-- After deleting `SimpleGraph.triangleEdges`, no vertex forms a triangle with `uv`. -/
theorem isEmpty_triangle_deleteEdges (F : SimpleGraph V) (u v : V) :
    IsEmpty {w : V // (F.deleteEdges (F.triangleEdges u v)).Adj u w ∧
      (F.deleteEdges (F.triangleEdges u v)).Adj v w} := by
  refine ⟨fun x => ?_⟩
  obtain ⟨w, huw, hvw⟩ := x
  exact ((deleteEdges_adj ..).1 huw).2
    ⟨w, ((deleteEdges_adj ..).1 huw).1, ((deleteEdges_adj ..).1 hvw).1, rfl⟩

/-- The contracted edge itself is not a triangle edge, so it survives the deletion. -/
theorem adj_deleteEdges_triangleEdges {u v : V} (huv : F.Adj u v) :
    (F.deleteEdges (F.triangleEdges u v)).Adj u v := by
  refine (deleteEdges_adj ..).2 ⟨huv, ?_⟩
  rintro ⟨w, -, hv', hf⟩
  rcases Sym2.eq_iff.1 hf with ⟨-, h2⟩ | ⟨-, h2⟩
  · exact hv'.ne h2
  · exact huv.ne h2.symm

/-- If no vertex forms a triangle with `uv` then contracting `uv` removes exactly one edge.
This is the situation the proof of `thm:complement` reduces to by first deleting edges. -/
theorem card_edgeSet_contractionQuotient_singleton_of_isEmpty [Finite V] {u v : V}
    (h : F.Adj u v) (htri : IsEmpty {w : V // F.Adj u w ∧ F.Adj v w}) :
    Nat.card (F ⊘ ({s(u, v)} : Set (Sym2 V))).edgeSet = Nat.card F.edgeSet - 1 := by
  have hb := Nat.card_eq_of_bijective _
    ⟨contractEdgeMap_injective h htri, contractEdgeMap_surjective h⟩
  have := card_edgeSet_sub_one h
  omega

/-! ### Minors -/

/-- A one-vertex induced subgraph is connected. -/
theorem connected_induce_singleton (F : SimpleGraph V) (x : V) :
    (F.induce {x}).Connected := by
  haveI : Nonempty ({x} : Set V) := ⟨⟨x, rfl⟩⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have hab : (⟨a, ha⟩ : ({x} : Set V)) = ⟨b, hb⟩ := Subtype.ext (ha.trans hb.symm)
  rw [hab]

/-- The minor model with singleton branch sets, available whenever `K` has the same vertices
as `F` and fewer edges. -/
def MinorModel.ofLE {K : SimpleGraph V} (h : K ≤ F) : MinorModel K F where
  branchSet v := {v}
  connected v := connected_induce_singleton F v
  disjoint _ _ hvw := Set.disjoint_singleton.2 hvw
  adjacent _ _ hvw := ⟨_, rfl, _, rfl, h hvw⟩

@[refl]
theorem IsMinor.refl (F : SimpleGraph V) : IsMinor F F := ⟨MinorModel.ofLE le_rfl⟩

/-- The inclusion of one induced subgraph into a larger one. -/
private def inclHom {A B : Set V} (h : A ⊆ B) : F.induce A →g F.induce B where
  toFun := Set.inclusion h
  map_rel' := id

/-- The union of the branch sets of a minor model over a *connected* set of indices is
connected: within one branch set connectivity is given, and adjacent indices have their branch
sets joined by an edge. -/
private theorem connected_biUnion_branch {K : SimpleGraph W} (C : MinorModel K F) (T : Set W)
    (hT : (K.induce T).Connected) : (F.induce (⋃ k ∈ T, C.branchSet k)).Connected := by
  set S : Set V := ⋃ k ∈ T, C.branchSet k with hSdef
  have hsub : ∀ {k : W}, k ∈ T → C.branchSet k ⊆ S := fun hk => Set.subset_biUnion_of_mem hk
  have hmem : ∀ {k : W} {x : V}, k ∈ T → x ∈ C.branchSet k → x ∈ S := fun hk hx => hsub hk hx
  -- Reachability inside a single branch set.
  have hin : ∀ {k : W} (hk : k ∈ T) {x y : V} (hx : x ∈ C.branchSet k) (hy : y ∈ C.branchSet k),
      (F.induce S).Reachable ⟨x, hmem hk hx⟩ ⟨y, hmem hk hy⟩ := by
    intro k hk x y hx hy
    obtain ⟨p⟩ := (C.connected k).preconnected ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨p.map (inclHom (hsub hk))⟩
  -- Reachability along a walk of indices.
  have key : ∀ {a b : T} (_ : (K.induce T).Walk a b) {x y : V}
      (hx : x ∈ C.branchSet (a : W)) (hy : y ∈ C.branchSet (b : W)),
      (F.induce S).Reachable ⟨x, hmem a.2 hx⟩ ⟨y, hmem b.2 hy⟩ := by
    intro a b p
    induction p with
    | @nil a => intro x y hx hy; exact hin a.2 hx hy
    | @cons a c b hac _ ih =>
      intro x y hx hy
      obtain ⟨u, hu, w, hw, huw⟩ := C.adjacent hac
      exact ((hin a.2 hx hu).trans
        (Adj.reachable (show (F.induce S).Adj ⟨u, hmem a.2 hu⟩ ⟨w, hmem c.2 hw⟩ from
          huw))).trans (ih hw hy)
  -- Assemble.
  obtain ⟨k₀⟩ := hT.nonempty
  obtain ⟨⟨x₀, hx₀⟩⟩ := (C.connected (k₀ : W)).nonempty
  haveI : Nonempty ↥S := ⟨⟨x₀, hmem k₀.2 hx₀⟩⟩
  refine ⟨fun p q => ?_⟩
  obtain ⟨x, hx⟩ := p
  obtain ⟨y, hy⟩ := q
  obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.1 hx
  obtain ⟨l, hl, hyl⟩ := Set.mem_iUnion₂.1 hy
  exact key (hT.preconnected ⟨k, hk⟩ ⟨l, hl⟩).some hxk hyl

theorem IsMinor.trans {X : Type*} {K : SimpleGraph W} {J : SimpleGraph X}
    (h : IsMinor J K) (h' : IsMinor K F) : IsMinor J F := by
  obtain ⟨B⟩ := h
  obtain ⟨C⟩ := h'
  refine ⟨{ branch := fun j => ⋃ k ∈ B.branchSet j, C.branchSet k
            connected := fun j => connected_biUnion_branch C _ (B.connected j)
            disjoint := ?_
            adjacent := ?_ }⟩
  · intro j j' hjj'
    rw [Set.disjoint_left]
    rintro x hx hx'
    obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨l, hl, hxl⟩ := Set.mem_iUnion₂.1 hx'
    have hkl : k ≠ l := fun hkl => (B.disjoint hjj').le_bot ⟨hk, hkl ▸ hl⟩
    exact (C.disjoint hkl).le_bot ⟨hxk, hxl⟩
  · intro j j' hjj'
    obtain ⟨k, hk, l, hl, hkl⟩ := B.adjacent hjj'
    obtain ⟨x, hx, y, hy, hxy⟩ := C.adjacent hkl
    exact ⟨x, Set.mem_biUnion hk hx, y, Set.mem_biUnion hl hy, hxy⟩

/-- A subgraph on the same vertex set is a minor. -/
theorem isMinor_spanningSubgraph (F : SimpleGraph V) (s : Set (Sym2 V)) :
    IsMinor ((spanningSubgraph F) s) F := ⟨MinorModel.ofLE (spanningSubgraph_le F s)⟩

/-- An induced subgraph is a minor. -/
theorem isMinor_induce (F : SimpleGraph V) (s : Set V) : IsMinor (F.induce s) F :=
  ⟨{ branchSet v := {(v : V)}
     connected v := connected_induce_singleton F v
     disjoint _ _ hvw := Set.disjoint_singleton.2 fun h => hvw (Subtype.ext h)
     adjacent _ _ hvw := ⟨_, rfl, _, rfl, hvw⟩ }⟩

/-- A graph obtained by deleting edges is a minor. -/
theorem isMinor_deleteEdges (F : SimpleGraph V) (s : Set (Sym2 V)) :
    IsMinor (F.deleteEdges s) F := ⟨MinorModel.ofLE (deleteEdges_le s)⟩

/-- A contraction quotient is a minor, provided it is loopless. -/
theorem isMinor_of_iso_contractionQuotient {L : Set (Sym2 V)} (hL : L ⊆ F.edgeSet)
    {K : SimpleGraph W} (e : (toLoopGraph K) ≃lg (F ⊘ L)) : IsMinor K F := by
  have hle : fromEdgeSet L ≤ F := by
    intro a b hab
    rw [fromEdgeSet_adj] at hab
    exact hL hab.1
  exact ⟨{
    branchSet w := (e w).supp
    connected w :=
      Connected.mono (fun _ _ hab => hle hab) (ConnectedComponent.connected_toSimpleGraph (e w))
    disjoint v w hvw := by
      rw [Set.disjoint_left]
      intro x hx hx'
      rw [ConnectedComponent.mem_supp_iff] at hx hx'
      exact hvw (e.injective (hx.symm.trans hx'))
    adjacent v w hvw := by
      obtain ⟨x, y, hxy, -, hx, hy⟩ := e.map_rel_iff.2 hvw
      exact ⟨x, hx, y, hy, hxy⟩ }⟩

/-! ### Contracting a single edge -/

/-- The simple graph obtained from `F` by contracting the single edge `uv`.  Contracting one
edge of a simple graph never creates a loop
(`SimpleGraph.contractionQuotient_singleton_isLoopless`), so unlike `F ⊘ L` this is again a
simple graph. -/
noncomputable def contractEdge (F : SimpleGraph V) (u v : V) :
    SimpleGraph (fromEdgeSet ({s(u, v)} : Set (Sym2 V))).ConnectedComponent :=
  (F ⊘ ({s(u, v)} : Set (Sym2 V))).toSimpleGraph (contractionQuotient_singleton_isLoopless u v)

@[simp]
theorem contractEdge_adj (F : SimpleGraph V) (u v : V)
    {c d : (fromEdgeSet ({s(u, v)} : Set (Sym2 V))).ConnectedComponent} :
    (F.contractEdge u v).Adj c d ↔ ∃ x y, F.Adj x y ∧ s(x, y) ∉ ({s(u, v)} : Set (Sym2 V)) ∧
      (fromEdgeSet ({s(u, v)} : Set (Sym2 V))).connectedComponentMk x = c ∧
      (fromEdgeSet ({s(u, v)} : Set (Sym2 V))).connectedComponentMk y = d := Iff.rfl

theorem toLoopGraph_contractEdge (F : SimpleGraph V) (u v : V) :
    (toLoopGraph (F.contractEdge u v)) = F ⊘ ({s(u, v)} : Set (Sym2 V)) := rfl

/-- A connected induced subgraph with two distinct vertices contains an edge. -/
theorem exists_adj_of_connected_of_ne {s : Set V} (h : (F.induce s).Connected) {x y : ↥s}
    (hxy : x ≠ y) : ∃ p q : ↥s, (F.induce s).Adj p q := by
  obtain ⟨w⟩ := h.preconnected x y
  cases w with
  | nil => exact absurd rfl hxy
  | cons hab _ => exact ⟨_, _, hab⟩

/-- The image of a connected set of vertices under a single-edge contraction is connected:
each edge either survives or has its two endpoints identified. -/
theorem connected_induce_image_contractEdge {s : Set V} {a b : V} (hab : F.Adj a b)
    (h : (F.induce s).Connected) :
    ((F.contractEdge a b).induce
      ((fromEdgeSet ({s(a, b)} : Set (Sym2 V))).connectedComponentMk '' s)).Connected := by
  classical
  set q := (fromEdgeSet ({s(a, b)} : Set (Sym2 V))).connectedComponentMk with hqdef
  set T : Set (fromEdgeSet ({s(a, b)} : Set (Sym2 V))).ConnectedComponent := q '' s with hTdef
  have hmem : ∀ {x : V}, x ∈ s → q x ∈ T := fun hx => ⟨_, hx, rfl⟩
  have hstep : ∀ {x y : ↥s}, (F.induce s).Adj x y → q ↑x ≠ q ↑y →
      ((F.contractEdge a b).induce T).Adj ⟨q ↑x, hmem x.2⟩ ⟨q ↑y, hmem y.2⟩ := by
    intro x y hxy hne
    exact ⟨↑x, ↑y, hxy, fun hc => hne ((connectedComponentMk_eq_iff hab.ne).2 (Or.inr hc)),
      rfl, rfl⟩
  have hwalk : ∀ {x y : ↥s}, (F.induce s).Walk x y →
      ((F.contractEdge a b).induce T).Reachable ⟨q ↑x, hmem x.2⟩ ⟨q ↑y, hmem y.2⟩ := by
    intro x y p
    induction p with
    | nil => rfl
    | @cons x' z' _ hxz _ ih =>
      rcases Classical.em (q ↑x' = q ↑z') with heq | hne
      · have hsub : (⟨q ↑x', hmem x'.2⟩ : ↥T) = ⟨q ↑z', hmem z'.2⟩ := Subtype.ext heq
        rw [hsub]
        exact ih
      · exact (Adj.reachable (hstep hxz hne)).trans ih
  obtain ⟨x₀⟩ := h.nonempty
  haveI : Nonempty ↥T := ⟨⟨q ↑x₀, hmem x₀.2⟩⟩
  refine ⟨fun c d => ?_⟩
  obtain ⟨x, hx, hxc⟩ := c.2
  obtain ⟨y, hy, hyd⟩ := d.2
  rw [show c = ⟨q x, hmem hx⟩ from Subtype.ext hxc.symm,
    show d = ⟨q y, hmem hy⟩ from Subtype.ext hyd.symm]
  exact hwalk (h.preconnected ⟨x, hx⟩ ⟨y, hy⟩).some

/-- **Contracting an edge inside a branch set.**  Pushing the branch sets forward along a
single-edge contraction again gives a minor model, provided the contracted edge lies inside one
branch set: the quotient map identifies only its two endpoints, so the branch sets stay
disjoint. -/
noncomputable def MinorModel.contractEdge {K : SimpleGraph W} (C : MinorModel K F) {w₀ : W}
    {a b : V} (hab : F.Adj a b) (ha : a ∈ C.branchSet w₀) (hb : b ∈ C.branchSet w₀) :
    MinorModel K (F.contractEdge a b) where
  branchSet w := (fromEdgeSet ({s(a, b)} : Set (Sym2 V))).connectedComponentMk '' C.branchSet w
  connected w := connected_induce_image_contractEdge hab (C.connected w)
  disjoint v w hvw := by
    have hbr : ∀ {u : W} {z : V}, z ∈ C.branchSet u → z ∈ C.branchSet w₀ → u = w₀ := by
      intro u z hz hz0
      by_contra hne
      exact Set.disjoint_left.1 (C.disjoint hne) hz hz0
    rw [Set.disjoint_left]
    rintro c ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    rcases (connectedComponentMk_eq_iff hab.ne).1 hyx with rfl | he
    · exact Set.disjoint_left.1 (C.disjoint hvw) hx hy
    · rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hvw ((hbr hx (by rw [h2]; exact hb)).trans (hbr hy (by rw [h1]; exact ha)).symm)
      · exact hvw ((hbr hx (by rw [h2]; exact ha)).trans (hbr hy (by rw [h1]; exact hb)).symm)
  adjacent v w hvw := by
    have hbr : ∀ {u : W} {z : V}, z ∈ C.branchSet u → z ∈ C.branchSet w₀ → u = w₀ := by
      intro u z hz hz0
      by_contra hne
      exact Set.disjoint_left.1 (C.disjoint hne) hz hz0
    obtain ⟨x, hx, y, hy, hxy⟩ := C.adjacent hvw
    refine ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, x, y, hxy, fun hc => ?_, rfl, rfl⟩
    rcases Sym2.eq_iff.1 hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hvw.ne ((hbr hx (by rw [h1]; exact ha)).trans (hbr hy (by rw [h2]; exact hb)).symm)
    · exact hvw.ne ((hbr hx (by rw [h1]; exact hb)).trans (hbr hy (by rw [h2]; exact ha)).symm)

/-- A minor model whose branch sets are all singletons exhibits `K` as a spanning subgraph of
an induced subgraph of `F`: no contraction is needed. -/
theorem MinorModel.exists_iso_of_forall_subsingleton {K : SimpleGraph W} (C : MinorModel K F)
    (hsub : ∀ w, (C.branchSet w).Subsingleton) :
    ∃ (s : Set V) (t : Set (Sym2 ↥s)), Nonempty (K ≃g (spanningSubgraph (F.induce s)) t) := by
  classical
  set f : W → V := fun w => (((C.connected w).nonempty.some : ↥(C.branchSet w)) : V) with hfdef
  have hfmem : ∀ w, f w ∈ C.branchSet w := fun w => ((C.connected w).nonempty.some).2
  have hbranch : ∀ w, C.branchSet w = {f w} := fun w =>
    Set.eq_singleton_iff_unique_mem.2 ⟨hfmem w, fun x hx => hsub w hx (hfmem w)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    exact Set.disjoint_left.1 (C.disjoint hne) (hfmem x) (by rw [hxy]; exact hfmem y)
  set g : W → ↥(Set.range f) := fun w => ⟨f w, ⟨w, rfl⟩⟩ with hgdef
  have hgbij : Function.Bijective g :=
    ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), by rintro ⟨-, w, rfl⟩; exact ⟨w, rfl⟩⟩
  refine ⟨Set.range f, {p | ∃ v w, K.Adj v w ∧ p = s(g v, g w)},
    ⟨⟨Equiv.ofBijective g hgbij, ?_⟩⟩⟩
  intro v w
  constructor
  · rintro ⟨-, v', w', hvw', hp⟩
    rcases Sym2.eq_iff.1 hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hgbij.1 h1, hgbij.1 h2]; exact hvw'
    · rw [hgbij.1 h1, hgbij.1 h2]; exact hvw'.symm
  · intro hvw
    obtain ⟨x, hx, y, hy, hxy⟩ := C.adjacent hvw
    rw [hbranch v, Set.mem_singleton_iff] at hx
    rw [hbranch w, Set.mem_singleton_iff] at hy
    exact ⟨by rw [hx, hy] at hxy; exact hxy, v, w, hvw, rfl⟩

/-- **Every minor is produced by the three atomic operations**: from a minor model of `K` in
`F` one reads off a set `s` of vertices to keep, a set `t` of edges to keep and a set `L` of
edges to contract, such that `K` is the resulting contraction quotient.

The vertices kept are the union of the branch sets, the edges kept are those joining two
vertices of one branch set together with those joining branch sets of adjacent vertices of `K`,
and the edges contracted are the former. -/
theorem MinorModel.exists_eq_contractionQuotient {K : SimpleGraph W} (C : MinorModel K F) :
    ∃ (s : Set V) (t L : Set (Sym2 ↥s)),
      L ⊆ ((spanningSubgraph (F.induce s)) t).edgeSet ∧
        Nonempty ((toLoopGraph K) ≃lg ((spanningSubgraph (F.induce s)) t ⊘ L)) := by
  classical
  set s : Set V := ⋃ w, C.branchSet w with hsdef
  have hmem : ∀ {w : W} {x : V}, x ∈ C.branchSet w → x ∈ s := fun hx => Set.mem_iUnion.2 ⟨_, hx⟩
  -- Every kept vertex lies in exactly one branch set; `idx` names its index.
  have hex : ∀ x : ↥s, ∃ w, (x : V) ∈ C.branchSet w := fun x => Set.mem_iUnion.1 x.2
  set idx : ↥s → W := fun x => (hex x).choose with hidxdef
  have hidx : ∀ x : ↥s, (x : V) ∈ C.branchSet (idx x) := fun x => (hex x).choose_spec
  have hidx_eq : ∀ (x : ↥s) (w : W), (x : V) ∈ C.branchSet w → idx x = w := fun x w hx => by
    by_contra hne
    exact (C.disjoint hne).le_bot ⟨hidx x, hx⟩
  set F₁ := F.induce s with hF₁def
  -- The edges inside a branch set, and the edges realising an adjacency of `K`.
  set L : Set (Sym2 ↥s) :=
    Sym2.fromRel (r := fun x y => F₁.Adj x y ∧ idx x = idx y)
      ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩ with hLdef
  set C' : Set (Sym2 ↥s) :=
    Sym2.fromRel (r := fun x y => F₁.Adj x y ∧ K.Adj (idx x) (idx y))
      ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩ with hC'def
  have hLmem : ∀ x y : ↥s, s(x, y) ∈ L ↔ F₁.Adj x y ∧ idx x = idx y := fun _ _ =>
    Sym2.fromRel_prop
  have hC'mem : ∀ x y : ↥s, s(x, y) ∈ C' ↔ F₁.Adj x y ∧ K.Adj (idx x) (idx y) := fun _ _ =>
    Sym2.fromRel_prop
  -- The classes of `fromEdgeSet L` are exactly the branch sets.
  have hwalk : ∀ (w : W) (a b : ↥(C.branchSet w)), (F.induce (C.branchSet w)).Walk a b →
      (fromEdgeSet L).Reachable ⟨a.1, hmem a.2⟩ ⟨b.1, hmem b.2⟩ := by
    intro w a b p
    induction p with
    | nil => exact Reachable.refl _
    | @cons a' b' _ hab _ ih =>
      refine Reachable.trans (Adj.reachable ?_) ih
      rw [fromEdgeSet_adj]
      refine ⟨(hLmem _ _).2 ⟨hab, (hidx_eq _ w a'.2).trans (hidx_eq _ w b'.2).symm⟩, fun hc => ?_⟩
      exact hab.ne (Subtype.ext (congrArg (Subtype.val : ↥s → V) hc))
  have hreach : ∀ (w : W) (x y : ↥s), (x : V) ∈ C.branchSet w → (y : V) ∈ C.branchSet w →
      (fromEdgeSet L).Reachable x y := fun w x y hx hy => by
    obtain ⟨p⟩ := (C.connected w).preconnected ⟨x.1, hx⟩ ⟨y.1, hy⟩
    exact hwalk w _ _ p
  have hconst : ∀ x y : ↥s, (fromEdgeSet L).Reachable x y → idx x = idx y := by
    rintro x y ⟨p⟩
    induction p with
    | nil => rfl
    | @cons a b c hab _ ih =>
      rw [fromEdgeSet_adj] at hab
      exact ((hLmem _ _).1 hab.1).2.trans ih
  -- Hence they are indexed by the vertices of `K`.
  have hpt : ∀ w : W, ∃ x : ↥s, idx x = w := fun w => by
    obtain ⟨a⟩ := (C.connected w).nonempty
    exact ⟨⟨a.1, hmem a.2⟩, hidx_eq _ w a.2⟩
  set pt : W → ↥s := fun w => (hpt w).choose with hptdef
  have hptspec : ∀ w, idx (pt w) = w := fun w => (hpt w).choose_spec
  set ι : (fromEdgeSet L).ConnectedComponent ≃ W :=
    { toFun := ConnectedComponent.lift idx fun x y p _ => hconst x y ⟨p⟩
      invFun := fun w => connectedComponentMk _ (pt w)
      left_inv := by
        refine ConnectedComponent.ind fun x => ?_
        refine ConnectedComponent.eq.2 (hreach (idx x) _ _ ?_ (hidx x))
        rw [← hptspec (idx x)]
        exact hidx (pt (idx x))
      right_inv := hptspec } with hιdef
  have hιmk : ∀ x : ↥s, ι (connectedComponentMk _ x) = idx x := fun _ => rfl
  refine ⟨s, L ∪ C', L, ?_, ⟨⟨ι.symm, ?_⟩⟩⟩
  · -- The contracted edges are edges of the kept graph.
    intro e he
    induction e using Sym2.ind with
    | h x y => exact ⟨((hLmem x y).1 he).1, Or.inl he⟩
  · -- Two classes are adjacent exactly when the corresponding vertices of `K` are.
    intro a b
    constructor
    · rintro ⟨x, y, ⟨hxy, hxyt⟩, hnL, hx, hy⟩
      have hax : idx x = a := by rw [← hιmk, hx, ι.apply_symm_apply]
      have hby : idx y = b := by rw [← hιmk, hy, ι.apply_symm_apply]
      rcases hxyt with h | h
      · exact absurd h hnL
      · rw [← hax, ← hby]; exact ((hC'mem x y).1 h).2
    · intro hab
      obtain ⟨p, hp, q, hq, hpq⟩ := C.adjacent hab
      refine ⟨⟨p, hmem hp⟩, ⟨q, hmem hq⟩, ⟨hpq, Or.inr ((hC'mem _ _).2 ⟨hpq, ?_⟩)⟩, ?_, ?_, ?_⟩
      · rw [hidx_eq _ a hp, hidx_eq _ b hq]; exact hab
      · rw [hLmem]
        rintro ⟨-, hidxeq⟩
        rw [hidx_eq _ a hp, hidx_eq _ b hq] at hidxeq
        exact hab.ne hidxeq
      · exact ι.injective (by rw [hιmk, ι.apply_symm_apply, hidx_eq _ a hp])
      · exact ι.injective (by rw [hιmk, ι.apply_symm_apply, hidx_eq _ b hq])

/-- **The model definition agrees with the operational one**: `K` is a minor of `F` exactly
when it is isomorphic to a contraction quotient of a spanning subgraph of an induced subgraph
of `F` — that is, exactly when `K` is obtained from `F` by deleting vertices, deleting edges
and contracting edges.

The hypothesis `L ⊆ ((F.induce s).spanningSubgraph t).edgeSet` is essential: contracting a set
of pairs that are not edges would merge vertices lying in different components, which is not a
minor operation.

This is the bridge between `SimpleGraph.IsMinor` and the closure properties of
`HomInd/Closure.lean`. -/
theorem isMinor_iff_exists_induce_spanningSubgraph_contraction {K : SimpleGraph W} :
    IsMinor K F ↔ ∃ (s : Set V) (t L : Set (Sym2 ↥s)),
      L ⊆ ((spanningSubgraph (F.induce s)) t).edgeSet ∧
        Nonempty ((toLoopGraph K) ≃lg ((spanningSubgraph (F.induce s)) t ⊘ L)) := by
  refine ⟨fun ⟨C⟩ => C.exists_eq_contractionQuotient, ?_⟩
  rintro ⟨s, t, L, hL, ⟨e⟩⟩
  exact (isMinor_of_iso_contractionQuotient hL e).trans
    ((isMinor_spanningSubgraph _ t).trans (isMinor_induce F s))

end SimpleGraph

end Lax871432Proofs
