/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Lax871432.LoopGraphs
import Lax871432Proofs.GraphTheory.Minor
import Lax871432Proofs.Hom.LoopGraph
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finite.Card

/-!
# Homomorphism counts into complements

This file expands `hom(F, Gᶜ)` as a signed sum of homomorphism counts into `G` itself, indexed
by minors of `F`.  It is the analogue of `Hom/DisjUnion.lean` for complements, and the input to
`thm:complement` in `PreservationClosure/Complement.lean`.

The expansion proceeds in two steps, matching the factorisation `Gᶜ = (G°)^` of
`SimpleGraph.fullCompl_looped`.

1. **Full complements** (`SimpleGraph.homCount_fullCompl`, Lovász, *Large Networks and Graph
   Limits* (2012), equation (5.23)): by inclusion–exclusion over the edges of `F`,

   `hom(F, X̂) = ∑_{s ⊆ E(F)} (-1)^{|s|} hom(F_s, X)`,

   where `F_s` is the spanning subgraph of `F` with edge set `s`.

2. **Looped graphs** (`SimpleGraph.homCount_looped`): a homomorphism `F → G°` is the same
   thing as a pair consisting of a set `L ⊆ E(F)` of edges collapsed to loops and a
   homomorphism out of the contraction quotient, whence

   `hom(F, G°) = ∑_{L ⊆ E(F)} hom(F ⊘ L, G)`.

Composing the two gives `SimpleGraph.homCount_compl`, equation `eq:del-contr` of the paper:
every graph occurring on the right-hand side is obtained from `F` by deleting and contracting
edges, i.e. is a minor of `F`.

## Main declarations

* `SimpleGraph.homCount_fullCompl`: equation (5.23).
* `SimpleGraph.homCount_looped`: `hom(F, G°) = ∑_L hom(F ⊘ L, G)`.
* `SimpleGraph.homCount_compl`: `eq:del-contr`.

## Implementation notes

Signs force the identities to live in `ℤ` rather than `ℕ`.  Sums range over
`Finset F.edgeSet`, which requires `Fintype F.edgeSet`; this is available for a finite `F` with
decidable adjacency, and is supplied as an instance argument.
-/

namespace Lax871432Proofs

open _root_.SimpleGraph
open Lax871432.LoopGraphs
open scoped Lax871432.LoopGraphs
open Lax871432.HomomorphismCounts
open Lax68.GraphMinors

open Function

namespace SimpleGraph

open scoped LoopGraph

variable {V W : Type*}

/-! ### Homomorphisms into a full complement -/

/-- An edge of `F` lies in the set of pairs selected by `L` exactly when it lies in `L`. -/
theorem mem_edgeSetOf_iff (F : SimpleGraph V) (L : Finset F.edgeSet) (e : F.edgeSet) :
    (e : Sym2 V) ∈ (edgeSetOf F) L ↔ e ∈ L := by
  simp [Lax871432.LoopGraphs.edgeSetOf, Subtype.val_injective.eq_iff]

/-- **Equation (5.23)**: the number of homomorphisms from a simple graph `F` into a full
complement `X̂`, by inclusion–exclusion over the edges of `F`.

For each edge `e` of `F` let `A e` be the set of vertex maps sending `e` to an edge or loop of
`X`.  A vertex map is a homomorphism into `X̂` exactly when it avoids every `A e`, and for
`s ⊆ E(F)` the intersection `⋂_{e ∈ s} A e` is the set of homomorphisms `F_s → X`. -/
theorem homCount_fullCompl [Finite V] [Finite W] (F : SimpleGraph V) [Fintype F.edgeSet]
    (X : LoopGraph W) :
    (LoopGraph.homCount (toLoopGraph F) X.fullCompl : ℤ) =
      ∑ s : Finset F.edgeSet, (-1 : ℤ) ^ s.card *
        (LoopGraph.homCount (toLoopGraph ((spanningSubgraph F) ((edgeSetOf F) s))) X : ℤ) := by
  classical
  haveI := Fintype.ofFinite V
  haveI := Fintype.ofFinite W
  -- `A f e` says that `f` sends the endpoints of the edge `e` to an adjacent pair of `X`.
  set A : (V → W) → F.edgeSet → Prop := fun f e =>
    Sym2.lift ⟨fun a b => X.Adj (f a) (f b),
      fun _ _ => propext ⟨fun h => X.symm.symm _ _ h, fun h => X.symm.symm _ _ h⟩⟩
      (e : Sym2 V) with hA
  have hAmk : ∀ (f : V → W) (a b : V) (hab : F.Adj a b),
      A f ⟨s(a, b), hab⟩ ↔ X.Adj (f a) (f b) := fun _ _ _ _ => Iff.rfl
  -- Every homomorphism count is a number of vertex maps.
  have hcount : ∀ (Y : LoopGraph V) (Z : LoopGraph W), LoopGraph.homCount Y Z =
      (Finset.univ.filter fun f : V → W => ∀ a b, Y.Adj a b → Z.Adj (f a) (f b)).card := by
    intro Y Z
    haveI : Fintype (Y →lg Z) := Fintype.ofFinite _
    rw [LoopGraph.homCount, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    exact Fintype.card_congr
      { toFun := fun g => ⟨⇑g, fun _ _ h => g.map_rel h⟩
        invFun := fun f => ⟨f.1, fun {_ _} h => f.2 _ _ h⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  -- The condition defining `hom(F_s, X)` is a conjunction over the edges of `s`.
  have hspan : ∀ (s : Finset F.edgeSet) (f : V → W),
      (∀ a b, (toLoopGraph ((spanningSubgraph F) ((edgeSetOf F) s))).Adj a b → X.Adj (f a) (f b)) ↔
        ∀ e ∈ s, A f e := by
    intro s f
    constructor
    · rintro h ⟨e, he⟩ hes
      induction e using Sym2.ind with
      | h a b =>
        rw [mem_edgeSet] at he
        exact (hAmk f a b he).2 (h a b ⟨he, (mem_edgeSetOf_iff F s ⟨s(a, b), he⟩).2 hes⟩)
    · rintro h a b ⟨hab, hmem⟩
      exact (hAmk f a b hab).1 (h _ ((mem_edgeSetOf_iff F s ⟨s(a, b), hab⟩).1 hmem))
  -- Likewise the condition defining `hom(F, X̂)` says that no edge is realised.
  have hfull : ∀ f : V → W,
      (∀ a b, (toLoopGraph F).Adj a b → X.fullCompl.Adj (f a) (f b)) ↔ ∀ e : F.edgeSet, ¬ A f e := by
    intro f
    constructor
    · rintro h ⟨e, he⟩
      induction e using Sym2.ind with
      | h a b => rw [mem_edgeSet] at he; exact fun hc => h a b he ((hAmk f a b he).1 hc)
    · exact fun h a b hab hc => h ⟨s(a, b), hab⟩ ((hAmk f a b hab).2 hc)
  -- Expand both sides as sums over vertex maps and apply inclusion–exclusion.
  rw [hcount (toLoopGraph F) X.fullCompl, ← Finset.sum_boole]
  simp_rw [hcount _ X, ← Finset.sum_boole, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  -- Each summand on the right is a product of indicators over the selected edges.
  have hprod : ∀ s : Finset F.edgeSet,
      (if ∀ a b, (toLoopGraph ((spanningSubgraph F) ((edgeSetOf F) s))).Adj a b → X.Adj (f a) (f b)
        then (1 : ℤ) else 0) = ∏ e ∈ s, if A f e then (1 : ℤ) else 0 := by
    intro s
    rw [Finset.prod_boole]
    by_cases hc : ∀ e ∈ s, A f e
    · rw [if_pos hc, if_pos ((hspan s f).2 hc)]
    · rw [if_neg hc, if_neg fun h => hc ((hspan s f).1 h)]
  simp_rw [hprod]
  -- The left-hand side is the product over *all* edges of `1` minus the indicator.
  have hL : (if ∀ a b, (toLoopGraph F).Adj a b → X.fullCompl.Adj (f a) (f b) then (1 : ℤ) else 0)
      = ∏ e : F.edgeSet, (1 - if A f e then (1 : ℤ) else 0) := by
    have hstep : ∀ e : F.edgeSet,
        (1 - if A f e then (1 : ℤ) else 0) = if ¬ A f e then (1 : ℤ) else 0 := by
      intro e; by_cases h : A f e <;> simp [h]
    simp_rw [hstep]
    rw [Finset.prod_boole]
    by_cases hc : ∀ e ∈ (Finset.univ : Finset F.edgeSet), ¬ A f e
    · rw [if_pos hc, if_pos ((hfull f).2 fun e => hc e (Finset.mem_univ e))]
    · rw [if_neg hc, if_neg fun h => hc fun e _ => (hfull f).1 h e]
  rw [hL, show (fun e : F.edgeSet => (1 : ℤ) - (if A f e then (1 : ℤ) else 0)) =
      fun e => (-(if A f e then (1 : ℤ) else 0)) + 1 from funext fun _ => sub_eq_neg_add _ _,
    Finset.prod_add, ← Finset.powerset_univ]
  exact Finset.sum_congr rfl fun t _ => by
    rw [Finset.prod_neg, Finset.prod_const_one, mul_one]

/-! ### Homomorphisms into a looped graph -/

/-- The set of edges of `F` collapsed by a homomorphism `f : F → G°`, namely those whose two
endpoints have the same image. -/
noncomputable def collapsedEdges {F : SimpleGraph V} {G : SimpleGraph W} [Fintype F.edgeSet]
    (f : (toLoopGraph F) →lg (looped G)) : Finset F.edgeSet := by
  classical
  exact {e ∈ Finset.univ |
    Sym2.lift ⟨fun u v => f u = f v, by intros; simp [eq_comm]⟩ (e : Sym2 V)}

/-- The endpoints of a contracted edge lie in the same class. -/
theorem connectedComponentMk_eq_of_mem {F : SimpleGraph V} (L : Finset F.edgeSet) {x y : V}
    (hxy : F.Adj x y) (hL : (⟨s(x, y), hxy⟩ : F.edgeSet) ∈ L) :
    (fromEdgeSet ((edgeSetOf F) L)).connectedComponentMk x =
      (fromEdgeSet ((edgeSetOf F) L)).connectedComponentMk y := by
  refine ConnectedComponent.eq.2 (Adj.reachable ?_)
  rw [fromEdgeSet_adj]
  exact ⟨(mem_edgeSetOf_iff F L ⟨s(x, y), hxy⟩).2 hL, hxy.ne⟩

/-- A set `L` of edges of `F` together with a homomorphism out of the contraction `F ⊘ L`
determines a homomorphism `F → G°`: compose with the quotient map.  An edge of `F` is sent to
a loop exactly when it lies in `L`. -/
def homLoopedOfContraction (F : SimpleGraph V) (G : SimpleGraph W)
    (p : Σ L : Finset F.edgeSet, ((F ⊘ (edgeSetOf F) L) →lg (toLoopGraph G))) :
    (toLoopGraph F) →lg (looped G) where
  toFun x := p.2 ((fromEdgeSet ((edgeSetOf F) p.1)).connectedComponentMk x)
  map_rel' := by
    intro x y hxy
    by_cases hc : (fromEdgeSet ((edgeSetOf F) p.1)).connectedComponentMk x =
        (fromEdgeSet ((edgeSetOf F) p.1)).connectedComponentMk y
    · exact Or.inr (by rw [hc])
    · refine Or.inl (p.2.map_rel ⟨x, y, hxy, fun hm => hc ?_, rfl, rfl⟩)
      exact connectedComponentMk_eq_of_mem p.1 hxy ((mem_edgeSetOf_iff F p.1 _).1 hm)

theorem homLoopedOfContraction_apply (F : SimpleGraph V) (G : SimpleGraph W)
    (p : Σ L : Finset F.edgeSet, ((F ⊘ (edgeSetOf F) L) →lg (toLoopGraph G))) (x : V) :
    homLoopedOfContraction F G p x =
      p.2 ((fromEdgeSet ((edgeSetOf F) p.1)).connectedComponentMk x) := rfl

/-- **The key step of `lem:looping`**: an edge of `F` is collapsed by the associated
homomorphism into `G°` exactly when it was selected for contraction.  The forward direction is
immediate; the converse uses that `G` is loopless, so an *uncontracted* edge must be sent to a
genuine edge of `G`. -/
theorem mem_iff_homLoopedOfContraction_eq (F : SimpleGraph V) (G : SimpleGraph W)
    (L : Finset F.edgeSet) (ψ : (F ⊘ (edgeSetOf F) L) →lg (toLoopGraph G)) {x y : V}
    (hxy : F.Adj x y) :
    (⟨s(x, y), hxy⟩ : F.edgeSet) ∈ L ↔
      homLoopedOfContraction F G ⟨L, ψ⟩ x = homLoopedOfContraction F G ⟨L, ψ⟩ y := by
  refine ⟨fun hL => by
    rw [homLoopedOfContraction_apply, homLoopedOfContraction_apply,
      connectedComponentMk_eq_of_mem L hxy hL], fun heq => ?_⟩
  by_contra hL
  have hadj : (F ⊘ (edgeSetOf F) L).Adj
      ((fromEdgeSet ((edgeSetOf F) L)).connectedComponentMk x)
      ((fromEdgeSet ((edgeSetOf F) L)).connectedComponentMk y) :=
    ⟨x, y, hxy, fun hm => hL ((mem_edgeSetOf_iff F L _).1 hm), rfl, rfl⟩
  exact G.irrefl (heq ▸ ψ.map_rel hadj)

/-- **`lem:looping`**: a homomorphism `F → G°` is the same thing as a set `L` of edges of `F`
together with a homomorphism `F ⊘ L → G`.

The map from right to left is `SimpleGraph.homLoopedOfContraction`.  It is injective because
`SimpleGraph.mem_iff_homLoopedOfContraction_eq` recovers `L` from the composite, and surjective
because a homomorphism `f : F → G°` factors through the contraction by the edges it collapses
(`SimpleGraph.collapsedEdges`). -/
theorem nonempty_equiv_hom_looped [Finite V] (F : SimpleGraph V) (G : SimpleGraph W) :
    Nonempty (((toLoopGraph F) →lg (looped G)) ≃
      Σ L : Finset F.edgeSet, ((F ⊘ (edgeSetOf F) L) →lg (toLoopGraph G))) := by
  classical
  haveI : Fintype F.edgeSet := Fintype.ofFinite _
  refine ⟨(Equiv.ofBijective (homLoopedOfContraction F G) ⟨?_, ?_⟩).symm⟩
  · -- Injectivity.
    rintro ⟨L, φ⟩ ⟨L', φ'⟩ hEq
    have hfun : ∀ x, homLoopedOfContraction F G ⟨L, φ⟩ x =
        homLoopedOfContraction F G ⟨L', φ'⟩ x := fun x => DFunLike.congr_fun hEq x
    have hLL : L = L' := by
      ext e
      obtain ⟨e, he⟩ := e
      induction e using Sym2.ind with
      | h x y =>
        rw [mem_edgeSet] at he
        rw [mem_iff_homLoopedOfContraction_eq F G L φ he,
          mem_iff_homLoopedOfContraction_eq F G L' φ' he, hfun, hfun]
    subst hLL
    refine Sigma.mk.injEq .. ▸ ⟨rfl, heq_of_eq (DFunLike.ext _ _ ?_)⟩
    refine ConnectedComponent.ind fun x => ?_
    exact hfun x
  · -- Surjectivity.
    intro f
    -- `f` identifies the endpoints of every edge it collapses, hence of every reachable pair.
    have hedge : ∀ {a b : V}, s(a, b) ∈ (edgeSetOf F) (collapsedEdges f) → f a = f b := by
      rintro a b ⟨⟨e, he⟩, heL, hev⟩
      subst hev
      simpa [collapsedEdges, Sym2.lift_mk] using heL
    have hconst : ∀ {x y : V},
        (fromEdgeSet ((edgeSetOf F) (collapsedEdges f))).Reachable x y → f x = f y := by
      rintro x y ⟨p⟩
      induction p with
      | nil => rfl
      | @cons a b c hab _ ih =>
        rw [fromEdgeSet_adj] at hab
        exact (hedge hab.1).trans ih
    refine ⟨⟨collapsedEdges f,
      { toFun := ConnectedComponent.lift f fun _ _ p _ => hconst ⟨p⟩
        map_rel' := ?_ }⟩, DFunLike.ext _ _ fun _ => rfl⟩
    rintro c d ⟨x, y, hxy, hL, rfl, rfl⟩
    have hne : f x ≠ f y := fun hc =>
      hL ((mem_edgeSetOf_iff F _ ⟨s(x, y), hxy⟩).2
        (by simpa [collapsedEdges, Sym2.lift_mk] using hc))
    rcases f.map_rel hxy with h | h
    · exact h
    · exact absurd h hne

/-- **`lem:looping`**: `hom(F, G°) = ∑_{L ⊆ E(F)} hom(F ⊘ L, G)`.

Only those `L` for which `F ⊘ L` is loopless contribute; the remaining terms vanish by
`LoopGraph.homCount_eq_zero_of_not_isLoopless`. -/
theorem homCount_looped [Finite V] [Finite W] (F : SimpleGraph V) [Fintype F.edgeSet]
    (G : SimpleGraph W) :
    LoopGraph.homCount (toLoopGraph F) (looped G) =
      ∑ L : Finset F.edgeSet, LoopGraph.homCount (F ⊘ (edgeSetOf F) L) (toLoopGraph G) := by
  rw [LoopGraph.homCount, Nat.card_congr (nonempty_equiv_hom_looped F G).some, Nat.card_sigma]
  rfl

/-! ### Homomorphisms into a complement -/

/-- **`eq:del-contr`**: combining `SimpleGraph.homCount_fullCompl` and
`SimpleGraph.homCount_looped` through `SimpleGraph.fullCompl_looped`,

`hom(F, Gᶜ) = ∑_{s ⊆ E(F)} (-1)^{|s|} ∑_{L ⊆ s} hom(F_s ⊘ L, G)`.

Every `F_s ⊘ L` occurring here is obtained from `F` by deleting the edges outside `s` and then
contracting those in `L`, hence is a minor of `F`.  This is the identity from which
`thm:complement` is read off. -/
theorem homCount_compl [Finite V] [Finite W] (F : SimpleGraph V) [Fintype F.edgeSet]
    (G : SimpleGraph W) :
    (homCount F Gᶜ : ℤ) =
      ∑ s : Finset F.edgeSet, (-1 : ℤ) ^ s.card *
        ∑ L ∈ s.powerset,
          (LoopGraph.homCount
            (((spanningSubgraph F) ((edgeSetOf F) s)) ⊘ (edgeSetOf F) L) (toLoopGraph G) : ℤ) := by
  classical
  haveI := Fintype.ofFinite V
  rw [← homCount_toLoopGraph, ← fullCompl_looped, homCount_fullCompl]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  -- Expand `hom(F_s, G°)` by `lem:looping`, indexed by the subsets of the edges of `F_s`,
  -- and reindex those along the underlying sets of unordered pairs.
  haveI : Fintype ((spanningSubgraph F) ((edgeSetOf F) s)).edgeSet := Fintype.ofFinite _
  have hmemS : ∀ x : Sym2 V, x ∈ ((spanningSubgraph F) ((edgeSetOf F) s)).edgeSet ↔
      x ∈ F.edgeSet ∧ x ∈ (edgeSetOf F) s := by
    intro x; rw [edgeSet_spanningSubgraph]; exact Iff.rfl
  rw [homCount_looped ((spanningSubgraph F) ((edgeSetOf F) s)) G]
  push_cast
  refine Finset.sum_nbij'
    (i := fun L' : Finset ((spanningSubgraph F) ((edgeSetOf F) s)).edgeSet =>
      (L'.map ⟨Subtype.val, Subtype.val_injective⟩).subtype (· ∈ F.edgeSet))
    (j := fun L : Finset F.edgeSet =>
      (L.map ⟨Subtype.val, Subtype.val_injective⟩).subtype
        (· ∈ ((spanningSubgraph F) ((edgeSetOf F) s)).edgeSet))
    ?_ ?_ ?_ ?_ ?_
  · -- the image of a set of edges of `F_s` is a subset of `s`
    intro L' _
    rw [Finset.mem_powerset]
    intro e he
    rw [Finset.mem_subtype, Finset.mem_map] at he
    obtain ⟨e', he', hee'⟩ := he
    exact (mem_edgeSetOf_iff F s e).1 (hee' ▸ ((hmemS _).1 e'.2).2)
  · exact fun _ _ => Finset.mem_univ _
  · -- round trip on the left
    intro L' _
    ext e
    simp only [Finset.mem_subtype, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨a, ⟨b, hb, hab⟩, hae⟩
      exact Subtype.val_injective (hab.trans hae) ▸ hb
    · intro he
      exact ⟨⟨e.1, edgeSet_subset_edgeSet.2 (spanningSubgraph_le F _) e.2⟩,
        ⟨e, he, rfl⟩, rfl⟩
  · -- round trip on the right
    intro L hL
    rw [Finset.mem_powerset] at hL
    ext e
    simp only [Finset.mem_subtype, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨a, ⟨b, hb, hab⟩, hae⟩
      exact Subtype.val_injective (hab.trans hae) ▸ hb
    · intro he
      have hmem : (e : Sym2 V) ∈ ((spanningSubgraph F) ((edgeSetOf F) s)).edgeSet :=
        (hmemS _).2 ⟨e.2, (mem_edgeSetOf_iff F s e).2 (hL he)⟩
      exact ⟨⟨e.1, hmem⟩, ⟨e, he, rfl⟩, rfl⟩
  · -- the summands agree: the two descriptions select the same set of unordered pairs
    intro L' _
    have hset : (edgeSetOf ((spanningSubgraph F) ((edgeSetOf F) s))) L' =
        (edgeSetOf F) ((L'.map ⟨Subtype.val, Subtype.val_injective⟩).subtype (· ∈ F.edgeSet)) := by
      ext x
      simp only [Lax871432.LoopGraphs.edgeSetOf, Set.mem_image, Finset.mem_coe, Finset.mem_subtype]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a.1, edgeSet_subset_edgeSet.2 (spanningSubgraph_le F _) a.2⟩,
          Finset.mem_map_of_mem _ ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨b, hb, hab⟩ := Finset.mem_map.1 ha
        exact ⟨b, hb, hab⟩
    rw [hset]

/-! ### `eq:del-contr` as a linear combination of homomorphism counts -/

/-- A summation index of `eq:del-contr` that actually contributes: a set `s` of edges of `F` to
keep, a subset `L ⊆ s` to contract, and the requirement that the resulting quotient carry no
loop.  Indices whose quotient has a loop are omitted because their homomorphism count vanishes
identically. -/
abbrev DelContrIndex (F : SimpleGraph V) :=
  {p : Finset F.edgeSet × Finset F.edgeSet //
    p.2 ⊆ p.1 ∧ (((spanningSubgraph F) ((edgeSetOf F) p.1)) ⊘ (edgeSetOf F) p.2).IsLoopless}

noncomputable instance (F : SimpleGraph V) [Finite V] [Fintype F.edgeSet] :
    Fintype (DelContrIndex F) := Fintype.ofFinite _

/-- The number of vertices of the minor of `F` produced by a summation index. -/
noncomputable def DelContrIndex.size {F : SimpleGraph V} (i : (DelContrIndex F)) : ℕ :=
  Nat.card (fromEdgeSet ((edgeSetOf F) i.1.2)).ConnectedComponent

theorem DelContrIndex.size_le [Finite V] {F : SimpleGraph V} (i : (DelContrIndex F)) :
    i.size ≤ Nat.card V := card_connectedComponent_le _

/-- The minor `F_s ⊘ L` of `F` produced by a summation index, transported to a graph over
`Fin _` so that `SimpleGraph.mem_cl_of_determines` applies to it. -/
noncomputable def DelContrIndex.graph [Finite V] {F : SimpleGraph V} (i : (DelContrIndex F)) :
    SimpleGraph (Fin i.size) :=
  SimpleGraph.map (Finite.equivFin _)
    ((((spanningSubgraph F) ((edgeSetOf F) i.1.1)) ⊘ (edgeSetOf F) i.1.2).toSimpleGraph i.2.2)

/-- The graph attached to a summation index is isomorphic to the quotient it names. -/
theorem DelContrIndex.nonempty_iso [Finite V] {F : SimpleGraph V} (i : (DelContrIndex F)) :
    Nonempty ((toLoopGraph i.graph) ≃lg
      (((spanningSubgraph F) ((edgeSetOf F) i.1.1)) ⊘ (edgeSetOf F) i.1.2)) :=
  ⟨(Iso.map (Finite.equivFin _) _).symm⟩

theorem DelContrIndex.homCount_graph [Finite V] [Finite W] {F : SimpleGraph V}
    (i : (DelContrIndex F)) (G : SimpleGraph W) :
    homCount i.graph G = LoopGraph.homCount
      (((spanningSubgraph F) ((edgeSetOf F) i.1.1)) ⊘ (edgeSetOf F) i.1.2) (toLoopGraph G) := by
  rw [← homCount_toLoopGraph]
  exact LoopGraph.homCount_congr_left i.nonempty_iso.some (toLoopGraph G)

/-- **`eq:del-contr`, as a linear combination**: `hom(F, Gᶜ)` is the signed sum, over the
summation indices that contribute, of the homomorphism counts from the corresponding minors of
`F`.  Every coefficient is `±1`, hence nonzero.

This is the form `thm:complement` uses: `SimpleGraph.exists_graphFamily` groups the indices by
isomorphism type, and `SimpleGraph.mem_cl_of_determines` then applies. -/
theorem homCount_compl_delContr [Finite V] [Finite W] (F : SimpleGraph V) [Fintype F.edgeSet]
    (G : SimpleGraph W) :
    (homCount F Gᶜ : ℤ) =
      ∑ i : (DelContrIndex F), (-1 : ℤ) ^ i.1.1.card * (homCount i.graph G : ℤ) := by
  classical
  set c : Finset F.edgeSet × Finset F.edgeSet → ℤ := fun p =>
    (LoopGraph.homCount (((spanningSubgraph F) ((edgeSetOf F) p.1)) ⊘ (edgeSetOf F) p.2)
      (toLoopGraph G) : ℤ) with hcdef
  -- Rewrite the right-hand side as a sum over those pairs `(s, L)` that contribute.
  have hright : ∑ i : (DelContrIndex F), (-1 : ℤ) ^ i.1.1.card * (homCount i.graph G : ℤ) =
      ∑ p ∈ Finset.univ.filter (fun p : Finset F.edgeSet × Finset F.edgeSet =>
        p.2 ⊆ p.1 ∧ (((spanningSubgraph F) ((edgeSetOf F) p.1)) ⊘ (edgeSetOf F) p.2).IsLoopless),
        (-1 : ℤ) ^ p.1.card * c p := by
    rw [Finset.sum_subtype (p := fun p : Finset F.edgeSet × Finset F.edgeSet =>
        p.2 ⊆ p.1 ∧ (((spanningSubgraph F) ((edgeSetOf F) p.1)) ⊘ (edgeSetOf F) p.2).IsLoopless)
      _ (fun x => Finset.mem_filter.trans (by simp)) (fun p => (-1 : ℤ) ^ p.1.card * c p)]
    exact Finset.sum_congr rfl fun i _ => by rw [DelContrIndex.homCount_graph]
  -- The omitted indices contribute nothing.
  have hloop : ∑ p ∈ Finset.univ.filter (fun p : Finset F.edgeSet × Finset F.edgeSet =>
        p.2 ⊆ p.1 ∧ (((spanningSubgraph F) ((edgeSetOf F) p.1)) ⊘ (edgeSetOf F) p.2).IsLoopless),
        (-1 : ℤ) ^ p.1.card * c p =
      ∑ p ∈ Finset.univ.filter (fun p : Finset F.edgeSet × Finset F.edgeSet => p.2 ⊆ p.1),
        (-1 : ℤ) ^ p.1.card * c p := by
    refine Finset.sum_subset (fun p hp => ?_) fun p hp hp' => ?_
    · rw [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, hp.2.1⟩
    · rw [Finset.mem_filter] at hp hp'
      have hz : c p = 0 := by
        rw [hcdef, Nat.cast_eq_zero]
        exact LoopGraph.homCount_eq_zero_of_not_isLoopless
          (fun hc => hp' ⟨hp.1, hp.2, hc⟩) (toLoopGraph_isLoopless G)
      rw [hz, mul_zero]
  rw [hright, hloop, homCount_compl F G, Finset.sum_filter, Fintype.sum_prod_type]
  -- Unfold the filtered sum over pairs into the iterated sum of `eq:del-contr`.
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext L
  simp

end SimpleGraph

end Lax871432Proofs
