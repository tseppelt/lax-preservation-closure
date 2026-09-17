/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.SetTheory.Cardinal.Finite
import Lax871432.HomomorphismCounts

/-!
# Counting graph homomorphisms

This file introduces the four counting functions underlying the theory of homomorphism
indistinguishability:

* `SimpleGraph.homCount G H`: the number of homomorphisms `G →g H`;
* `SimpleGraph.surjCount G H`: the number of strongly surjective homomorphisms `G →g H`;
* `SimpleGraph.injCount G H`: the number of injective homomorphisms `G →g H`;
* `SimpleGraph.autCount G`: the number of automorphisms of `G`.

All four are defined using `Nat.card`, so that they carry no `Fintype` arguments and are
total: the count of an infinite type is `0`.

Along the way we introduce the image of a homomorphism as a subgraph of the target
(`SimpleGraph.Hom.range`) and the notion of a *strongly surjective* homomorphism
(`SimpleGraph.Hom.IsStrongSurjective`), namely one whose image is the whole target.  This is
strictly stronger than surjectivity on vertices: it additionally requires every edge of the
target to be the image of an edge of the source.

## Main declarations

* `SimpleGraph.Hom.range`: the image subgraph of a homomorphism.
* `SimpleGraph.Hom.IsStrongSurjective`: vertex- and edge-surjectivity.
* `SimpleGraph.homCount`, `surjCount`, `injCount`, `autCount`: the counting functions.
* `SimpleGraph.homCount_congr_left`, `homCount_congr_right`: isomorphism invariance.
-/

namespace Lax871432Proofs

open _root_.SimpleGraph
open Lax871432.HomomorphismCounts

open Function

instance RelHom.instFinite {α β : Type*} [Finite α] [Finite β]
    {r : α → α → Prop} {s : β → β → Prop} : Finite (r →r s) :=
  Finite.of_injective (fun f : r →r s => (f : α → β)) DFunLike.coe_injective

instance RelIso.instFinite {α β : Type*} [Finite α] [Finite β]
    {r : α → α → Prop} {s : β → β → Prop} : Finite (r ≃r s) :=
  Finite.of_injective (fun f : r ≃r s => (f : α → β)) fun _ _ h => RelIso.ext (congrFun h)

namespace SimpleGraph

variable {U V W : Type*} {F : SimpleGraph U} {G : SimpleGraph V} {H : SimpleGraph W}

/-! ### The image of a homomorphism -/

/-- The image of a homomorphism `f : G →g H`, as a subgraph of `H`.  Its vertices are the
image of the vertex set of `G` and its edges are the images of the edges of `G`.

This is in general a proper subgraph of the subgraph of `H` induced on `Set.range f`, since
`H` may have edges between vertices in the range that are not images of edges of `G`. -/
def Hom.range (f : G →g H) : H.Subgraph := Subgraph.map f ⊤

@[simp]
lemma Hom.range_verts (f : G →g H) : (Hom.range f).verts = Set.range f := by
  simp [Hom.range]

@[simp]
lemma Hom.range_adj (f : G →g H) {u v : W} :
    (Hom.range f).Adj u v ↔ ∃ a b, G.Adj a b ∧ f a = u ∧ f b = v := by
  simp [Hom.range, Subgraph.map, Relation.Map]

/-- The graph on the image of `f`, i.e. the coercion of `f.range` to a `SimpleGraph`. -/
abbrev Hom.imageGraph (f : G →g H) : SimpleGraph (Hom.range f).verts := (Hom.range f).coe

lemma Hom.imageGraph_adj (f : G →g H) {u v : (Hom.range f).verts} :
    (Hom.imageGraph f).Adj u v ↔ ∃ a b, G.Adj a b ∧ f a = (u : W) ∧ f b = (v : W) :=
  (Hom.range_adj f)

/-- The corestriction of `f : G →g H` to its image. -/
def Hom.toRange (f : G →g H) : G →g (Hom.imageGraph f) where
  toFun a := ⟨f a, by simp⟩
  map_rel' {a b} hab := (Hom.imageGraph_adj f).2 ⟨a, b, hab, rfl, rfl⟩

@[simp]
lemma Hom.coe_toRange (f : G →g H) (a : V) : ((Hom.toRange f) a : W) = f a := rfl

lemma Hom.toRange_surjective (f : G →g H) : Surjective (Hom.toRange f) := by
  rintro ⟨w, hw⟩
  rw [Hom.range_verts] at hw
  obtain ⟨a, rfl⟩ := hw
  exact ⟨a, rfl⟩

/-! ### Strongly surjective homomorphisms -/

/-- A homomorphism `f : G →g H` is *strongly surjective* if its image is all of `H`;
equivalently, if it is surjective on vertices and every edge of `H` is the image of an edge
of `G`.  See `SimpleGraph.Hom.isStrongSurjective_iff_range_eq_top`. -/
structure Hom.IsStrongSurjective (f : G →g H) : Prop where
  /-- A strongly surjective homomorphism is surjective on vertices. -/
  surjective : Surjective f
  /-- Every edge of the target is the image of an edge of the source. -/
  exists_adj : ∀ ⦃u v : W⦄, H.Adj u v → ∃ a b, G.Adj a b ∧ f a = u ∧ f b = v

namespace Hom

lemma isStrongSurjective_iff_range_eq_top {f : G →g H} :
    (Hom.IsStrongSurjective f) ↔ (Hom.range f) = ⊤ := by
  constructor
  · intro hf
    refine Subgraph.ext ?_ (funext fun u => funext fun v => propext ?_)
    · rw [Hom.range_verts, Subgraph.verts_top, Set.range_eq_univ]
      exact hf.surjective
    · rw [Hom.range_adj, Subgraph.top_adj]
      exact ⟨fun ⟨a, b, hab, ha, hb⟩ => ha ▸ hb ▸ f.map_rel' hab, fun h => hf.exists_adj h⟩
  · intro hf
    constructor
    · rw [← Set.range_eq_univ, ← Hom.range_verts, hf, Subgraph.verts_top]
    · intro u v huv
      have : (Hom.range f).Adj u v := by rw [hf]; exact Subgraph.top_adj.2 huv
      exact Hom.range_adj f |>.1 this

@[simp]
lemma isStrongSurjective_id (G : SimpleGraph V) : (Hom.IsStrongSurjective (Hom.id : G →g G)) :=
  ⟨surjective_id, fun _ _ h => ⟨_, _, h, rfl, rfl⟩⟩

lemma IsStrongSurjective.comp {X : Type*} {K : SimpleGraph X} {g : H →g K} {f : G →g H}
    (hg : (Hom.IsStrongSurjective g)) (hf : (Hom.IsStrongSurjective f)) : (Hom.IsStrongSurjective (g.comp f)) where
  surjective := hg.surjective.comp hf.surjective
  exists_adj u v huv := by
    obtain ⟨a, b, hab, ha, hb⟩ := hg.exists_adj huv
    obtain ⟨c, d, hcd, hc, hd⟩ := hf.exists_adj hab
    exact ⟨c, d, hcd, by simp [hc, ha], by simp [hd, hb]⟩

lemma toRange_isStrongSurjective (f : G →g H) : (Hom.IsStrongSurjective (Hom.toRange f)) where
  surjective := (Hom.toRange_surjective f)
  exists_adj := by
    rintro u v ⟨a, b, hab, ha, hb⟩
    exact ⟨a, b, hab, Subtype.ext ha, Subtype.ext hb⟩

end Hom

lemma Iso.isStrongSurjective (e : G ≃g H) : (Hom.IsStrongSurjective e.toHom) where
  surjective := e.toEquiv.surjective
  exists_adj u v huv :=
    ⟨e.symm u, e.symm v, e.symm.map_adj_iff.2 huv, e.apply_symm_apply u, e.apply_symm_apply v⟩

lemma Iso.injective_toHom (e : G ≃g H) : Injective e.toHom := e.toEquiv.injective

/-- Equal subgraphs have isomorphic coercions. -/
def Subgraph.isoCoeOfEq {S T : G.Subgraph} (h : S = T) : S.coe ≃g T.coe := by
  subst h; exact RelIso.refl _

/-- A homomorphism which is both injective and strongly surjective is an isomorphism. -/
noncomputable def Iso.ofInjectiveOfIsStrongSurjective (f : G →g H) (hinj : Injective f)
    (hsurj : (Hom.IsStrongSurjective f)) : G ≃g H where
  toEquiv := Equiv.ofBijective f ⟨hinj, hsurj.surjective⟩
  map_rel_iff' {a b} := by
    refine ⟨fun h => ?_, f.map_adj⟩
    obtain ⟨c, d, hcd, hc, hd⟩ := hsurj.exists_adj h
    exact hinj hc ▸ hinj hd ▸ hcd

lemma Hom.injective_toRange {f : G →g H} (hf : Injective f) : Injective (Hom.toRange f) :=
  fun _ _ h => hf (congrArg Subtype.val h)

/-- An injective homomorphism is an isomorphism onto its image. -/
noncomputable def Hom.isoImageGraph (f : G →g H) (hf : Injective f) : G ≃g (Hom.imageGraph f) :=
  Iso.ofInjectiveOfIsStrongSurjective (Hom.toRange f) (Hom.injective_toRange hf)
    (Hom.toRange_isStrongSurjective f)

/-- Precomposing with a strongly surjective homomorphism does not change the image. -/
theorem Hom.range_comp_of_isStrongSurjective {X : Type*} {K : SimpleGraph X} (g : H →g K)
    {f : G →g H} (hf : (Hom.IsStrongSurjective f)) : (Hom.range (g.comp f)) = (Hom.range g) := by
  refine Subgraph.ext ?_ (funext fun u => funext fun v => propext ?_)
  · simp [Set.range_comp, Set.range_eq_univ.2 hf.surjective]
  · simp only [Hom.range_adj]
    refine ⟨fun ⟨a, b, hab, ha, hb⟩ => ⟨f a, f b, f.map_adj hab, ha, hb⟩, ?_⟩
    rintro ⟨c, d, hcd, hc, hd⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hf.exists_adj hcd
    exact ⟨a, b, hab, by simp [ha, hc], by simp [hb, hd]⟩

/-! ### Edge counts under homomorphisms -/

/-- A strongly surjective homomorphism induces a surjection on edge sets. -/
theorem card_edgeSet_le_of_isStrongSurjective [Finite V] {f : G →g H}
    (hf : (Hom.IsStrongSurjective f)) : Nat.card H.edgeSet ≤ Nat.card G.edgeSet := by
  refine Nat.card_le_card_of_surjective
    (fun e : G.edgeSet => (⟨Sym2.map f e.1, f.map_mem_edgeSet e.2⟩ : H.edgeSet)) ?_
  rintro ⟨e, he⟩
  induction e using Sym2.ind with
  | h u v =>
    rw [mem_edgeSet] at he
    obtain ⟨a, b, hab, ha, hb⟩ := hf.exists_adj he
    exact ⟨⟨s(a, b), by rwa [mem_edgeSet]⟩, Subtype.ext (by simp [ha, hb])⟩

/-- An injective homomorphism induces an injection on edge sets. -/
theorem card_edgeSet_le_of_injective [Finite W] {f : G →g H} (hf : Injective f) :
    Nat.card G.edgeSet ≤ Nat.card H.edgeSet :=
  Nat.card_le_card_of_injective
    (fun e : G.edgeSet => (⟨Sym2.map f e.1, f.map_mem_edgeSet e.2⟩ : H.edgeSet))
    fun _ _ h => Subtype.ext (Sym2.map.injective hf (congrArg Subtype.val h))

/-- A strongly surjective homomorphism between graphs with equally many vertices is an
isomorphism. -/
theorem nonempty_iso_of_isStrongSurjective [Finite V] [Finite W] {f : G →g H}
    (hf : (Hom.IsStrongSurjective f)) (hcard : Nat.card V = Nat.card W) : Nonempty (G ≃g H) := by
  have : Injective f := by
    have := Nat.bijective_iff_surjective_and_card f |>.2 ⟨hf.surjective, hcard⟩
    exact this.1
  exact ⟨Iso.ofInjectiveOfIsStrongSurjective f this hf⟩

/-- An injective homomorphism between graphs with equally many vertices and equally many
edges is an isomorphism. -/
theorem nonempty_iso_of_injective [Finite V] [Finite W] {f : G →g H} (hf : Injective f)
    (hv : Nat.card V = Nat.card W) (he : Nat.card G.edgeSet = Nat.card H.edgeSet) :
    Nonempty (G ≃g H) := by
  have hsurj : Surjective f := (Nat.bijective_iff_injective_and_card f |>.2 ⟨hf, hv⟩).2
  refine ⟨Iso.ofInjectiveOfIsStrongSurjective f hf ⟨hsurj, fun u v huv => ?_⟩⟩
  -- The induced injection on edge sets is bijective, so `s(u, v)` has an edge preimage.
  have hbij : Bijective
      (fun e : G.edgeSet => (⟨Sym2.map f e.1, f.map_mem_edgeSet e.2⟩ : H.edgeSet)) :=
    Nat.bijective_iff_injective_and_card _ |>.2
      ⟨fun _ _ h => Subtype.ext (Sym2.map.injective hf (congrArg Subtype.val h)), he⟩
  obtain ⟨⟨e, he'⟩, heq⟩ := hbij.2 ⟨s(u, v), by rwa [mem_edgeSet]⟩
  have heq' : Sym2.map f e = s(u, v) := congrArg Subtype.val heq
  induction e using Sym2.ind with
  | h a b =>
    rw [mem_edgeSet] at he'
    simp only [Sym2.map_mk] at heq'
    rcases Sym2.eq_iff.1 heq' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨a, b, he', h₁, h₂⟩
    · exact ⟨b, a, he'.symm, h₂, h₁⟩

/-! ### The counting functions -/

/-- `surjCount G H` is the number of strongly surjective homomorphisms from `G` to `H`. -/
noncomputable def surjCount (G : SimpleGraph V) (H : SimpleGraph W) : ℕ :=
  Nat.card {f : G →g H // (Hom.IsStrongSurjective f)}

/-- `injCount G H` is the number of injective homomorphisms from `G` to `H`. -/
noncomputable def injCount (G : SimpleGraph V) (H : SimpleGraph W) : ℕ :=
  Nat.card {f : G →g H // Injective f}

/-- `autCount G` is the number of automorphisms of `G`. -/
noncomputable def autCount (G : SimpleGraph V) : ℕ := Nat.card (G ≃g G)

lemma homCount_eq_card [Fintype (G →g H)] : homCount G H = Fintype.card (G →g H) :=
  Nat.card_eq_fintype_card

/-- `injCount` agrees with Mathlib's `SimpleGraph.labelledCopyCount`, which counts the
labelled copies of `G` inside `H`. -/
lemma injCount_eq_labelledCopyCount [Fintype V] [Fintype W] :
    injCount G H = H.labelledCopyCount G := by
  classical
  rw [injCount, labelledCopyCount, Nat.card_eq_fintype_card]
  exact Fintype.card_congr ⟨fun f => ⟨f.1, f.2⟩, fun f => ⟨f.1, f.2⟩, fun _ => rfl, fun _ => rfl⟩

lemma surjCount_le_homCount [Finite V] [Finite W] : surjCount G H ≤ homCount G H :=
  Nat.card_le_card_of_injective _ Subtype.val_injective

lemma injCount_le_homCount [Finite V] [Finite W] : injCount G H ≤ homCount G H :=
  Nat.card_le_card_of_injective _ Subtype.val_injective

/-- A homomorphism count is positive exactly when a homomorphism exists. -/
lemma homCount_pos_iff [Finite V] [Finite W] : 0 < homCount G H ↔ Nonempty (G →g H) := by
  rw [homCount, Nat.card_pos_iff]
  exact and_iff_left inferInstance

/-- There is always at least one automorphism, the identity. -/
lemma one_le_autCount (G : SimpleGraph V) [Finite V] : 1 ≤ autCount G :=
  Nat.card_pos (α := G ≃g G)

lemma autCount_ne_zero (G : SimpleGraph V) [Finite V] : autCount G ≠ 0 :=
  Nat.one_le_iff_ne_zero.1 (one_le_autCount G)

/-! ### Isomorphism invariance -/

/-- Homomorphism counts only depend on the isomorphism type of the target. -/
theorem homCount_congr_right (K : SimpleGraph U) (e : G ≃g H) :
    homCount K G = homCount K H :=
  Nat.card_congr
    { toFun f := e.toHom.comp f
      invFun f := e.symm.toHom.comp f
      left_inv f := by ext a; simp
      right_inv f := by ext a; simp }

/-- Homomorphism counts only depend on the isomorphism types of both arguments. -/
theorem homCount_congr {V' W' : Type*} {G' : SimpleGraph V'} {H' : SimpleGraph W'}
    (e₁ : G ≃g G') (e₂ : H ≃g H') : homCount G H = homCount G' H' :=
  (homCount_congr_left e₁ H).trans (homCount_congr_right G' e₂)

end SimpleGraph

end Lax871432Proofs
