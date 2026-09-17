/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Lax871432Proofs.GraphTheory.Prod
import Lax871432Proofs.GraphTheory.Sum
import Lax871432Proofs.Hom.Count
import Lax871432.GraphProducts

/-!
# Homomorphism counts of sums and categorical products

For simple graphs `F`, `G`, `H` and a connected graph `K`, the following identities hold,
cf. Lovász, *Large Networks and Graph Limits* (2012), (5.28)–(5.30):

* `hom(G ⊕g H, K) = hom(G, K) * hom(H, K)`, see `SimpleGraph.homCount_sum_left`;
* `hom(K, G ×g H) = hom(K, G) * hom(K, H)`, see `SimpleGraph.homCount_catProd_right`;
* `hom(K, G ⊕g H) = hom(K, G) + hom(K, H)` for connected `K`, see
  `SimpleGraph.homCount_sum_right_of_connected`.

Here `⊕g` is Mathlib's disjoint sum of graphs and `×g` is the categorical product, defined in
`GraphTheory/Prod.lean`; the structural facts about `⊕g` used below are in
`GraphTheory/Sum.lean`.

## Main declarations

* `SimpleGraph.Hom.sumEquiv`: `(G ⊕g H →g K) ≃ (G →g K) × (H →g K)`.
* `SimpleGraph.Hom.catProdEquiv`: `(K →g G ×g H) ≃ (K →g G) × (K →g H)`.
* `SimpleGraph.Hom.sumEquivOfConnected`: `(K →g G ⊕g H) ≃ (K →g G) ⊕ (K →g H)` for connected `K`.
-/

namespace Lax871432Proofs

open scoped Lax871432.GraphProducts

open _root_.SimpleGraph
open Lax871432.HomomorphismCounts

open Function

namespace SimpleGraph

variable {U V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph U}

/-! ### Homomorphisms out of a disjoint sum -/

/-- A homomorphism out of a disjoint sum `G ⊕g H` is the same thing as a pair of
homomorphisms, one out of `G` and one out of `H`. -/
def Hom.sumEquiv : (G ⊕g H →g K) ≃ (G →g K) × (H →g K) where
  toFun f := ⟨f.comp Embedding.sumInl.toHom, f.comp Embedding.sumInr.toHom⟩
  invFun p :=
    ⟨Sum.elim ⇑p.1 ⇑p.2, fun {u v} h => by
      cases u with
      | inl a => cases v with
        | inl b => exact p.1.map_rel' h
        | inr b => simp at h
      | inr a => cases v with
        | inl b => simp at h
        | inr b => exact p.2.map_rel' h⟩
  left_inv f := by ext (v | v) <;> rfl
  right_inv _ := rfl

/-- **(5.28)**: `hom(G ⊕g H, K) = hom(G, K) * hom(H, K)`. -/
theorem homCount_sum_left (G : SimpleGraph V) (H : SimpleGraph W) (K : SimpleGraph U) :
    homCount (G ⊕g H) K = homCount G K * homCount H K := by
  rw [homCount, homCount, homCount, ← Nat.card_prod]
  exact Nat.card_congr Hom.sumEquiv

/-! ### Homomorphisms into a categorical product -/

/-- A homomorphism into a categorical product `G ×g H` is the same thing as a pair of
homomorphisms, one into `G` and one into `H`. -/
def Hom.catProdEquiv : (K →g G ×g H) ≃ (K →g G) × (K →g H) where
  toFun f := ⟨(catProdFst G H).comp f, (catProdSnd G H).comp f⟩
  invFun p := ⟨fun v => (p.1 v, p.2 v), fun h => ⟨p.1.map_rel' h, p.2.map_rel' h⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **(5.29)**: `hom(K, G ×g H) = hom(K, G) * hom(K, H)`. -/
theorem homCount_catProd_right (K : SimpleGraph U) (G : SimpleGraph V) (H : SimpleGraph W) :
    homCount K (G ×g H) = homCount K G * homCount K H := by
  rw [homCount, homCount, homCount, ← Nat.card_prod]
  exact Nat.card_congr Hom.catProdEquiv

/-- Post-composition with the two inclusions into a disjoint sum. -/
def Hom.sumInclusion : (K →g G) ⊕ (K →g H) → (K →g G ⊕g H)
  | .inl g => Embedding.sumInl.toHom.comp g
  | .inr h => Embedding.sumInr.toHom.comp h

@[simp]
theorem Hom.sumInclusion_inl_apply (g : K →g G) (v : U) :
    Hom.sumInclusion (H := H) (.inl g) v = Sum.inl (g v) := rfl

@[simp]
theorem Hom.sumInclusion_inr_apply (h : K →g H) (v : U) :
    Hom.sumInclusion (G := G) (.inr h) v = Sum.inr (h v) := rfl

theorem Hom.sumInclusion_injective [Nonempty U] :
    Injective (Hom.sumInclusion (G := G) (H := H) (K := K)) := by
  have v₀ := Classical.arbitrary U
  rintro (g | g) (h | h) hgh
  · exact congrArg Sum.inl <| DFunLike.ext _ _ fun v => by
      simpa using DFunLike.congr_fun hgh v
  · exact absurd (DFunLike.congr_fun hgh v₀) (by simp)
  · exact absurd (DFunLike.congr_fun hgh v₀) (by simp)
  · exact congrArg Sum.inr <| DFunLike.ext _ _ fun v => by
      simpa using DFunLike.congr_fun hgh v

theorem Hom.sumInclusion_surjective (hK : K.Connected) :
    Surjective (Hom.sumInclusion (G := G) (H := H) (K := K)) := by
  obtain ⟨v₀⟩ := hK.nonempty
  intro f
  by_cases h : (f v₀).isLeft
  · have hf : ∀ v, (f v).isLeft := fun v => (Hom.isLeft_eq_of_connected hK f v v₀).trans h
    exact ⟨.inl ((Hom.sumLeft f) hf), by ext v; simp⟩
  · have hf : ∀ v, (f v).isRight := fun v => by
      rw [← Sum.not_isLeft, Hom.isLeft_eq_of_connected hK f v v₀]; simpa using h
    exact ⟨.inr ((Hom.sumRight f) hf), by ext v; simp⟩

theorem Hom.sumInclusion_bijective (hK : K.Connected) :
    Bijective (Hom.sumInclusion (G := G) (H := H) (K := K)) :=
  haveI := hK.nonempty
  ⟨Hom.sumInclusion_injective, Hom.sumInclusion_surjective hK⟩

/-- A homomorphism from a connected graph `K` into a disjoint sum factors through exactly one
of the two summands. -/
noncomputable def Hom.sumEquivOfConnected (hK : K.Connected) :
    (K →g G ⊕g H) ≃ (K →g G) ⊕ (K →g H) :=
  (Equiv.ofBijective _ (Hom.sumInclusion_bijective hK)).symm

/-- **(5.30)**: `hom(K, G ⊕g H) = hom(K, G) + hom(K, H)` for connected `K`. -/
theorem homCount_sum_right_of_connected [Finite U] [Finite V] [Finite W] (hK : K.Connected)
    (G : SimpleGraph V) (H : SimpleGraph W) :
    homCount K (G ⊕g H) = homCount K G + homCount K H := by
  rw [homCount, homCount, homCount, ← Nat.card_sum]
  exact Nat.card_congr (Hom.sumEquivOfConnected hK)

/-! ### Edgeless graphs and isolated vertices -/

/-- A homomorphism out of an edgeless graph is an arbitrary vertex map. -/
@[simps]
def Hom.botEquiv {α : Type*} (G : SimpleGraph V) : ((⊥ : SimpleGraph α) →g G) ≃ (α → V) where
  toFun f := ⇑f
  invFun f := ⟨f, fun h => absurd h (by simp)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `hom(⊥, G) = |V(G)|^{|V(⊥)|}`: an edgeless source imposes no condition.  Together with
`SimpleGraph.GraphClass.IsEdgeDeletionClosed` this is what makes homomorphism
indistinguishability determine the number of vertices. -/
theorem homCount_bot {α : Type*} [Finite α] (G : SimpleGraph V) :
    homCount (⊥ : SimpleGraph α) G = Nat.card V ^ Nat.card α := by
  rw [homCount, Nat.card_congr (Hom.botEquiv G), Nat.card_fun]

/-- The edges of `F` meeting the complement of `s`; deleting them isolates every vertex
outside `s`. -/
def incidenceEdges {α : Type*} (s : Set α) : Set (Sym2 α) := {e | ∃ t ∈ sᶜ, t ∈ e}

theorem notMem_incidenceEdges {α : Type*} {s : Set α} {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    s(x, y) ∉ incidenceEdges s := by
  rintro ⟨t, ht, hte⟩
  rcases Sym2.mem_iff.1 hte with rfl | rfl
  · exact ht hx
  · exact ht hy

theorem mem_of_notMem_incidenceEdges {α : Type*} {s : Set α} {x y : α}
    (h : s(x, y) ∉ incidenceEdges s) : x ∈ s ∧ y ∈ s :=
  ⟨not_not.1 fun hx => h ⟨x, hx, Sym2.mem_mk_left x y⟩,
    not_not.1 fun hy => h ⟨y, hy, Sym2.mem_mk_right x y⟩⟩

/-- A homomorphism out of `F` with all edges meeting `sᶜ` deleted is a homomorphism out of the
subgraph induced on `s`, together with arbitrary images for the vertices outside `s`. -/
noncomputable def Hom.deleteIncidenceEquiv {α : Type*} (F : SimpleGraph α) (s : Set α)
    (G : SimpleGraph V) :
    ((F.deleteEdges (incidenceEdges s)) →g G) ≃ ((F.induce s) →g G) × (↥sᶜ → V) := by
  classical
  exact
    { toFun f := ⟨⟨fun x => f x.1, fun {x y} h => f.map_rel (by
          rw [deleteEdges_adj]
          exact ⟨h, notMem_incidenceEdges x.2 y.2⟩)⟩, fun x => f x.1⟩
      invFun p := ⟨fun x => if hx : x ∈ s then p.1 ⟨x, hx⟩ else p.2 ⟨x, hx⟩, fun {x y} h => by
        rw [deleteEdges_adj] at h
        obtain ⟨hx, hy⟩ := mem_of_notMem_incidenceEdges h.2
        change G.Adj (if _ : x ∈ s then p.1 ⟨x, ‹x ∈ s›⟩ else p.2 ⟨x, ‹x ∉ s›⟩)
          (if _ : y ∈ s then p.1 ⟨y, ‹y ∈ s›⟩ else p.2 ⟨y, ‹y ∉ s›⟩)
        rw [dif_pos hx, dif_pos hy]
        exact p.1.map_rel h.1⟩
      left_inv f := by
        ext x
        by_cases hx : x ∈ s <;> simp
      right_inv p := by
        ext x
        · exact dif_pos x.2
        · exact dif_neg x.2 }

/-- **Splitting off the isolated vertices**: deleting every edge that meets `sᶜ` multiplies the
homomorphism count by `|V(G)|` once for each vertex outside `s`. -/
theorem homCount_deleteIncidence {α : Type*} [Finite α] [Finite V] (F : SimpleGraph α)
    (s : Set α) (G : SimpleGraph V) :
    homCount (F.deleteEdges (incidenceEdges s)) G =
      homCount (F.induce s) G * Nat.card V ^ Nat.card (↥sᶜ) := by
  rw [homCount, homCount, ← Nat.card_fun, ← Nat.card_prod]
  exact Nat.card_congr (Hom.deleteIncidenceEquiv F s G)

end SimpleGraph

end Lax871432Proofs
