/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Lax871432Proofs.Hom.Count
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Fin

/-!
# Lovász's homomorphism matrix lemma

Let `F` be a finite family of pairwise non-isomorphic graphs on at most `n` vertices which
represents every isomorphism class of graphs on at most `n` vertices.  Then the matrix
`M i j = hom(F i, F j)` is invertible.

This is the key ingredient in Lovász's theorem that homomorphism counts determine a finite
graph up to isomorphism; see `Lovasz/Basic.lean`.

## Proof outline

Following Grohe, *word2vec, node2vec, graph2vec, X2vec: Towards a theory of vector embeddings
of structured data*, Theorem 4.2:

1. **Factorisation.** Every homomorphism `F i →g F j` factors as a strongly surjective
   homomorphism onto its image followed by an injective homomorphism.  The image is
   isomorphic to a unique family member `F k`, and each such `f` admits exactly `aut(F k)`
   factorisations through `F k`.  Counting gives
   `hom(F i, F j) = ∑ k, surj(F i, F k) * aut(F k)⁻¹ * inj(F k, F j)`,
   that is `M = S * D⁻¹ * I` (`homMatrix_factorization`).
2. **Triangularity.** Order the family by `(|V|, |E|)`, refined to a linear order
   (`GraphFamily.exists_isCompatibleOrder`).  Then `S` is lower triangular
   (`surjMatrix_blockTriangular`) and `I` is upper triangular
   (`injMatrix_blockTriangular`), both with positive diagonal.
3. **Invertibility.** Triangular matrices with nonzero diagonal are invertible, and `D` is
   diagonal with positive entries, so `M` is a product of invertible matrices
   (`homMatrix_isUnit`).

## Main declarations

* `SimpleGraph.GraphFamily`: a finite indexed family of graphs on at most `n` vertices.
* `SimpleGraph.homMatrix`, `surjMatrix`, `injMatrix`, `autDiag`: the four matrices.
* `SimpleGraph.homMatrix_factorization`: `M = S * D⁻¹ * I`.
* `SimpleGraph.homMatrix_isUnit`: **Lovász's lemma**.
-/

namespace Lax871432Proofs

open _root_.SimpleGraph
open Lax871432.HomomorphismCounts

open Function

namespace SimpleGraph

/-! ### Graph families -/

/-- An *indexed graph family* of order `n`: a family of simple graphs indexed by `ι`, the
`i`-th of which has vertex set `Fin (size i)` for some `size i ≤ n`. -/
structure GraphFamily (n : ℕ) (ι : Type*) where
  /-- The number of vertices of the `i`-th graph. -/
  size : ι → ℕ
  /-- Every graph in the family has at most `n` vertices. -/
  size_le : ∀ i, size i ≤ n
  /-- The `i`-th graph of the family. -/
  graph : ∀ i, SimpleGraph (Fin (size i))

namespace GraphFamily

variable {n : ℕ} {ι : Type*} (F : GraphFamily n ι)

/-- Two indices carry isomorphic graphs. -/
def Iso (i j : ι) : Prop := Nonempty (F.graph i ≃g F.graph j)

/-- The graphs in the family are pairwise non-isomorphic. -/
def PairwiseNonIso : Prop := Pairwise fun i j => ¬ F.Iso i j

variable {F}

@[refl] theorem Iso.refl (i : ι) : F.Iso i i := ⟨RelIso.refl _⟩

theorem Iso.symm {i j : ι} (h : F.Iso i j) : F.Iso j i := ⟨h.some.symm⟩

theorem Iso.trans {i j k : ι} (h : F.Iso i j) (h' : F.Iso j k) : F.Iso i k :=
  ⟨h.some.trans h'.some⟩

theorem PairwiseNonIso.eq (hF : F.PairwiseNonIso) {i j : ι} (h : F.Iso i j) : i = j := by
  by_contra hne
  exact hF hne h

variable (F)

/-- The family represents every isomorphism class of graphs on at most `n` vertices. -/
def IsExhaustive : Prop :=
  ∀ m ≤ n, ∀ G : SimpleGraph (Fin m), ∃ i, Nonempty (G ≃g F.graph i)

end GraphFamily

variable {n : ℕ} {ι : Type*}

/-! ### The four matrices -/

section Matrices

variable (F : GraphFamily n ι)

/-- The homomorphism-count matrix `M i j = hom(F i, F j)`. -/
noncomputable def homMatrix : Matrix ι ι ℚ :=
  Matrix.of fun i j => (homCount (F.graph i) (F.graph j) : ℚ)

/-- The matrix counting strongly surjective homomorphisms, `S i j = surj(F i, F j)`. -/
noncomputable def surjMatrix : Matrix ι ι ℚ :=
  Matrix.of fun i j => (surjCount (F.graph i) (F.graph j) : ℚ)

/-- The matrix counting injective homomorphisms, `I i j = inj(F i, F j)`. -/
noncomputable def injMatrix : Matrix ι ι ℚ :=
  Matrix.of fun i j => (injCount (F.graph i) (F.graph j) : ℚ)

/-- The diagonal matrix of automorphism counts, `D = diag(aut(F i))`. -/
noncomputable def autDiag [DecidableEq ι] : Matrix ι ι ℚ :=
  Matrix.diagonal fun i => (autCount (F.graph i) : ℚ)

@[simp] theorem homMatrix_apply (i j : ι) :
    homMatrix F i j = (homCount (F.graph i) (F.graph j) : ℚ) := rfl

@[simp] theorem surjMatrix_apply (i j : ι) :
    surjMatrix F i j = (surjCount (F.graph i) (F.graph j) : ℚ) := rfl

@[simp] theorem injMatrix_apply (i j : ι) :
    injMatrix F i j = (injCount (F.graph i) (F.graph j) : ℚ) := rfl

end Matrices

/-! ### The image index -/

section ImageIndex

variable (F : GraphFamily n ι)

/-- The image of a homomorphism between members of an exhaustive family is isomorphic to a
member of the family. -/
theorem exists_iso_imageGraph (hF : F.IsExhaustive) {i j : ι} (f : F.graph i →g F.graph j) :
    ∃ k : ι, Nonempty ((Hom.imageGraph f) ≃g F.graph k) := by
  have hle : Nat.card (Hom.range f).verts ≤ n :=
    le_trans (Nat.card_le_card_of_injective (Subtype.val : (Hom.range f).verts → _)
      Subtype.val_injective) (by simpa using F.size_le j)
  obtain ⟨k, hk⟩ := hF _ hle (SimpleGraph.map (Finite.equivFin _) (Hom.imageGraph f))
  exact ⟨k, ⟨(Iso.map (Finite.equivFin _) (Hom.imageGraph f)).trans hk.some⟩⟩

/-- Every finite graph with at most `n` vertices is isomorphic to a member of an exhaustive
family of order `n`. -/
theorem GraphFamily.exists_iso (hF : F.IsExhaustive) {V : Type*} [Finite V] (G : SimpleGraph V)
    (hV : Nat.card V ≤ n) : ∃ i, Nonempty (G ≃g F.graph i) := by
  obtain ⟨i, hi⟩ := hF _ hV (SimpleGraph.map (Finite.equivFin V) G)
  exact ⟨i, ⟨(Iso.map (Finite.equivFin V) G).trans hi.some⟩⟩

/-- The index of the family member isomorphic to the image of `f`. -/
noncomputable def imageIndex (hF : F.IsExhaustive) {i j : ι} (f : F.graph i →g F.graph j) : ι :=
  (exists_iso_imageGraph F hF f).choose

theorem imageIndex_spec (hF : F.IsExhaustive) {i j : ι} (f : F.graph i →g F.graph j) :
    Nonempty ((Hom.imageGraph f) ≃g F.graph (imageIndex F hF f)) :=
  (exists_iso_imageGraph F hF f).choose_spec

/-- The image index of `g ∘ h` is `k` whenever `h : F i →g F k` is strongly surjective and
`g : F k →g F j` is injective. -/
theorem imageIndex_comp (hni : F.PairwiseNonIso) (hF : F.IsExhaustive) {i j k : ι}
    {h : F.graph i →g F.graph k} (hh : (Hom.IsStrongSurjective h)) {g : F.graph k →g F.graph j}
    (hg : Injective g) : imageIndex F hF (g.comp h) = k := by
  refine hni.eq (⟨?_⟩ : F.Iso (imageIndex F hF (g.comp h)) k)
  exact (imageIndex_spec F hF (g.comp h)).some.symm.trans
    ((Subgraph.isoCoeOfEq (Hom.range_comp_of_isStrongSurjective g hh)).trans
      (g.isoImageGraph hg).symm)

end ImageIndex

/-! ### Step 1: the factorisation `M = S * D⁻¹ * I` -/

section Factorization

variable (F : GraphFamily n ι)

/-- For fixed `i j k`, the number of pairs consisting of a strongly surjective homomorphism
`F i →g F k` and an injective homomorphism `F k →g F j` equals `aut(F k)` times the number of
homomorphisms `F i →g F j` with image index `k`.

The group `Aut(F k)` acts simply transitively on the factorisations of a fixed homomorphism
by `σ • (h, g) = (σ ∘ h, g ∘ σ⁻¹)`, so all fibres of the composition map have exactly
`aut(F k)` elements. -/
theorem surjCount_mul_injCount (hni : F.PairwiseNonIso) (hF : F.IsExhaustive) (i j k : ι) :
    surjCount (F.graph i) (F.graph k) * injCount (F.graph k) (F.graph j) =
      autCount (F.graph k) *
        Nat.card {f : F.graph i →g F.graph j // imageIndex F hF f = k} := by
  classical
  -- The composition map from factorisations through `F k` to homomorphisms with image
  -- index `k`.
  set φ : {h : F.graph i →g F.graph k // (Hom.IsStrongSurjective h)} ×
      {g : F.graph k →g F.graph j // Injective g} →
      {f : F.graph i →g F.graph j // imageIndex F hF f = k} :=
    fun p => ⟨p.2.1.comp p.1.1, imageIndex_comp F hni hF p.1.2 p.2.2⟩ with hφ
  -- Every fibre of `φ` is in bijection with `Aut(F k)`.
  have hfibre : ∀ f, Nat.card {p // φ p = f} = autCount (F.graph k) := by
    intro f
    -- A base factorisation of `f`, obtained from an isomorphism `α` between the image of
    -- `f` and `F k`.
    obtain ⟨α⟩ : Nonempty ((Hom.imageGraph f.1) ≃g F.graph k) := by
      have h := imageIndex_spec F hF f.1; rwa [f.2] at h
    set h₀ : F.graph i →g F.graph k := α.toHom.comp (Hom.toRange f.1) with hh₀def
    set g₀ : F.graph k →g F.graph j := (Hom.range f.1).hom.comp α.symm.toHom with hg₀def
    have hh₀ : (Hom.IsStrongSurjective h₀) :=
      (Iso.isStrongSurjective α).comp (Hom.toRange_isStrongSurjective f.1)
    have hg₀ : Injective g₀ := fun a b hab =>
      α.symm.toEquiv.injective (Subtype.ext hab)
    have hfact : ∀ a, g₀ (h₀ a) = f.1 a := fun a => by
      simp [hh₀def, hg₀def, Subgraph.hom]
      exact Hom.coe_toRange _ _
    -- The action of `Aut(F k)` on factorisations.
    have hσs : ∀ σ : F.graph k ≃g F.graph k, (Hom.IsStrongSurjective (σ.toHom.comp h₀)) :=
      fun σ => (Iso.isStrongSurjective σ).comp hh₀
    have hσi : ∀ σ : F.graph k ≃g F.graph k, Injective (g₀.comp σ.symm.toHom) :=
      fun σ a b hab => σ.symm.toEquiv.injective (hg₀ hab)
    have hσφ : ∀ σ : F.graph k ≃g F.graph k,
        φ ⟨⟨σ.toHom.comp h₀, hσs σ⟩, ⟨g₀.comp σ.symm.toHom, hσi σ⟩⟩ = f := by
      intro σ
      refine Subtype.ext (DFunLike.ext _ _ fun a => ?_)
      change g₀ (σ.symm (σ (h₀ a))) = f.1 a
      rw [RelIso.symm_apply_apply]
      exact hfact a
    set bmap : (F.graph k ≃g F.graph k) → {p // φ p = f} :=
      fun σ => ⟨⟨⟨σ.toHom.comp h₀, hσs σ⟩, ⟨g₀.comp σ.symm.toHom, hσi σ⟩⟩, hσφ σ⟩ with hbmap
    have hbinj : Injective bmap := by
      intro σ τ hστ
      have hcomp : σ.toHom.comp h₀ = τ.toHom.comp h₀ := congrArg (fun p => p.1.1.1) hστ
      refine RelIso.ext fun v => ?_
      obtain ⟨a, rfl⟩ := hh₀.surjective v
      simpa using DFunLike.congr_fun hcomp a
    have hbsurj : Surjective bmap := by
      rintro ⟨⟨⟨h, hh⟩, ⟨g, hg⟩⟩, hφp⟩
      have hgh : ∀ a, g (h a) = f.1 a := fun a => DFunLike.congr_fun (congrArg Subtype.val hφp) a
      -- Right inverses of the two surjections `h₀` and `h`.
      set s := surjInv hh₀.surjective with hs
      set t := surjInv hh.surjective with ht
      have hs' : ∀ v, h₀ (s v) = v := surjInv_eq hh₀.surjective
      have ht' : ∀ v, h (t v) = v := surjInv_eq hh.surjective
      have hwd : ∀ a, h (s (h₀ a)) = h a := fun a => hg <| by
        rw [hgh, hgh, ← hfact, ← hfact, hs']
      have hwd' : ∀ a, h₀ (t (h a)) = h₀ a := fun a => hg₀ <| by
        rw [hfact, hfact, ← hgh, ← hgh, ht']
      -- The automorphism carrying the base factorisation to `(h, g)`.
      set σ : F.graph k ≃g F.graph k :=
        { toEquiv :=
            { toFun v := h (s v)
              invFun w := h₀ (t w)
              left_inv v := by change h₀ (t (h (s v))) = v; rw [hwd' (s v), hs']
              right_inv w := by change h (s (h₀ (t w))) = w; rw [hwd (t w), ht'] }
          map_rel_iff' := by
            intro u v
            change (F.graph k).Adj (h (s u)) (h (s v)) ↔ (F.graph k).Adj u v
            refine ⟨fun hadj => ?_, fun hadj => ?_⟩
            · obtain ⟨a, b, hab, ha, hb⟩ := hh.exists_adj hadj
              have hau : h₀ a = u := hg₀ <| by rw [hfact, ← hgh, ha, hgh, ← hfact, hs']
              have hbv : h₀ b = v := hg₀ <| by rw [hfact, ← hgh, hb, hgh, ← hfact, hs']
              exact hau ▸ hbv ▸ h₀.map_adj hab
            · obtain ⟨a, b, hab, ha, hb⟩ := hh₀.exists_adj hadj
              rw [← ha, ← hb, hwd, hwd]
              exact h.map_adj hab } with hσdef
      refine ⟨σ, Subtype.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))⟩
      · exact DFunLike.ext _ _ fun a => hwd a
      · refine DFunLike.ext _ _ fun w => ?_
        change g₀ (h₀ (t w)) = g w
        rw [hfact, ← hgh, ht']
    calc Nat.card {p // φ p = f}
        = Nat.card (F.graph k ≃g F.graph k) :=
          (Nat.card_congr (Equiv.ofBijective bmap ⟨hbinj, hbsurj⟩)).symm
      _ = autCount (F.graph k) := rfl
  -- Partition the pairs into the fibres of `φ`.
  haveI : Fintype {f : F.graph i →g F.graph j // imageIndex F hF f = k} := Fintype.ofFinite _
  have hpart : Nat.card ({h : F.graph i →g F.graph k // (Hom.IsStrongSurjective h)} ×
      {g : F.graph k →g F.graph j // Injective g}) =
      ∑ f, Nat.card {p // φ p = f} := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr
      { toFun p := ⟨φ p, p, rfl⟩
        invFun x := x.2.1
        left_inv _ := rfl
        right_inv := by rintro ⟨_, p, rfl⟩; rfl }
  rw [surjCount, injCount, ← Nat.card_prod, hpart]
  simp [hfibre, Finset.card_univ, ← Nat.card_eq_fintype_card, mul_comm]

variable [Fintype ι]

/-- The homomorphism count decomposes over the possible images. -/
theorem homCount_eq_sum_card_imageIndex (hF : F.IsExhaustive) (i j : ι) :
    homCount (F.graph i) (F.graph j) =
      ∑ k, Nat.card {f : F.graph i →g F.graph j // imageIndex F hF f = k} := by
  rw [homCount, ← Nat.card_sigma]
  exact Nat.card_congr
    { toFun f := ⟨imageIndex F hF f, f, rfl⟩
      invFun x := x.2.1
      left_inv _ := rfl
      right_inv := by rintro ⟨_, f, rfl⟩; rfl }

/-- The factorisation identity over `ℚ`:
`hom(F i, F j) = ∑ k, surj(F i, F k) * aut(F k)⁻¹ * inj(F k, F j)`. -/
theorem homCount_eq_weighted_sum (hni : F.PairwiseNonIso) (hF : F.IsExhaustive) (i j : ι) :
    (homCount (F.graph i) (F.graph j) : ℚ) =
      ∑ k, (surjCount (F.graph i) (F.graph k) : ℚ) * (autCount (F.graph k) : ℚ)⁻¹ *
        (injCount (F.graph k) (F.graph j) : ℚ) := by
  rw [homCount_eq_sum_card_imageIndex F hF i j, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have haut : (autCount (F.graph k) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (autCount_ne_zero _)
  rw [eq_comm, mul_right_comm, ← div_eq_mul_inv, div_eq_iff haut, ← Nat.cast_mul,
    ← Nat.cast_mul, Nat.cast_inj]
  exact (surjCount_mul_injCount F hni hF i j k).trans (mul_comm _ _)

variable [DecidableEq ι]

/-- **Step 1**: `M = S * D⁻¹ * I`. -/
theorem homMatrix_factorization (hni : F.PairwiseNonIso) (hF : F.IsExhaustive) :
    homMatrix F = surjMatrix F * (autDiag F)⁻¹ * injMatrix F := by
  have haut : ∀ k : ι, (autCount (F.graph k) : ℚ) ≠ 0 := fun k =>
    Nat.cast_ne_zero.2 (autCount_ne_zero _)
  have hinv : (autDiag F)⁻¹ = Matrix.diagonal fun k => (autCount (F.graph k) : ℚ)⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [autDiag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg _ (funext fun k => mul_inv_cancel₀ (haut k))
  ext i j
  rw [homMatrix_apply, Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, hinv, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, surjMatrix_apply, injMatrix_apply]
  exact homCount_eq_weighted_sum F hni hF i j

end Factorization

/-! ### Step 2: a compatible order, and triangularity -/

section Triangularity

/-- A linear order on the index type is *compatible* with `F` if `i < j` implies that `F i`
has fewer vertices than `F j`, or as many vertices and at most as many edges.

The informal proof orders the family by the product order on `(|V|, |E|)`, which is only a
partial order; `Matrix.BlockTriangular` needs a linear order, and the condition above is what
a linear refinement retains. -/
def GraphFamily.IsCompatibleOrder (F : GraphFamily n ι) [LinearOrder ι] : Prop :=
  ∀ i j : ι, i < j → F.size i < F.size j ∨
    (F.size i = F.size j ∧ Nat.card (F.graph i).edgeSet ≤ Nat.card (F.graph j).edgeSet)

/-- Every finite graph family admits a compatible linear order: order lexicographically by
number of vertices, then by number of edges, then by an arbitrary tie-break. -/
theorem GraphFamily.exists_isCompatibleOrder [Finite ι] (F : GraphFamily n ι) :
    ∃ _ : LinearOrder ι, F.IsCompatibleOrder := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  set e := Fintype.equivFin ι with he
  set key : ι → ℕ ×ₗ (ℕ ×ₗ ℕ) :=
    fun i => toLex (F.size i, toLex (Nat.card (F.graph i).edgeSet, (e i : ℕ))) with hkeydef
  have hkey : Injective key := fun i j hij => by
    have h : (e i : ℕ) = (e j : ℕ) :=
      congrArg (fun p : ℕ ×ₗ (ℕ ×ₗ ℕ) => (ofLex (ofLex p).2).2) hij
    exact e.injective (Fin.val_injective h)
  refine ⟨LinearOrder.lift' key hkey, fun i j hij => ?_⟩
  have hlt : key i < key j := hij
  rcases Prod.Lex.lt_iff.1 hlt with h | ⟨h₁, h₂⟩
  · exact Or.inl h
  · refine Or.inr ⟨h₁, ?_⟩
    rcases Prod.Lex.lt_iff.1 h₂ with h | ⟨h₃, -⟩
    · exact le_of_lt h
    · exact le_of_eq h₃

variable (F : GraphFamily n ι) [LinearOrder ι]

/-- **`S` is lower triangular**: there is no strongly surjective homomorphism `F i →g F j`
when `i < j`, since such a homomorphism forces `F j` to have at most as many vertices as
`F i`, and equality would make `F i` and `F j` isomorphic. -/
theorem surjMatrix_blockTriangular (hni : F.PairwiseNonIso) (hord : F.IsCompatibleOrder) :
    (surjMatrix F).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hij' : i < j := hij
  suffices h : IsEmpty {f : F.graph i →g F.graph j // (Hom.IsStrongSurjective f)} by
    simp [surjMatrix, surjCount, Nat.card_of_isEmpty]
  refine ⟨fun ⟨f, hf⟩ => ?_⟩
  have hv : F.size j ≤ F.size i := by
    simpa using Nat.card_le_card_of_surjective _ hf.surjective
  rcases hord i j hij' with h | ⟨h, -⟩
  · omega
  · exact absurd (hni.eq (nonempty_iso_of_isStrongSurjective hf (by simp [h]))) hij'.ne

/-- **`I` is upper triangular**: there is no injective homomorphism `F i →g F j` when
`j < i`, since such a homomorphism forces `F i` to have at most as many vertices and edges as
`F j`, and equality in both would make `F i` and `F j` isomorphic. -/
theorem injMatrix_blockTriangular (hni : F.PairwiseNonIso) (hord : F.IsCompatibleOrder) :
    (injMatrix F).BlockTriangular id := by
  intro i j (hij : j < i)
  suffices h : IsEmpty {f : F.graph i →g F.graph j // Injective f} by
    simp [injMatrix, injCount, Nat.card_of_isEmpty]
  refine ⟨fun ⟨f, hf⟩ => ?_⟩
  have hv : F.size i ≤ F.size j := by
    simpa using Nat.card_le_card_of_injective _ hf
  rcases hord j i hij with h | ⟨h, he⟩
  · omega
  · have hle := card_edgeSet_le_of_injective hf
    exact absurd (hni.eq (nonempty_iso_of_injective hf (by simp [h]) (le_antisymm hle he)))
      hij.ne'

end Triangularity

/-! ### Step 3: invertibility -/

section Invertibility

variable (F : GraphFamily n ι)

/-- The diagonal of `S` is positive: the identity is strongly surjective. -/
theorem surjMatrix_diag_pos (i : ι) : 0 < surjMatrix F i i := by
  rw [surjMatrix_apply, Nat.cast_pos, surjCount]
  haveI : Nonempty {f : F.graph i →g F.graph i // (Hom.IsStrongSurjective f)} :=
    ⟨⟨Hom.id, Hom.isStrongSurjective_id _⟩⟩
  exact Nat.card_pos

/-- The diagonal of `I` is positive: the identity is injective. -/
theorem injMatrix_diag_pos (i : ι) : 0 < injMatrix F i i := by
  rw [injMatrix_apply, Nat.cast_pos, injCount]
  haveI : Nonempty {f : F.graph i →g F.graph i // Injective f} := ⟨⟨Hom.id, injective_id⟩⟩
  exact Nat.card_pos

variable [Fintype ι] [DecidableEq ι]

/-- `D` is invertible: every automorphism count is positive. -/
theorem autDiag_isUnit : IsUnit (autDiag F) := by
  rw [Matrix.isUnit_iff_isUnit_det, autDiag, Matrix.det_diagonal, isUnit_iff_ne_zero]
  refine ne_of_gt (Finset.prod_pos fun i _ => ?_)
  exact_mod_cast one_le_autCount (F.graph i)

variable [LinearOrder ι]

/-- `S` is invertible: it is lower triangular with positive diagonal. -/
theorem surjMatrix_isUnit (hni : F.PairwiseNonIso) (hord : F.IsCompatibleOrder) :
    IsUnit (surjMatrix F) := by
  rw [Matrix.isUnit_iff_isUnit_det,
    Matrix.det_of_isLowerTriangular _ (surjMatrix_blockTriangular F hni hord), isUnit_iff_ne_zero]
  exact ne_of_gt (Finset.prod_pos fun i _ => surjMatrix_diag_pos F i)

/-- `I` is invertible: it is upper triangular with positive diagonal. -/
theorem injMatrix_isUnit (hni : F.PairwiseNonIso) (hord : F.IsCompatibleOrder) :
    IsUnit (injMatrix F) := by
  rw [Matrix.isUnit_iff_isUnit_det,
    Matrix.det_of_isUpperTriangular (injMatrix_blockTriangular F hni hord), isUnit_iff_ne_zero]
  exact ne_of_gt (Finset.prod_pos fun i _ => injMatrix_diag_pos F i)

/-- **Lovász's homomorphism matrix lemma**, given a compatible order.  See
`SimpleGraph.homMatrix_isUnit` for the version that constructs the order. -/
theorem homMatrix_isUnit_of_isCompatibleOrder (hni : F.PairwiseNonIso) (hF : F.IsExhaustive)
    (hord : F.IsCompatibleOrder) : IsUnit (homMatrix F) := by
  rw [homMatrix_factorization F hni hF]
  exact ((surjMatrix_isUnit F hni hord).mul
    (Matrix.isUnit_nonsing_inv_iff.2 (autDiag_isUnit F))).mul (injMatrix_isUnit F hni hord)

end Invertibility

/-- **Lovász's homomorphism matrix lemma**: for a finite family of pairwise non-isomorphic
graphs on at most `n` vertices representing every isomorphism class, the matrix of
homomorphism counts is invertible. -/
theorem homMatrix_isUnit [Fintype ι] [DecidableEq ι] (F : GraphFamily n ι)
    (hni : F.PairwiseNonIso) (hF : F.IsExhaustive) : IsUnit (homMatrix F) := by
  obtain ⟨_, hord⟩ := F.exists_isCompatibleOrder
  exact homMatrix_isUnit_of_isCompatibleOrder F hni hF hord

end SimpleGraph

end Lax871432Proofs
