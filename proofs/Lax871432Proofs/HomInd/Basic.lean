/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Lax871432Proofs.Hom.DisjUnion
import Lax871432Proofs.Lovasz.Basic
import Lax871432.DistinguishingClosure
import Lax871432.GraphProducts
import Lax871432.PreservationProperties

/-!
# Graph classes, homomorphism indistinguishability, and the distinguishing closure

For a class `𝓕` of finite simple graphs, two graphs `G` and `H` are *homomorphism
indistinguishable over `𝓕`* if `hom(F, G) = hom(F, H)` for every `F ∈ 𝓕`.  Following
Roberson, *Oddomorphisms and homomorphism indistinguishability over graph classes* (2022),
the *homomorphism distinguishing closure* of `𝓕` is

  `cl 𝓕 = {K | ∀ G H, G ≡[𝓕] H → hom(K, G) = hom(K, H)}`,

the largest class with the same homomorphism indistinguishability relation as `𝓕`.

## Implementation notes

A class of graphs cannot be a `Set` of graphs: graphs live over arbitrary vertex types.
Instead a `GraphClass` is an isomorphism-invariant predicate on the finite simple graphs over
a vertex type in `Type`, which makes isomorphism invariance structural rather than a
hypothesis carried around.  Fixing `Type` is no loss of generality — every finite graph is
isomorphic to one of the form `SimpleGraph (Fin m)` — and it is forced: a `Type*` in a
structure field becomes a parameter of `GraphClass`, which would tie a class to a single
universe.

Coefficients are taken in `ℚ` rather than `ℝ`; since homomorphism counts are natural numbers
this is no restriction, and it matches `SimpleGraph.homMatrix`.

`SimpleGraph.GraphClass.cl` is built from the one-field structure
`SimpleGraph.GraphClass.Determines` rather than from the underlying `∀`-statement directly.
This matters: `GraphClass.cl` is an anonymous structure instance, so writing the quantifier
inline would make `𝓕.cl.Mem F` reduce — by delta on `Mem` and iota on the projection — to a
`∀` whose leading binders are implicit and instance-implicit.  Every `exact`, `by_cases` or
argument position mentioning such a hypothesis is then eta-expanded by the elaborator, which
duplicates the telescope and strands the `Finite` instances as unresolved metavariables.  A
structure application is never a `Pi`, so the reduction stops and all of that disappears.

## Main declarations

* `SimpleGraph.GraphClass`: a class of finite simple graphs.
* `SimpleGraph.HomIndistinguishable`, notation `G ≡[𝓕] H`.
* `SimpleGraph.GraphClass.Determines`: having one's homomorphism counts determined by `≡[𝓕]`.
* `SimpleGraph.GraphClass.cl`: the homomorphism distinguishing closure.
* `SimpleGraph.GraphClass.IsHomDistinguishingClosed`: `cl 𝓕 = 𝓕`.
* `SimpleGraph.mem_cl_of_determines`: **`lem:lincomb`**, the workhorse for deducing closure
  properties of `cl 𝓕` from preservation properties of `≡[𝓕]`.

## References

* Roberson, *Oddomorphisms and homomorphism indistinguishability over graph classes* (2022).
* Curticapean, Dell, Marx, *Homomorphisms are a good basis for counting small subgraphs*
  (2017), Lemma 3.6.
-/

namespace Lax871432Proofs

open scoped Lax871432.GraphProducts

open _root_.SimpleGraph
open Lax871432.GraphFamilies Lax871432.HomomorphismCounts Lax871432.LovaszTheorem
open Lax871432.HomomorphismIndistinguishability Lax871432.DistinguishingClosure
open Lax871432.IsomorphismRelaxations Lax871432.PreservationProperties
open scoped Lax871432.HomomorphismIndistinguishability

open Function

namespace SimpleGraph

/-! ### Graph classes

`GraphClass` and `HomIndistinguishable` are the concept
`Lax871432.HomomorphismIndistinguishability`; only the order on graph classes is added here.
-/

/-- One graph class is contained in another. -/
instance : LE GraphClass :=
  ⟨fun 𝓕 𝓖 => ∀ ⦃V : Type⦄ [Finite V] (F : SimpleGraph V), 𝓕.Mem F → 𝓖.Mem F⟩

variable {𝓕 𝓖 : GraphClass} {α V W : Type} [Finite α] [Finite V] [Finite W]
  {G : SimpleGraph V} {H : SimpleGraph W}

/-! ### Basic properties of membership -/

/-- Membership in a graph class is invariant under isomorphism. -/
theorem GraphClass.Mem_congr (𝓕 : GraphClass) (e : G ≃g H) : 𝓕.Mem G ↔ 𝓕.Mem H :=
  𝓕.mem_congr ⟨e⟩

/-! ### Basic properties of homomorphism indistinguishability -/

/-- Homomorphism indistinguishability may be tested against graphs over arbitrary finite
vertex types. -/
theorem homIndistinguishable_iff_forall_mem (𝓕 : GraphClass) (G : SimpleGraph V)
    (H : SimpleGraph W) :
    (G ≡[𝓕] H) ↔ ∀ {β : Type} [Finite β] (F : SimpleGraph β), 𝓕.Mem F →
      homCount F G = homCount F H := by
  constructor
  · intro h β _ F hF
    rw [homCount_congr_left (Iso.map (Finite.equivFin β) F) G,
      homCount_congr_left (Iso.map (Finite.equivFin β) F) H]
    exact h _ ((GraphClass.Mem_congr 𝓕 (Iso.map (Finite.equivFin β) F)).1 hF)
  · intro h _ F hF
    exact h F hF

@[refl]
theorem HomIndistinguishable.refl (𝓕 : GraphClass) (G : SimpleGraph V) : G ≡[𝓕] G :=
  fun _ _ _ => rfl

/-- A larger class distinguishes more graphs. -/
theorem HomIndistinguishable.mono (hle : 𝓕 ≤ 𝓖) (h : G ≡[𝓖] H) : G ≡[𝓕] H :=
  fun _ F hF => h F (hle F hF)

/-- **`eq:product`, class form**: homomorphism indistinguishability is preserved by taking the
categorical product with a fixed graph.  This is the key input to `mem_cl_of_determines`. -/
theorem HomIndistinguishable.catProd (h : G ≡[𝓕] H) {β : Type} [Finite β]
    (K : SimpleGraph β) : (G ×g K) ≡[𝓕] (H ×g K) := by
  intro _ F hF
  rw [homCount_catProd_right, homCount_catProd_right, h F hF]

/-! ### The homomorphism distinguishing closure -/

/-- To place a graph in `cl 𝓕` it suffices to determine its homomorphism counts into graphs
over arbitrary finite vertex types.  Converse of `SimpleGraph.homCount_eq_of_Mem_cl`. -/
theorem GraphClass.Mem_cl_of_forall (𝓕 : GraphClass) {K : SimpleGraph α}
    (h : ∀ {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W),
      (G ≡[𝓕] H) → homCount K G = homCount K H) :
    (cl 𝓕).Mem K :=
  ⟨fun G H hGH => h G H hGH⟩

/-- Membership in `cl 𝓕` determines homomorphism counts into any two related graphs. -/
theorem homCount_eq_of_Mem_cl {K : SimpleGraph α} (h : (cl 𝓕).Mem K) (hGH : G ≡[𝓕] H) :
    homCount K G = homCount K H :=
  h.homCount_eq G H hGH

/-- `cl` is extensive. -/
theorem GraphClass.le_cl (𝓕 : GraphClass) : 𝓕 ≤ (cl 𝓕) := by
  intro _ _ F hF
  exact ⟨fun G H hGH => (homIndistinguishable_iff_forall_mem 𝓕 G H).1 hGH F hF⟩

/-- `≡[𝓕]` and `≡[cl 𝓕]` are the same relation: this is the sense in which `cl 𝓕` is the
largest class with the same homomorphism indistinguishability relation as `𝓕`. -/
theorem homIndistinguishable_cl_iff (𝓕 : GraphClass) (G : SimpleGraph V) (H : SimpleGraph W) :
    (G ≡[(cl 𝓕)] H) ↔ (G ≡[𝓕] H) :=
  ⟨fun h => HomIndistinguishable.mono (GraphClass.le_cl 𝓕) h, fun h _ _ hF => homCount_eq_of_Mem_cl hF h⟩

/-- `cl` is idempotent. -/
theorem GraphClass.cl_cl (𝓕 : GraphClass) : (cl (cl 𝓕)) ≤ (cl 𝓕) := by
  intro _ _ K hK
  exact ⟨fun G H hGH => hK.homCount_eq G H ((homIndistinguishable_cl_iff 𝓕 G H).2 hGH)⟩

/-! ### Determined linear combinations

`SimpleGraph.mem_cl_of_determines` is `lem:lincomb`, the tool used throughout to turn a
preservation property of `≡[𝓕]` into a closure property of `cl 𝓕`.
-/

/-- **`lem:lincomb`, for an arbitrary relaxation**: suppose `R` is preserved under categorical
products, `L` is a finite family of pairwise non-isomorphic graphs and `α` assigns a nonzero
rational coefficient to each of them.  If `R` determines the linear combination
`∑ i, α i * hom(L i, -)`, then it determines each `hom(L i, -)` separately.

The proof multiplies the hypothesis by `hom(L i, K)` for all `K` on at most `n` vertices,
using `hprod` and `SimpleGraph.homCount_catProd_right`, and then inverts the homomorphism
matrix `SimpleGraph.homMatrix_isUnit`. -/
theorem determines_of_determines_sum {n : ℕ} {ι : Type} [Fintype ι] (R : GraphIsoRelaxation)
    (hprod : PreservedUnderCatProd R)
    (L : GraphFamily n ι) (hL : L.PairwiseNonIso) (α : ι → ℚ) (hα : ∀ i, α i ≠ 0)
    (hdet : ∀ {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W),
      R.Rel G H →
        ∑ i, α i * (homCount (L.graph i) G : ℚ) = ∑ i, α i * (homCount (L.graph i) H : ℚ))
    (i : ι) : Determines R (L.graph i) := by
  classical
  refine ⟨?_⟩
  intro V W _ _ G H hGH
  -- Work in the family `M` of representatives of *all* graphs on at most `n` vertices, whose
  -- homomorphism matrix is invertible.
  set M := repFamily n with hMdef
  haveI : Fintype (Quotient (boundedGraphSetoid n)) := Fintype.ofFinite _
  have hMni : M.PairwiseNonIso := repFamily_pairwiseNonIso n
  have hMex : M.IsExhaustive := repFamily_isExhaustive n
  -- Reindex `L` inside `M`: each `L j` is isomorphic to a unique member `M (ρ j)`.
  have hiso : ∀ j : ι, ∃ k, Nonempty (L.graph j ≃g M.graph k) := fun j =>
    GraphFamily.exists_iso M hMex (L.graph j) (by simpa using L.size_le j)
  set ρ : ι → Quotient (boundedGraphSetoid n) := fun j => (hiso j).choose with hρdef
  have hρ : ∀ j, Nonempty (L.graph j ≃g M.graph (ρ j)) := fun j => (hiso j).choose_spec
  have hρinj : Injective ρ := by
    intro a b hab
    refine GraphFamily.PairwiseNonIso.eq hL ⟨?_⟩
    have e := (hρ a).some
    rw [hab] at e
    exact e.trans (hρ b).some.symm
  -- Extend the coefficients by zero along `ρ`.
  set α' : Quotient (boundedGraphSetoid n) → ℚ := fun k => ∑ j, if ρ j = k then α j else 0
    with hα'def
  have hα'ρ : ∀ j, α' (ρ j) = α j := fun j => by
    simp only [hα'def, hρinj.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  -- The two linear combinations agree, term by term.
  have hreindex : ∀ {X : Type} [Finite X] (Y : SimpleGraph X),
      ∑ k, α' k * (homCount (M.graph k) Y : ℚ) = ∑ j, α j * (homCount (L.graph j) Y : ℚ) := by
    intro X _ Y
    simp only [hα'def, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [homCount_congr_left (hρ j).some Y]
  -- Multiplying by `hom(-, M l)` turns the hypothesis into a linear system.
  have hvec : Matrix.vecMul (fun k => α' k * (homCount (M.graph k) G : ℚ)) (homMatrix M) =
      Matrix.vecMul (fun k => α' k * (homCount (M.graph k) H : ℚ)) (homMatrix M) := by
    funext l
    have key := hdet (G ×g M.graph l) (H ×g M.graph l) (hprod G H (M.graph l) hGH)
    rw [← hreindex (G ×g M.graph l), ← hreindex (H ×g M.graph l)] at key
    simpa [Matrix.vecMul, dotProduct, homCount_catProd_right, mul_assoc] using key
  -- The homomorphism matrix of `M` is invertible, so the two vectors coincide.
  have huv := congrFun (Matrix.vecMul_injective_iff_isUnit.2 (homMatrix_isUnit M hMni hMex) hvec)
    (ρ i)
  rw [hα'ρ] at huv
  rw [homCount_congr_left (hρ i).some G, homCount_congr_left (hρ i).some H]
  exact_mod_cast mul_left_cancel₀ (hα i) huv

/-- **`lem:lincomb`**: the instance of `SimpleGraph.determines_of_determines_sum` for
homomorphism indistinguishability over a graph class, whose conclusion says that every member
of `L` lies in `cl 𝓕`. -/
theorem mem_cl_of_determines {n : ℕ} {ι : Type} [Fintype ι] (𝓕 : GraphClass)
    (L : GraphFamily n ι) (hL : L.PairwiseNonIso) (α : ι → ℚ) (hα : ∀ i, α i ≠ 0)
    (hdet : ∀ {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W),
      (G ≡[𝓕] H) →
        ∑ i, α i * (homCount (L.graph i) G : ℚ) = ∑ i, α i * (homCount (L.graph i) H : ℚ))
    (i : ι) : (cl 𝓕).Mem (L.graph i) :=
  determines_of_determines_sum (homIndRel 𝓕)
    (by intro V W X _ _ _ G H K h; exact HomIndistinguishable.catProd h K)
    L hL α hα (fun G H h => hdet G H h) i

/-- **`lem:lincomb`, with vanishing coefficients allowed.**  If a linear combination
`∑ i, α i * hom(L i, -)` over pairwise non-isomorphic graphs is determined by homomorphism
indistinguishability over `𝓕`, then every member with a *nonzero* coefficient lies in `cl 𝓕`.

`SimpleGraph.mem_cl_of_determines` is the special case where no coefficient vanishes; here the
family is first restricted to the support of `α`, which changes neither the linear combination
nor pairwise non-isomorphy. -/
theorem mem_cl_of_determines_of_ne_zero {n : ℕ} {ι : Type} [Fintype ι] (𝓕 : GraphClass)
    (L : GraphFamily n ι) (hL : L.PairwiseNonIso) (α : ι → ℚ)
    (hdet : ∀ {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W),
      (G ≡[𝓕] H) →
        ∑ i, α i * (homCount (L.graph i) G : ℚ) = ∑ i, α i * (homCount (L.graph i) H : ℚ))
    {i : ι} (hi : α i ≠ 0) : (cl 𝓕).Mem (L.graph i) := by
  classical
  haveI : Fintype {k : ι // α k ≠ 0} := Fintype.ofFinite _
  set M : GraphFamily n {k : ι // α k ≠ 0} :=
    { size := fun k => L.size k.1
      size_le := fun k => L.size_le k.1
      graph := fun k => L.graph k.1 } with hMdef
  -- Dropping the vanishing terms changes nothing.
  have hdrop : ∀ {V : Type} [Finite V] (G : SimpleGraph V),
      ∑ i, α i * (homCount (L.graph i) G : ℚ) =
        ∑ k : {k : ι // α k ≠ 0}, α k.1 * (homCount (M.graph k) G : ℚ) := by
    intro V _ G
    have h1 : ∑ i, α i * (homCount (L.graph i) G : ℚ) =
        ∑ i ∈ Finset.univ.filter (fun i => α i ≠ 0), α i * (homCount (L.graph i) G : ℚ) :=
      (Finset.sum_subset (Finset.filter_subset _ _) fun x _ hx => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hx
        rw [hx, zero_mul]).symm
    rw [h1, Finset.sum_subtype (p := fun i => α i ≠ 0) _ (fun x => by simp)
      (fun i => α i * (homCount (L.graph i) G : ℚ))]
  have hM : M.PairwiseNonIso := fun k k' hne hiso => hne (Subtype.ext (GraphFamily.PairwiseNonIso.eq hL hiso))
  have key : (cl 𝓕).Mem (M.graph ⟨i, hi⟩) := by
    refine mem_cl_of_determines 𝓕 M hM (fun k => α k.1) (fun k => k.2) ?_ ⟨i, hi⟩
    intro X Y _ _ G H hGH
    rw [← hdrop G, ← hdrop H]
    exact hdet G H hGH
  exact key

end SimpleGraph

end Lax871432Proofs
