/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Lax871432Proofs.Lovasz.HomMatrix
import Mathlib.Data.List.TFAE

/-!
# Lovász's theorem

Two finite simple graphs `G` and `H` on at most `n` vertices are isomorphic if and only if
they are *homomorphism indistinguishable* over all graphs, and already if and only if they
are homomorphism indistinguishable over all graphs on at most `n` vertices.  This is
Lovász, *Operations with structures* (1967).

The three-way equivalence is `SimpleGraph.tfae_homCount_eq`; the substantial implication is
`SimpleGraph.nonempty_iso_of_homCount_eq_of_card_le`, which deduces an isomorphism from
finitely many homomorphism counts.  It rests on the invertibility of the homomorphism matrix,
`SimpleGraph.homMatrix_isUnit`, proved in `Lovasz/HomMatrix.lean`.

Test graphs are taken of the form `SimpleGraph (Fin m)` rather than over arbitrary vertex
types.  This is no restriction: `SimpleGraph.homCount_eq_of_forall_fin` transports the
statement to any finite graph, in any universe.

## Main declarations

* `SimpleGraph.repFamily`: the family of representatives of the isomorphism classes of graphs
  on at most `n` vertices.
* `SimpleGraph.GraphFamily.iso_of_homCount_eq`: within an exhaustive family of pairwise
  non-isomorphic graphs, equal homomorphism counts force equal indices.
* `SimpleGraph.nonempty_iso_of_homCount_eq_of_card_le`: Lovász's theorem, bounded form.
* `SimpleGraph.nonempty_iso_of_homCount_eq`: Lovász's theorem, unbounded form.
* `SimpleGraph.tfae_homCount_eq`: the three-way equivalence.
-/

namespace Lax871432Proofs

open _root_.SimpleGraph
open Lax871432.HomomorphismCounts Lax871432.LovaszTheorem

open Function

namespace SimpleGraph

variable {U V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-! ### Homomorphism indistinguishability is an isomorphism invariant -/

/-- Isomorphic graphs receive the same number of homomorphisms from every graph.  This is the
easy implication of Lovász's theorem. -/
theorem homCount_eq_of_iso (e : G ≃g H) (K : SimpleGraph U) : homCount K G = homCount K H :=
  homCount_congr_right K e

/-- Homomorphism counts from all graphs of the form `SimpleGraph (Fin m)` determine
homomorphism counts from every finite graph, in any universe. -/
theorem homCount_eq_of_forall_fin [Finite U] (K : SimpleGraph U)
    (h : ∀ (m : ℕ) (L : SimpleGraph (Fin m)), homCount L G = homCount L H) :
    homCount K G = homCount K H := by
  rw [homCount_congr_left (Iso.map (Finite.equivFin U) K) G,
    homCount_congr_left (Iso.map (Finite.equivFin U) K) H]
  exact h _ _

/-! ### The family of representatives of isomorphism classes -/

/-- Graphs on at most `n` vertices, packaged as a sigma type. -/
abbrev BoundedGraph (n : ℕ) : Type := Σ m : Fin (n + 1), SimpleGraph (Fin m.val)

/-- Isomorphism of graphs on at most `n` vertices. -/
def boundedGraphSetoid (n : ℕ) : Setoid (BoundedGraph n) where
  r p q := Nonempty (p.2 ≃g q.2)
  iseqv := ⟨fun _ => ⟨RelIso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩

instance (n : ℕ) : Finite (Quotient (boundedGraphSetoid n)) := Quotient.finite _

/-- The family of representatives of the isomorphism classes of graphs on at most `n`
vertices, indexed by those isomorphism classes. -/
noncomputable def repFamily (n : ℕ) : GraphFamily n (Quotient (boundedGraphSetoid n)) where
  size c := (Quotient.out c).1
  size_le c := Nat.lt_succ_iff.1 (Quotient.out c).1.isLt
  graph c := (Quotient.out c).2

theorem repFamily_pairwiseNonIso (n : ℕ) : (repFamily n).PairwiseNonIso := by
  intro i j hne hiso
  refine hne ?_
  have : Quotient.mk (boundedGraphSetoid n) (Quotient.out i) =
      Quotient.mk (boundedGraphSetoid n) (Quotient.out j) := Quotient.sound hiso
  rwa [Quotient.out_eq, Quotient.out_eq] at this

theorem repFamily_isExhaustive (n : ℕ) : (repFamily n).IsExhaustive := by
  intro m hm K
  refine ⟨Quotient.mk (boundedGraphSetoid n) ⟨⟨m, Nat.lt_succ_of_le hm⟩, K⟩, ?_⟩
  have h : (boundedGraphSetoid n).r
      (Quotient.out (Quotient.mk (boundedGraphSetoid n) ⟨⟨m, Nat.lt_succ_of_le hm⟩, K⟩))
      ⟨⟨m, Nat.lt_succ_of_le hm⟩, K⟩ := Quotient.exact (Quotient.out_eq _)
  exact ⟨h.some.symm⟩

/-! ### Lovász's theorem -/

/-- Within an exhaustive family of pairwise non-isomorphic graphs, two members receiving the
same number of homomorphisms from every member of the family are isomorphic.

The homomorphism matrix of the family is invertible, so it has trivial kernel; the hypothesis
says exactly that `eᵢ - eⱼ` lies in that kernel. -/
theorem GraphFamily.iso_of_homCount_eq {n : ℕ} {ι : Type*} [Finite ι]
    (F : GraphFamily n ι) (hni : F.PairwiseNonIso) (hF : F.IsExhaustive) {i j : ι}
    (h : ∀ k, homCount (F.graph k) (F.graph i) = homCount (F.graph k) (F.graph j)) :
    F.Iso i j := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have hmul : (homMatrix F).mulVec (Pi.single i 1 - Pi.single j 1) = 0 := by
    funext k
    simp only [Matrix.mulVec, dotProduct_sub, dotProduct_single_one, Pi.zero_apply,
      sub_eq_zero, homMatrix_apply]
    exact_mod_cast congrArg (Nat.cast (R := ℚ)) (h k)
  have hker : (Pi.single i 1 - Pi.single j 1 : ι → ℚ) = 0 :=
    Matrix.mulVec_injective_iff_isUnit.2 (homMatrix_isUnit F hni hF)
      (hmul.trans (Matrix.mulVec_zero _).symm)
  have hij : i = j := by
    by_contra hne
    have h1 : (Pi.single i 1 - Pi.single j 1 : ι → ℚ) i = 1 := by simp [hne]
    rw [hker] at h1
    exact one_ne_zero h1.symm
  exact hij ▸ GraphFamily.Iso.refl i

/-- **Lovász's theorem, bounded form**: two finite graphs with at most `n` vertices which
receive the same number of homomorphisms from every graph on at most `n` vertices are
isomorphic. -/
theorem nonempty_iso_of_homCount_eq_of_card_le [Finite V] [Finite W] {n : ℕ}
    (hV : Nat.card V ≤ n) (hW : Nat.card W ≤ n)
    (h : ∀ m ≤ n, ∀ K : SimpleGraph (Fin m), homCount K G = homCount K H) :
    Nonempty (G ≃g H) := by
  classical
  set F := repFamily n with hFdef
  have hni : F.PairwiseNonIso := repFamily_pairwiseNonIso n
  have hex : F.IsExhaustive := repFamily_isExhaustive n
  obtain ⟨i, ⟨φ⟩⟩ := GraphFamily.exists_iso F hex G hV
  obtain ⟨j, ⟨ψ⟩⟩ := GraphFamily.exists_iso F hex H hW
  have hfam : ∀ k, homCount (F.graph k) (F.graph i) = homCount (F.graph k) (F.graph j) := by
    intro k
    rw [← homCount_congr_right (F.graph k) φ, ← homCount_congr_right (F.graph k) ψ]
    exact h (F.size k) (F.size_le k) (F.graph k)
  exact ⟨φ.trans ((GraphFamily.iso_of_homCount_eq F hni hex hfam).some.trans ψ.symm)⟩

/-- **Lovász's theorem**: two finite graphs receiving the same number of homomorphisms from
every finite graph are isomorphic. -/
theorem nonempty_iso_of_homCount_eq [Finite V] [Finite W]
    (h : ∀ (m : ℕ) (K : SimpleGraph (Fin m)), homCount K G = homCount K H) :
    Nonempty (G ≃g H) :=
  nonempty_iso_of_homCount_eq_of_card_le (le_max_left _ _) (le_max_right _ _)
    fun _ _ K => h _ K

/-- **Lovász's theorem**, as the three-way equivalence of

1. homomorphism indistinguishability over all finite graphs,
2. homomorphism indistinguishability over all graphs on at most `n` vertices,
3. isomorphism,

for graphs `G` and `H` on at most `n` vertices. -/
theorem tfae_homCount_eq [Finite V] [Finite W] {n : ℕ} (hV : Nat.card V ≤ n)
    (hW : Nat.card W ≤ n) :
    List.TFAE
      [∀ (m : ℕ) (K : SimpleGraph (Fin m)), homCount K G = homCount K H,
       ∀ m ≤ n, ∀ K : SimpleGraph (Fin m), homCount K G = homCount K H,
       Nonempty (G ≃g H)] := by
  tfae_have 1 → 2 := fun h _ _ K => h _ K
  tfae_have 2 → 3 := nonempty_iso_of_homCount_eq_of_card_le hV hW
  tfae_have 3 → 1 := fun ⟨e⟩ _ K => homCount_eq_of_iso e K
  tfae_finish

end SimpleGraph

end Lax871432Proofs
