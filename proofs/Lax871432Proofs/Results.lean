/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Lax871432.ForbiddenMinors
import Lax871432.LinearCombinationLemma
import Lax871432.LovaszTheorem
import Lax871432.TakingSummands
import Lax871432Proofs.PreservationClosure.Complement
import Lax871432Proofs.PreservationClosure.Summands

/-!
# The results of the submission

This module collects the theorems the submission claims, each discharging one statement of
the concept package.  The mathematics is in the modules below it: `Lovasz` for Lovász's
theorem, `HomInd` for the distinguishing closure and the lemma on determined linear
combinations, and `PreservationClosure` for the two theorems of the paper.
-/

namespace Lax871432Proofs

open _root_.SimpleGraph
open Lax871432.HomomorphismCounts Lax871432.HomomorphismIndistinguishability
open Lax871432.DistinguishingClosure
open Lax871432.ClosureProperties Lax871432.PreservationProperties

open scoped Lax871432.HomomorphismIndistinguishability

/--
---
conclusion: Lax871432.LovaszTheorem.nonempty_iso_iff_forall_homCount_eq
---
Lovász's theorem.  The forward implication is the substantial one: it factors through the
invertibility of the homomorphism matrix of a family of representatives of all graphs on at
most `n` vertices, which follows from its factorisation into the surjective-homomorphism
matrix, the diagonal of automorphism counts, and the injective-homomorphism matrix, both
outer factors being triangular with positive diagonal.  The converse is the invariance of
homomorphism counts under isomorphism of the target.
-/
theorem lovasz {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W) :
    (∀ (m : ℕ) (K : SimpleGraph (Fin m)), homCount K G = homCount K H) ↔ Nonempty (G ≃g H) :=
  ⟨SimpleGraph.nonempty_iso_of_homCount_eq, fun ⟨e⟩ _ K => SimpleGraph.homCount_eq_of_iso e K⟩

/--
---
conclusion: Lax871432.LinearCombinationLemma.mem_cl_of_determines
---
A determined linear combination places its graphs in the distinguishing closure.  The proof
multiplies the hypothesis by `hom(L i, K)` for every `K` on at most `n` vertices — legitimate
because `≡[𝓕]` is preserved by the categorical product — and inverts the homomorphism matrix.

The bound `n` does not appear in the statement: the index type is finite, so the number of
vertices of the members of the family is bounded by the supremum of their sizes.
-/
theorem mem_cl_of_determines (𝓕 : GraphClass) {ι : Type} [Fintype ι] {size : ι → ℕ}
    (L : ∀ i, SimpleGraph (Fin (size i)))
    (hL : ∀ i j, i ≠ j → IsEmpty (L i ≃g L j))
    (α : ι → ℚ) (hα : ∀ i, α i ≠ 0)
    (hdet : ∀ {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W),
      (G ≡[𝓕] H) →
        ∑ i, α i * (homCount (L i) G : ℚ) = ∑ i, α i * (homCount (L i) H : ℚ))
    (i : ι) : (cl 𝓕).Mem (L i) := by
  classical
  let M : SimpleGraph.GraphFamily (Finset.univ.sup size) ι :=
    { size := size
      size_le := fun i => Finset.le_sup (Finset.mem_univ i)
      graph := L }
  have hni : M.PairwiseNonIso := fun i j hij ⟨e⟩ => (hL i j hij).false e
  exact (SimpleGraph.GraphClass.Mem_fin (cl 𝓕) (L i)).2
    (SimpleGraph.mem_cl_of_determines 𝓕 M hni α hα (fun G H h => hdet G H h) i)

/--
---
conclusion: Lax871432.TakingSummands.preservedUnderDisjointUnion_of_isSummandClosed
---
`thm:taking-summands`, (1) ⇒ (2).  Writing `F` as the disjoint union of its connected
components turns `hom(F, G + H)` into a sum, over the subsets of the components, of products
`hom(∐_{i ∈ t} C i, G) · hom(∐_{i ∉ t} C i, H)`.  Every graph occurring there is a summand of
`F`, hence in `𝓕`, so both sides are determined by `≡[𝓕]`.
-/
theorem preservedUnderDisjointUnion_of_isSummandClosed (𝓕 : GraphClass) :
    IsSummandClosed 𝓕 → PreservedUnderDisjointUnion 𝓕 :=
  fun h => SimpleGraph.GraphClass.IsSummandClosed.preservedUnderDisjointUnion h

/--
---
conclusion: Lax871432.TakingSummands.preservedUnderDisjointUnion_iff_cl_isSummandClosed
---
`thm:taking-summands`, (2) ⇔ (3).  Forwards, the same decomposition applied with `H := F`
exhibits a linear combination determined by `≡[𝓕]` whose coefficients `hom(∐_{i ∉ t} C i, F)`
are positive; after grouping the summands by isomorphism type the lemma on determined linear
combinations places every sub-union in `cl 𝓕`.  Backwards, (1) ⇒ (2) applied to `cl 𝓕`
suffices, since `≡[𝓕]` and `≡[cl 𝓕]` are the same relation.
-/
theorem preservedUnderDisjointUnion_iff_cl_isSummandClosed (𝓕 : GraphClass) :
    PreservedUnderDisjointUnion 𝓕 ↔ IsSummandClosed (cl 𝓕) :=
  SimpleGraph.GraphClass.preservedUnderDisjointUnion_iff_cl_isSummandClosed 𝓕

/--
---
conclusion: Lax871432.ForbiddenMinors.preservedUnderCompl_of_isMinorClosed
---
`thm:complement`, (1) ⇒ (2).  A minor-closed class is closed under deleting edges and under
contracting edges, and `hom(F, Ḡ)` is a signed sum of homomorphism counts from the graphs
obtained from `F` by deleting a set of edges and contracting another, all of which are minors
of `F`.
-/
theorem preservedUnderCompl_of_isMinorClosed (𝓕 : GraphClass) :
    IsMinorClosed 𝓕 → PreservedUnderCompl 𝓕 := fun h =>
  SimpleGraph.GraphClass.IsEdgeContractionClosed.preservedUnderCompl
    (SimpleGraph.GraphClass.IsMinorClosed.isEdgeDeletionClosed h)
    (SimpleGraph.GraphClass.IsMinorClosed.isEdgeContractionClosed h)

/--
---
conclusion: Lax871432.ForbiddenMinors.preservedUnderCompl_iff_cl_isMinorClosed
---
`thm:complement`, (2) ⇔ (3), the main result.  Forwards, the signed sum expressing
`hom(F, Ḡ)` is determined by `≡[𝓕]`; a coefficient analysis shows that the terms belonging to
a single edge deletion, respectively to a single edge contraction, cannot cancel, so `cl 𝓕`
is closed under deleting an edge and under contracting an edge, and these two operations
already generate all minors.  Backwards, (1) ⇒ (2) applied to `cl 𝓕`.
-/
theorem preservedUnderCompl_iff_cl_isMinorClosed (𝓕 : GraphClass) :
    PreservedUnderCompl 𝓕 ↔ IsMinorClosed (cl 𝓕) :=
  SimpleGraph.GraphClass.preservedUnderCompl_iff_cl_isMinorClosed 𝓕

end Lax871432Proofs
