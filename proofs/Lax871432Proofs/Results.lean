/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Lax871432.EdgeContractions
import Lax871432.ForbiddenMinors
import Lax871432.InducedSubgraphs
import Lax871432.LinearCombinationLemma
import Lax871432.ProductPreservation
import Lax871432.LovaszTheorem
import Lax871432.TakingSummands
import Lax871432Proofs.PreservationClosure.Complement
import Lax871432Proofs.PreservationClosure.LexProd
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
open Lax871432.IsomorphismRelaxations

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
  (SimpleGraph.tfae_homCount_eq (le_max_left (Nat.card V) (Nat.card W))
    (le_max_right (Nat.card V) (Nat.card W))).out 0 2

/--
---
conclusion: Lax871432.ProductPreservation.preservedUnderCatProd
---
Preservation under categorical products.  By the identity
`hom(F, G ×g K) = hom(F, G) · hom(F, K)`, which expresses that `×g` is the product in the
category of graphs and graph homomorphisms, both sides of the required equation pick up the
same factor `hom(F, K)`.
-/
theorem preservedUnderCatProd (𝓕 : GraphClass) :
    PreservedUnderCatProd (homIndRel 𝓕) := by
  intro V W X _ _ _ G H K h
  exact SimpleGraph.HomIndistinguishable.catProd h K

/--
---
conclusion: Lax871432.LinearCombinationLemma.determines_of_determines_sum
---
A determined linear combination determines its constituents.  Enlarge the family to a family
`M` of representatives of *all* graphs on at most `n` vertices, `n` being the supremum of the
sizes of the members, and extend the coefficients by zero.  Multiplying the hypothesis by
`hom(-, M k)` for each `k` — legitimate because `R` is preserved under categorical products —
turns it into the statement that a single vector meets the homomorphism matrix of `M` in the
same way for the two graphs.  That matrix is invertible, so the vectors agree coordinatewise,
and dividing by the nonzero coefficient gives the claim.
-/
theorem determines_of_determines_sum (R : GraphIsoRelaxation) (hprod : PreservedUnderCatProd R)
    {ι : Type} [Fintype ι] {size : ι → ℕ} (L : ∀ i, SimpleGraph (Fin (size i)))
    (hL : ∀ i j, i ≠ j → IsEmpty (L i ≃g L j))
    (α : ι → ℚ) (hα : ∀ i, α i ≠ 0)
    (hdet : ∀ {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W),
      R.Rel G H →
        ∑ i, α i * (homCount (L i) G : ℚ) = ∑ i, α i * (homCount (L i) H : ℚ))
    (i : ι) : Determines R (L i) := by
  classical
  let M : SimpleGraph.GraphFamily (Finset.univ.sup size) ι :=
    { size := size
      size_le := fun i => Finset.le_sup (Finset.mem_univ i)
      graph := L }
  have hni : M.PairwiseNonIso := fun i j hij ⟨e⟩ => (hL i j hij).false e
  exact SimpleGraph.determines_of_determines_sum R hprod M hni α hα (fun G H h => hdet G H h) i

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
    IsSummandClosed 𝓕 → PreservedUnderDisjointUnion (homIndRel 𝓕) :=
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
    PreservedUnderDisjointUnion (homIndRel 𝓕) ↔ IsSummandClosed (cl 𝓕) :=
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
    IsMinorClosed 𝓕 → PreservedUnderCompl (homIndRel 𝓕) := fun h =>
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
    PreservedUnderCompl (homIndRel 𝓕) ↔ IsMinorClosed (cl 𝓕) :=
  SimpleGraph.GraphClass.preservedUnderCompl_iff_cl_isMinorClosed 𝓕

/--
---
conclusion: Lax871432.InducedSubgraphs.preservedUnderLeftLexProd_of_isInducedSubgraphClosed
---
`prop:lexprod-indsub`, (1) ⇒ (2).  In the formula for `hom(F, G ⋅ H)` the factor depending on
`H` counts homomorphisms out of a disjoint union of subgraphs of `F` induced by the classes of
a partition.  Each of those induced subgraphs lies in `𝓕`, so none of them distinguishes `H`
from `H'`, and the counts agree summand by summand.
-/
theorem preservedUnderLeftLexProd_of_isInducedSubgraphClosed (𝓕 : GraphClass) :
    IsInducedSubgraphClosed 𝓕 → PreservedUnderLeftLexProd (homIndRel 𝓕) :=
  fun h => SimpleGraph.GraphClass.IsInducedSubgraphClosed.preservedUnderLeftLexProd h

/--
---
conclusion: Lax871432.EdgeContractions.preservedUnderRightLexProd_of_isContractionClosed
---
`prop:lexprod-contract`, (1) ⇒ (2).  In the formula for `hom(F, G ⋅ H)` the factor depending
on `G` counts homomorphisms out of a quotient `F / 𝓡`, which is a contraction of `F` and so
lies in `𝓕`.
-/
theorem preservedUnderRightLexProd_of_isContractionClosed (𝓕 : GraphClass) :
    IsContractionClosed 𝓕 → PreservedUnderRightLexProd (homIndRel 𝓕) :=
  fun h => SimpleGraph.GraphClass.IsContractionClosed.preservedUnderRightLexProd h

/--
---
conclusion: Lax871432.EdgeContractions.preservedUnderRightLexProd_iff_cl_isContractionClosed
---
`prop:lexprod-contract`, (2) ⇔ (3).  Forwards, take the right factor to be a complete graph on
the vertices of `F`: every coefficient `hom(∐ R ∈ 𝓡, F[R], K)` is then positive, since the
disjoint union of the classes is a graph on `V(F)` and maps into that complete graph.  The
formula therefore exhibits a linear combination of the counts from the quotients `F / 𝓡` that
`≡[𝓕]` determines, and the lemma on determined linear combinations places each quotient in
`cl 𝓕`; every contraction is such a quotient.  Backwards, (1) ⇒ (2) applied to `cl 𝓕`.
-/
theorem preservedUnderRightLexProd_iff_cl_isContractionClosed (𝓕 : GraphClass) :
    PreservedUnderRightLexProd (homIndRel 𝓕) ↔ IsContractionClosed (cl 𝓕) :=
  SimpleGraph.GraphClass.preservedUnderRightLexProd_iff_cl_isContractionClosed 𝓕

/--
---
conclusion: Lax871432.InducedSubgraphs.preservedUnderLeftLexProd_iff_cl_isInducedSubgraphClosed
---
`prop:lexprod-indsub`, (2) ⇔ (3).  Forwards, take the left factor to be a complete graph on
the vertices of `F`: every coefficient `hom(F / 𝓡, K)` is then positive, since a quotient of
`F` has at most as many vertices as `F`.  The formula therefore exhibits a linear combination
of the counts from the disjoint unions of the classes that `≡[𝓕]` determines, and the lemma on
determined linear combinations places each such disjoint union in `cl 𝓕`.  Applying this to
the partition whose classes are those of `F[U]` together with a singleton for each vertex
outside `U` gives `F[U]` with isolated vertices attached; `lem:minors` strips them off.
Backwards, (1) ⇒ (2) applied to `cl 𝓕`.
-/
theorem preservedUnderLeftLexProd_iff_cl_isInducedSubgraphClosed (𝓕 : GraphClass) :
    PreservedUnderLeftLexProd (homIndRel 𝓕) ↔ IsInducedSubgraphClosed (cl 𝓕) :=
  SimpleGraph.GraphClass.preservedUnderLeftLexProd_iff_cl_isInducedSubgraphClosed 𝓕

end Lax871432Proofs
