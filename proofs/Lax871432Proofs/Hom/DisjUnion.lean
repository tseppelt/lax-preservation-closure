/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Lax871432Proofs.Hom.Basic
import Lax871432Proofs.Hom.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-!
# Homomorphism counts into a disjoint union

A homomorphism out of `F` is determined by its restrictions to the connected components of
`F`, and a homomorphism out of a connected graph into a disjoint union factors through one of
the two summands.  Combining the two gives, for graphs `F`, `G` and `H`,

  `hom(F, G ⊕g H) = ∑_{s : comp(F) → Bool} ∏_{c : comp(F)}
                      (if s c then hom(c, G) else hom(c, H))`

cf. Lovász, *Large Networks and Graph Limits* (2012), the discussion following (5.30).

## Main declarations

* `SimpleGraph.Hom.piConnectedComponentEquiv`: a homomorphism out of `F` is the same thing as
  a family of homomorphisms out of the connected components of `F`.
* `SimpleGraph.homCount_eq_prod_connectedComponent`: `hom(F, G) = ∏_c hom(c, G)`.
* `SimpleGraph.homCount_sum_right`: the displayed formula above.
* `SimpleGraph.homCount_sigma_sum_right`, `SimpleGraph.homCount_sum_right_eq_sum_powerset`:
  `eq:disjunion`, the same expansion indexed by subsets of the parts.
-/

namespace Lax871432Proofs

open _root_.SimpleGraph
open Lax871432.HomomorphismCounts

namespace SimpleGraph

variable {α β γ W : Type*}

/-- A homomorphism out of `F` is the same thing as a family of homomorphisms out of the
connected components of `F`. -/
noncomputable def Hom.piConnectedComponentEquiv (F : SimpleGraph α) (G : SimpleGraph W) :
    (F →g G) ≃ ∀ c : F.ConnectedComponent, (c.toSimpleGraph →g G) where
  toFun f c := f.comp c.toSimpleGraph_hom
  invFun := homOfConnectedComponents F
  left_inv f := by ext v; rfl
  right_inv π := by
    funext c
    ext ⟨v, hv⟩
    have hc : F.connectedComponentMk v = c := hv
    subst hc
    rfl

/-! ### `eq:disjunion` -/

/-- **`eq:disjunion`**: the number of homomorphisms from a disjoint union of connected graphs
into a disjoint union, expanded over the ways of distributing the parts between the two
summands. -/
theorem homCount_sigma_sum_right {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
    [∀ i, Finite (V i)] {D : ∀ i, SimpleGraph (V i)} (hD : ∀ i, (D i).Connected)
    {β γ : Type*} [Finite β] [Finite γ] (G : SimpleGraph β) (H : SimpleGraph γ) :
    homCount (SimpleGraph.sigma D) (G ⊕g H) =
      ∑ t : Finset ι, homCount (sigmaOn (↑t) D) G * homCount (sigmaOn (↑tᶜ) D) H := by
  rw [homCount_sigma]
  simp_rw [fun i => homCount_sum_right_of_connected (hD i) G H]
  rw [Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [homCount_sigmaOn_coe, homCount_sigmaOn_coe, ← Finset.compl_eq_univ_sdiff]

/-- **`eq:disjunion`**, in terms of the connected components of `F`. -/
theorem homCount_sum_right_eq_sum_powerset {α β γ : Type*} [Finite α] [Finite β] [Finite γ]
    (F : SimpleGraph α) (G : SimpleGraph β) (H : SimpleGraph γ)
    [Fintype F.ConnectedComponent] [DecidableEq F.ConnectedComponent] :
    homCount F (G ⊕g H) =
      ∑ t : Finset F.ConnectedComponent,
        homCount (sigmaOn (↑t) fun c : F.ConnectedComponent => c.toSimpleGraph) G *
          homCount (sigmaOn (↑tᶜ) fun c : F.ConnectedComponent => c.toSimpleGraph) H := by
  rw [homCount_congr_left (Iso.sigmaConnectedComponent F).symm (G ⊕g H)]
  exact homCount_sigma_sum_right (fun c => c.connected_toSimpleGraph) G H

end SimpleGraph

end Lax871432Proofs
