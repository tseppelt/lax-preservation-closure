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

/-- **Component decomposition of homomorphism counts**: `hom(F, G) = ∏_c hom(c, G)`, the
product ranging over the connected components `c` of `F`. -/
theorem homCount_eq_prod_connectedComponent (F : SimpleGraph α) (G : SimpleGraph W)
    [Fintype F.ConnectedComponent] :
    homCount F G = ∏ c : F.ConnectedComponent, homCount c.toSimpleGraph G := by
  rw [homCount, Nat.card_congr (Hom.piConnectedComponentEquiv F G), Nat.card_pi]
  rfl

/-- Distributing a product of binary sums over all `Bool`-valued choice functions. -/
private theorem prod_add_eq_sum_prod_bool {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℕ) :
    ∏ i, (a i + b i) = ∑ s : ι → Bool, ∏ i, if s i then a i else b i := by
  have h : ∀ i : ι, a i + b i = ∑ j : Bool, if j then a i else b i := fun i => by simp
  rw [Finset.prod_congr rfl fun i _ => h i, Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- **Homomorphism counts into a disjoint union**: splitting `F` into connected components and
choosing, for each component, which summand it maps into. -/
theorem homCount_sum_right [Finite α] [Finite β] [Finite γ]
    (F : SimpleGraph α) (G : SimpleGraph β) (H : SimpleGraph γ)
    [Fintype F.ConnectedComponent] [DecidableEq F.ConnectedComponent] :
    homCount F (G ⊕g H) =
      ∑ s : F.ConnectedComponent → Bool, ∏ c : F.ConnectedComponent,
        if s c then homCount c.toSimpleGraph G else homCount c.toSimpleGraph H := by
  rw [homCount_eq_prod_connectedComponent]
  rw [Finset.prod_congr rfl fun c _ =>
    homCount_sum_right_of_connected c.connected_toSimpleGraph G H]
  exact prod_add_eq_sum_prod_bool _ _

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

/-- Every union of connected components of `F` admits a homomorphism into `F`. -/
theorem homCount_sigmaOn_connectedComponent_pos {α : Type*} [Finite α] (F : SimpleGraph α)
    (s : Set F.ConnectedComponent) :
    0 < homCount (sigmaOn s fun c : F.ConnectedComponent => c.toSimpleGraph) F :=
  homCount_pos_iff.2
    ⟨(Iso.sigmaConnectedComponent F).toHom.comp (Hom.sigmaOnIncl s _)⟩

end SimpleGraph

end Lax871432Proofs
