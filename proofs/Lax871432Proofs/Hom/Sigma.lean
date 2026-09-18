/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Lax871432Proofs.GraphTheory.Sigma
import Lax871432Proofs.Hom.Count

/-!
# Homomorphism counts out of indexed disjoint unions

The indexed form of Lovász, *Large Networks and Graph Limits* (2012), (5.28):

  `hom(∐ i, Gᵢ, K) = ∏ i, hom(Gᵢ, K)`.

The disjoint union itself is defined in `GraphTheory/Sigma.lean`.

## Main declarations

* `SimpleGraph.Hom.sigmaEquiv`: `(∐ i, Gᵢ →g K) ≃ ∀ i, (Gᵢ →g K)`.
* `SimpleGraph.homCount_sigma`: `hom(∐ i, Gᵢ, K) = ∏ i, hom(Gᵢ, K)`.
* `SimpleGraph.homCount_sigmaOn_coe`: the same for a subfamily indexed by a `Finset`.
-/

namespace Lax871432Proofs

open _root_.SimpleGraph
open Lax871432.HomomorphismCounts

open Function

namespace SimpleGraph

universe u v

variable {ι : Type u} {V : ι → Type v} {W : Type*}

/-! ### Homomorphism counts -/

/-- A homomorphism out of a disjoint union is the same thing as a family of homomorphisms out
of the parts. -/
def Hom.sigmaEquiv (G : ∀ i, SimpleGraph (V i)) (K : SimpleGraph W) :
    (SimpleGraph.sigma G →g K) ≃ ∀ i, (G i →g K) where
  toFun f i := f.comp (Hom.sigmaIncl G i)
  invFun π :=
    { toFun p := π p.1 p.2
      map_rel' := by rintro _ _ ⟨k, c, d, hcd, rfl, rfl⟩; exact (π k).map_adj hcd }
  left_inv _ := DFunLike.ext _ _ fun _ => rfl
  right_inv _ := funext fun _ => DFunLike.ext _ _ fun _ => rfl

/-- **(5.28), indexed form**: `hom(∐ i, Gᵢ, K) = ∏ i, hom(Gᵢ, K)`. -/
theorem homCount_sigma [Fintype ι] (G : ∀ i, SimpleGraph (V i)) (K : SimpleGraph W) :
    homCount (SimpleGraph.sigma G) K = ∏ i, homCount (G i) K := by
  rw [homCount, Nat.card_congr (Hom.sigmaEquiv G K), Nat.card_pi]
  rfl

/-- The homomorphism count out of a subfamily union indexed by a `Finset`. -/
theorem homCount_sigmaOn_coe (s : Finset ι) (G : ∀ i, SimpleGraph (V i)) (K : SimpleGraph W) :
    homCount (sigmaOn (↑s) G) K = ∏ i ∈ s, homCount (G i) K := by
  classical
  rw [homCount_sigma]
  simp only [Finset.coe_sort_coe, Finset.univ_eq_attach]
  exact Finset.prod_attach s fun i => homCount (G i) K

/-- Every sub-union of the parts of `∐ i, D i` maps into `∐ i, D i`, so its homomorphism count
there is positive. -/
theorem homCount_sigmaOn_sigma_pos [Finite ι] [∀ i, Finite (V i)]
    (D : ∀ i, SimpleGraph (V i)) (s : Set ι) :
    0 < homCount (sigmaOn s D) (SimpleGraph.sigma D) :=
  homCount_pos_iff.2 ⟨Hom.sigmaOnIncl s D⟩

end SimpleGraph

end Lax871432Proofs
