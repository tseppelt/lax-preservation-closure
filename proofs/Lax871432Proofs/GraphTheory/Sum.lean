/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# Structural facts about disjoint sums of graphs

Complements Mathlib's `Mathlib/Combinatorics/SimpleGraph/Sum.lean` with the facts about `⊕g`
needed to count homomorphisms out of a connected graph: adjacency, and hence reachability,
never crosses between the two summands, so a homomorphism from a connected graph lands
entirely in one of them.

Homomorphism *counts* live in `Hom/Basic.lean`.

## Main declarations

* `SimpleGraph.Walk.isLeft_eq_of_sum`: a walk in a disjoint sum stays on one side.
* `SimpleGraph.Hom.sumLeft`, `Hom.sumRight`: the component of a one-sided homomorphism.
-/

namespace Lax871432Proofs

open _root_.SimpleGraph

open Function

namespace SimpleGraph

variable {U V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph U}

/-! ### Walks and homomorphisms stay on one side -/

/-- Adjacent vertices of a disjoint sum lie on the same side. -/
theorem isLeft_eq_of_sum_adj {u v : V ⊕ W} (h : (G ⊕g H).Adj u v) : u.isLeft = v.isLeft := by
  cases u <;> cases v <;> simp_all

/-- The endpoints of a walk in a disjoint sum lie on the same side. -/
theorem Walk.isLeft_eq_of_sum : ∀ {u v : V ⊕ W}, (G ⊕g H).Walk u v → u.isLeft = v.isLeft
  | _, _, .nil => rfl
  | _, _, .cons h p => (isLeft_eq_of_sum_adj h).trans (Walk.isLeft_eq_of_sum p)

/-- A homomorphism from a connected graph into a disjoint sum maps every vertex to the
same side. -/
theorem Hom.isLeft_eq_of_connected (hK : K.Connected) (f : K →g G ⊕g H) (u v : U) :
    (f u).isLeft = (f v).isLeft := by
  obtain ⟨p⟩ := hK.preconnected u v
  exact (Walk.isLeft_eq_of_sum (p.map f))

/-- The left component of a homomorphism into a disjoint sum all of whose values lie on the
left. -/
def Hom.sumLeft (f : K →g G ⊕g H) (hf : ∀ v, (f v).isLeft) : K →g G where
  toFun v := (f v).getLeft (hf v)
  map_rel' {u v} h := by
    have hadj : (G ⊕g H).Adj (f u) (f v) := f.map_adj h
    rw [← Sum.inl_getLeft (f u) (hf u), ← Sum.inl_getLeft (f v) (hf v)] at hadj
    exact hadj

@[simp]
theorem Hom.inl_sumLeft (f : K →g G ⊕g H) (hf : ∀ v, (f v).isLeft) (v : U) :
    Sum.inl ((Hom.sumLeft f) hf v) = f v := Sum.inl_getLeft _ _

/-- The right component of a homomorphism into a disjoint sum all of whose values lie on the
right. -/
def Hom.sumRight (f : K →g G ⊕g H) (hf : ∀ v, (f v).isRight) : K →g H where
  toFun v := (f v).getRight (hf v)
  map_rel' {u v} h := by
    have hadj : (G ⊕g H).Adj (f u) (f v) := f.map_adj h
    rw [← Sum.inr_getRight (f u) (hf u), ← Sum.inr_getRight (f v) (hf v)] at hadj
    exact hadj

@[simp]
theorem Hom.inr_sumRight (f : K →g G ⊕g H) (hf : ∀ v, (f v).isRight) (v : U) :
    Sum.inr ((Hom.sumRight f) hf v) = f v := Sum.inr_getRight _ _


end SimpleGraph

end Lax871432Proofs
