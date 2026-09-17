/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finite.Sigma

/-!
# Indexed disjoint unions of graphs

Mathlib provides the binary disjoint union `G ⊕g H` of graphs.  This file introduces the
disjoint union `SimpleGraph.sigma G` of a family `G : ∀ i, SimpleGraph (V i)`, together with
the isomorphisms that reindex and split such a union, and the decomposition of a graph into
its connected components.

Homomorphism *counts* out of a disjoint union live in `Hom/Sigma.lean`.

## Main declarations

* `SimpleGraph.sigma`: the disjoint union of a family of graphs.
* `SimpleGraph.sigmaOn`: the disjoint union of the subfamily indexed by a set of indices.
* `SimpleGraph.Iso.sigmaConnectedComponent`: a graph is the disjoint union of its connected
  components.
* `SimpleGraph.Iso.sigmaCongrLeft`, `Iso.sigmaSum`, `Iso.sigmaSplit`: reindexing and splitting.
* `SimpleGraph.Hom.sigmaIncl`, `Hom.sigmaOnIncl`: the inclusions of a part and of a subfamily.

## Implementation notes

Adjacency in `SimpleGraph.sigma` is stated as an existential over a common index rather than
with a dependent rewrite `h ▸ ·`, which keeps the definition free of transports; see
`SimpleGraph.sigma_adj_mk` for the usable form.
-/

namespace Lax871432Proofs

open _root_.SimpleGraph

open Function

namespace SimpleGraph

universe u v

variable {ι : Type u} {V : ι → Type v} {W : Type*}

/-! ### The indexed disjoint union -/

/-- The disjoint union of a family of graphs.  Two vertices are adjacent when they lie in the
same part and are adjacent there. -/
protected def sigma (G : ∀ i, SimpleGraph (V i)) : SimpleGraph (Σ i, V i) where
  Adj p q := ∃ (i : ι) (a b : V i), (G i).Adj a b ∧ p = ⟨i, a⟩ ∧ q = ⟨i, b⟩
  symm := ⟨fun _ _ ⟨i, a, b, hab, hp, hq⟩ => ⟨i, b, a, hab.symm, hq, hp⟩⟩
  loopless := ⟨fun _ ⟨_, a, b, hab, hp, hq⟩ => by
    obtain rfl : a = b := eq_of_heq (Sigma.mk.injEq .. ▸ (hp.symm.trans hq)).2
    exact (G _).irrefl hab⟩

@[simp]
theorem sigma_adj_mk {G : ∀ i, SimpleGraph (V i)} {i : ι} {a b : V i} :
    (SimpleGraph.sigma G).Adj ⟨i, a⟩ ⟨i, b⟩ ↔ (G i).Adj a b := by
  refine ⟨fun ⟨j, c, d, hcd, hp, hq⟩ => ?_, fun h => ⟨i, a, b, h, rfl, rfl⟩⟩
  obtain rfl : i = j := congrArg Sigma.fst hp
  obtain rfl : a = c := eq_of_heq (Sigma.mk.injEq .. ▸ hp).2
  obtain rfl : b = d := eq_of_heq (Sigma.mk.injEq .. ▸ hq).2
  exact hcd

theorem sigma_adj_iff {G : ∀ i, SimpleGraph (V i)} {p q : Σ i, V i} :
    (SimpleGraph.sigma G).Adj p q ↔
      ∃ (i : ι) (a b : V i), (G i).Adj a b ∧ p = ⟨i, a⟩ ∧ q = ⟨i, b⟩ := Iff.rfl

/-- Adjacent vertices of a disjoint union lie in the same part. -/
theorem fst_eq_of_sigma_adj {G : ∀ i, SimpleGraph (V i)} {p q : Σ i, V i}
    (h : (SimpleGraph.sigma G).Adj p q) : p.1 = q.1 := by
  obtain ⟨i, a, b, -, rfl, rfl⟩ := h
  rfl

/-- The inclusion of the `i`-th part into the disjoint union. -/
def Hom.sigmaIncl (G : ∀ i, SimpleGraph (V i)) (i : ι) : G i →g SimpleGraph.sigma G where
  toFun a := ⟨i, a⟩
  map_rel' h := sigma_adj_mk.2 h

@[simp]
theorem Hom.sigmaIncl_apply (G : ∀ i, SimpleGraph (V i)) (i : ι) (a : V i) :
    Hom.sigmaIncl G i a = ⟨i, a⟩ := rfl

/-- The disjoint union of the subfamily of `G` indexed by the set `s`. -/
abbrev sigmaOn (s : Set ι) (G : ∀ i, SimpleGraph (V i)) : SimpleGraph (Σ i : s, V i) :=
  SimpleGraph.sigma fun i : s => G (i : ι)

/-! ### The decomposition into connected components -/

/-- The vertices of a graph are the disjoint union of the vertices of its connected
components. -/
def connectedComponentSigmaEquiv {α : Type*} (F : SimpleGraph α) :
    (Σ c : F.ConnectedComponent, c) ≃ α where
  toFun p := p.2.val
  invFun v := ⟨F.connectedComponentMk v, ⟨v, rfl⟩⟩
  left_inv := by
    rintro ⟨c, ⟨v, hv⟩⟩
    have hc : F.connectedComponentMk v = c := hv
    subst hc
    rfl
  right_inv _ := rfl

/-- A graph is the disjoint union of its connected components. -/
def Iso.sigmaConnectedComponent {α : Type*} (F : SimpleGraph α) :
    (SimpleGraph.sigma fun c : F.ConnectedComponent => c.toSimpleGraph) ≃g F where
  toEquiv := connectedComponentSigmaEquiv F
  map_rel_iff' {p q} := by
    constructor
    · intro h
      obtain ⟨c, x⟩ := p
      obtain ⟨d, y⟩ := q
      -- Adjacent vertices lie in the same component, so `c = d`.
      have hcd : c = d := by
        rw [← x.property, ← y.property]
        exact ConnectedComponent.eq.2 h.reachable
      subst hcd
      exact sigma_adj_mk.2 ((c.toSimpleGraph_adj x.property y.property).2 h)
    · rintro ⟨c, ⟨x, hx⟩, ⟨y, hy⟩, hadj, rfl, rfl⟩
      exact (c.toSimpleGraph_adj hx hy).1 hadj

theorem nonempty_iso_sigma_connectedComponent {α : Type*} (F : SimpleGraph α) :
    Nonempty (F ≃g SimpleGraph.sigma fun c : F.ConnectedComponent => c.toSimpleGraph) :=
  ⟨(Iso.sigmaConnectedComponent F).symm⟩

/-! ### Reindexing and splitting -/

/-- Reindexing a disjoint union along an equivalence of index types. -/
def Iso.sigmaCongrLeft {κ : Type*} (e : κ ≃ ι) (G : ∀ i, SimpleGraph (V i)) :
    (SimpleGraph.sigma fun k => G (e k)) ≃g SimpleGraph.sigma G where
  toEquiv := Equiv.sigmaCongrLeft e
  map_rel_iff' {p q} := by
    obtain ⟨i, a⟩ := p
    obtain ⟨j, b⟩ := q
    constructor
    · intro h
      obtain rfl : i = j := e.injective (fst_eq_of_sigma_adj h)
      exact (sigma_adj_mk (G := fun k => G (e k))).2 ((sigma_adj_mk (G := G)).1 h)
    · intro h
      obtain rfl : i = j := fst_eq_of_sigma_adj h
      exact (sigma_adj_mk (G := G)).2 ((sigma_adj_mk (G := fun k => G (e k))).1 h)

/-- A disjoint union indexed by a sum type splits as the disjoint union of the two parts. -/
def Iso.sigmaSum {κ κ' : Type u} {V : κ ⊕ κ' → Type v} (G : ∀ k, SimpleGraph (V k)) :
    SimpleGraph.sigma G ≃g
      ((SimpleGraph.sigma fun a => G (.inl a)) ⊕g SimpleGraph.sigma fun b => G (.inr b)) where
  toEquiv := Equiv.sumSigmaDistrib V
  map_rel_iff' {p q} := by
    obtain ⟨i, x⟩ := p
    obtain ⟨j, y⟩ := q
    cases i with
    | inl a =>
      cases j with
      | inl a' =>
        constructor
        · intro h
          obtain rfl : a = a' := fst_eq_of_sigma_adj h
          exact (sigma_adj_mk (G := G)).2 ((sigma_adj_mk (G := fun a => G (.inl a))).1 h)
        · intro h
          obtain rfl : a = a' := Sum.inl_injective (fst_eq_of_sigma_adj h)
          exact (sigma_adj_mk (G := fun a => G (.inl a))).2 ((sigma_adj_mk (G := G)).1 h)
      | inr b' =>
        exact ⟨fun h => absurd h (by simp),
          fun h => absurd (fst_eq_of_sigma_adj h) (by simp)⟩
    | inr b =>
      cases j with
      | inl a' =>
        exact ⟨fun h => absurd h (by simp),
          fun h => absurd (fst_eq_of_sigma_adj h) (by simp)⟩
      | inr b' =>
        constructor
        · intro h
          obtain rfl : b = b' := fst_eq_of_sigma_adj h
          exact (sigma_adj_mk (G := G)).2 ((sigma_adj_mk (G := fun b => G (.inr b))).1 h)
        · intro h
          obtain rfl : b = b' := Sum.inr_injective (fst_eq_of_sigma_adj h)
          exact (sigma_adj_mk (G := fun b => G (.inr b))).2 ((sigma_adj_mk (G := G)).1 h)

open scoped Classical in
/-- Splitting a disjoint union along a set of indices and its complement. -/
noncomputable def Iso.sigmaSplit (s : Set ι) (G : ∀ i, SimpleGraph (V i)) :
    SimpleGraph.sigma G ≃g (sigmaOn s G ⊕g sigmaOn sᶜ G) :=
  (Iso.sigmaCongrLeft (Equiv.sumCompl (· ∈ s)) G).symm.trans
    (Iso.sigmaSum fun k => G (Equiv.sumCompl (· ∈ s) k))

/-! ### Subfamilies -/

/-- The inclusion of a subfamily union into the union of the whole family. -/
def Hom.sigmaOnIncl (s : Set ι) (G : ∀ i, SimpleGraph (V i)) :
    sigmaOn s G →g SimpleGraph.sigma G where
  toFun p := ⟨p.1, p.2⟩
  map_rel' := by rintro _ _ ⟨k, c, d, hcd, rfl, rfl⟩; exact sigma_adj_mk.2 hcd

theorem nonempty_hom_sigmaOn_sigma (s : Set ι) (G : ∀ i, SimpleGraph (V i)) :
    Nonempty (sigmaOn s G →g SimpleGraph.sigma G) :=
  ⟨Hom.sigmaOnIncl s G⟩


end SimpleGraph

end Lax871432Proofs
