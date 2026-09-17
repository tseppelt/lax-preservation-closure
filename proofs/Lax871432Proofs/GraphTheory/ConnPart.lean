/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Lax871432Proofs.GraphTheory.Sigma
import Lax871432.Contractions

/-!
# Partitions of the vertices of a graph into connected parts

A `SimpleGraph.ConnPart F` is a partition of `V(F)`, given as a setoid, all of whose classes
induce connected subgraphs of `F`.  It carries the quotient `F / 𝓡`, a simple graph on the
classes, and the disjoint union `∐ R ∈ 𝓡, F[R]` of the subgraphs induced by the classes.

These are the index of the sum in `SimpleGraph.homCount_lexProd`, and the presentation of
`Lax871432.Contractions.IsContraction` by a quotient rather than by a projection.

## Main declarations

* `SimpleGraph.ConnPart`: a partition into connected parts.
* `SimpleGraph.ConnPart.quotientGraph`, `SimpleGraph.ConnPart.parts`: the two graphs it carries.
* `SimpleGraph.ConnPart.ofMap`: the partition into the connected components of the subgraph of
  `F` spanned by the edges whose endpoints a given map identifies.
* `SimpleGraph.isContraction_iff`: `K` is a contraction of `F` exactly when it is isomorphic
  to `F / 𝓡` for some `𝓡`.
-/

namespace Lax871432Proofs

open _root_.SimpleGraph

namespace SimpleGraph

variable {V : Type*}

/-! ### The subgraph spanned by the edges a map identifies -/

/-- The spanning subgraph of `F` consisting of those edges whose endpoints `p` sends to the
same value. -/
def fibreSubgraph (F : SimpleGraph V) {β : Type*} (p : V → β) : SimpleGraph V where
  Adj u v := F.Adj u v ∧ p u = p v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => F.irrefl h.1⟩

@[simp]
theorem fibreSubgraph_adj {F : SimpleGraph V} {β : Type*} {p : V → β} {u v : V} :
    (fibreSubgraph F p).Adj u v ↔ F.Adj u v ∧ p u = p v := Iff.rfl

theorem fibreSubgraph_le (F : SimpleGraph V) {β : Type*} (p : V → β) :
    fibreSubgraph F p ≤ F := fun _ _ h => h.1

/-- A walk in `F.fibreSubgraph p` keeps the value of `p`. -/
theorem eq_of_reachable_fibreSubgraph {F : SimpleGraph V} {β : Type*} {p : V → β} {u v : V}
    (h : (fibreSubgraph F p).Reachable u v) : p u = p v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hab _ ih => exact (fibreSubgraph_adj.1 hab).2.trans ih

/-! ### Partitions into connected parts -/

/-- A partition of the vertices of `F`, all of whose classes induce connected subgraphs. -/
structure ConnPart (F : SimpleGraph V) where
  /-- The partition, as an equivalence relation on the vertices. -/
  setoid : Setoid V
  /-- Every class induces a connected subgraph of `F`. -/
  connected : ∀ a : Quotient setoid, (F.induce {v | Quotient.mk setoid v = a}).Connected

namespace ConnPart

variable {F : SimpleGraph V} (𝓡 : ConnPart F)

/-- The class of a vertex. -/
def proj (v : V) : Quotient 𝓡.setoid := Quotient.mk 𝓡.setoid v

theorem proj_eq_iff {u v : V} : 𝓡.proj u = 𝓡.proj v ↔ 𝓡.setoid u v :=
  Quotient.eq (r := 𝓡.setoid)

/-- The subgraph of `F` induced by a class. -/
def part (a : Quotient 𝓡.setoid) : SimpleGraph {v | 𝓡.proj v = a} := F.induce _

/-- The quotient `F / 𝓡`: distinct classes are adjacent when `F` joins them. -/
def quotientGraph : SimpleGraph (Quotient 𝓡.setoid) where
  Adj a b := a ≠ b ∧ ∃ x y, F.Adj x y ∧ 𝓡.proj x = a ∧ 𝓡.proj y = b
  symm := ⟨fun _ _ h => by
    obtain ⟨hne, x, y, hxy, hx, hy⟩ := h
    exact ⟨hne.symm, y, x, hxy.symm, hy, hx⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp]
theorem quotientGraph_adj {a b : Quotient 𝓡.setoid} :
    𝓡.quotientGraph.Adj a b ↔ a ≠ b ∧ ∃ x y, F.Adj x y ∧ 𝓡.proj x = a ∧ 𝓡.proj y = b :=
  Iff.rfl

/-- `∐ R ∈ 𝓡, F[R]`, the disjoint union of the subgraphs induced by the classes. -/
def parts : SimpleGraph (Σ a : Quotient 𝓡.setoid, {v | 𝓡.proj v = a}) :=
  SimpleGraph.sigma 𝓡.part

/-- The projection is a homomorphism onto the quotient wherever it does not collapse. -/
theorem quotientGraph_adj_of_adj {u v : V} (h : F.Adj u v) (hne : 𝓡.proj u ≠ 𝓡.proj v) :
    𝓡.quotientGraph.Adj (𝓡.proj u) (𝓡.proj v) := ⟨hne, u, v, h, rfl, rfl⟩

/-- The quotient by a partition into connected parts is a contraction of `F`. -/
def contraction : Lax871432.Contractions.Contraction 𝓡.quotientGraph F where
  proj := 𝓡.proj
  connected := 𝓡.connected
  adj_iff _ _ := Iff.rfl

theorem isContraction : Lax871432.Contractions.IsContraction 𝓡.quotientGraph F :=
  ⟨𝓡.contraction⟩

end ConnPart

/-! ### Finiteness -/

instance ConnPart.instFinite {F : SimpleGraph V} [Finite V] : Finite (ConnPart F) :=
  Finite.of_injective (fun 𝓡 => (𝓡.setoid.r : V → V → Prop)) <| by
    intro R S h
    obtain ⟨s, hs⟩ := R
    obtain ⟨t, ht⟩ := S
    obtain rfl : s = t := Setoid.ext fun a b => Eq.to_iff (congrFun (congrFun h a) b)
    rfl

noncomputable instance ConnPart.instFintype {F : SimpleGraph V} [Finite V] :
    Fintype (ConnPart F) := Fintype.ofFinite _

end SimpleGraph

end Lax871432Proofs
