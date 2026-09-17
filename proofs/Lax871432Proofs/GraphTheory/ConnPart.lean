/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Lax871432Proofs.GraphTheory.Sigma
import Lax871432.ConnectedPartitions
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
open Lax871432.ConnectedPartitions

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

namespace ConnPart

variable {F : SimpleGraph V} (𝓡 : ConnPart F)

theorem proj_eq_iff {u v : V} : 𝓡.proj u = 𝓡.proj v ↔ 𝓡.setoid u v :=
  Quotient.eq (r := 𝓡.setoid)

@[simp]
theorem quotientGraph_adj {a b : Quotient 𝓡.setoid} :
    𝓡.quotientGraph.Adj a b ↔ a ≠ b ∧ ∃ x y, F.Adj x y ∧ 𝓡.proj x = a ∧ 𝓡.proj y = b :=
  Iff.rfl

/-- The projection is a homomorphism onto the quotient wherever it does not collapse. -/
theorem quotientGraph_adj_of_adj {u v : V} (h : F.Adj u v) (hne : 𝓡.proj u ≠ 𝓡.proj v) :
    𝓡.quotientGraph.Adj (𝓡.proj u) (𝓡.proj v) := ⟨hne, u, v, h, rfl, rfl⟩

/-- The quotient by a partition into connected parts is a contraction of `F`. -/
def contraction : Lax871432.Contractions.Contraction 𝓡.quotientGraph F where
  proj := 𝓡.proj
  connected := 𝓡.connected
  adj_iff _ _ := Iff.rfl

theorem isContraction : Lax871432.Contractions.IsContraction 𝓡.quotientGraph F :=
  ⟨(ConnPart.contraction 𝓡)⟩

end ConnPart

/-! ### Every contraction is a quotient -/

namespace Contraction

open Lax871432.Contractions

variable {W : Type*} {K : SimpleGraph W} {F : SimpleGraph V} (c : Contraction K F)

theorem proj_surjective : Function.Surjective c.proj := fun w => by
  obtain ⟨v⟩ := (c.connected w).nonempty
  exact ⟨v.1, v.2⟩

/-- The partition of `V(F)` into the fibres of a contraction. -/
def connPart : ConnPart F where
  setoid := Setoid.ker c.proj
  connected := fun a => by
    obtain ⟨v, rfl⟩ := a.exists_rep
    have hset : {u | Quotient.mk (Setoid.ker c.proj) u = Quotient.mk (Setoid.ker c.proj) v}
        = {u | c.proj u = c.proj v} := by
      ext u
      exact Quotient.eq (r := Setoid.ker c.proj)
    rw [hset]
    exact c.connected (c.proj v)

/-- The classes of that partition are the vertices of the contraction. -/
noncomputable def equivQuotient : Quotient (Setoid.ker c.proj) ≃ W :=
  Equiv.ofBijective (Quotient.lift c.proj fun _ _ h => h)
    ⟨by
      intro a b
      induction a using Quotient.ind
      induction b using Quotient.ind
      exact fun h => Quotient.sound h,
     fun w => by
      obtain ⟨v, hv⟩ := proj_surjective c w
      exact ⟨Quotient.mk _ v, hv⟩⟩

/-- **A contraction is the quotient by the partition into its fibres.** -/
noncomputable def isoQuotientGraph : K ≃g (connPart c).quotientGraph :=
  RelIso.symm
    { toEquiv := equivQuotient c
      map_rel_iff' := by
        intro a b
        induction a using Quotient.ind with | _ u =>
        induction b using Quotient.ind with | _ v =>
        rw [c.adj_iff]
        constructor
        · rintro ⟨hne, x, y, hxy, hx, hy⟩
          exact ⟨fun h => hne (congrArg (equivQuotient c) h), x, y, hxy,
            Quotient.sound hx, Quotient.sound hy⟩
        · rintro ⟨hne, x, y, hxy, hx, hy⟩
          exact ⟨fun h => hne ((equivQuotient c).injective h), x, y, hxy,
            Quotient.exact hx, Quotient.exact hy⟩ }

end Contraction

end SimpleGraph

end Lax871432Proofs
