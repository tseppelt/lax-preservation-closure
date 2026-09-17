/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Mathlib.Combinatorics.SimpleGraph.Prod
import Lax871432.GraphProducts

/-!
# The categorical product of graphs

The categorical product `×g` itself is the concept `Lax871432.GraphProducts`; this file adds
the API for it, following the organisation of Mathlib's
`Mathlib/Combinatorics/SimpleGraph/Prod.lean`, which so far provides only the box product `□`.

It is the product in the category of graphs and graph homomorphisms; see
`SimpleGraph.Hom.catProdEquiv` in `Hom/Basic.lean` for the universal property.
-/

variable {α β γ : Type*}

namespace Lax871432Proofs

open scoped Lax871432.GraphProducts

open _root_.SimpleGraph

namespace SimpleGraph

variable {G : SimpleGraph α} {H : SimpleGraph β}

@[simp]
theorem catProd_adj {x y : α × β} :
    (G ×g H).Adj x y ↔ G.Adj x.1 y.1 ∧ H.Adj x.2 y.2 :=
  Iff.rfl

theorem catProd_adj_mk {a₁ a₂ : α} {b₁ b₂ : β} :
    (G ×g H).Adj (a₁, b₁) (a₂, b₂) ↔ G.Adj a₁ a₂ ∧ H.Adj b₁ b₂ :=
  Iff.rfl

theorem neighborSet_catProd (x : α × β) :
    (G ×g H).neighborSet x = G.neighborSet x.1 ×ˢ H.neighborSet x.2 := by
  ext ⟨a', b'⟩
  simp only [mem_neighborSet, catProd_adj, Set.mem_prod]

variable (G H)

/-- The categorical product is commutative up to isomorphism. `Equiv.prodComm` as a graph
isomorphism. -/
@[simps!]
def catProdComm : G ×g H ≃g H ×g G := ⟨Equiv.prodComm _ _, and_comm⟩

/-- The categorical product is associative up to isomorphism. `Equiv.prodAssoc` as a graph
isomorphism. -/
@[simps!]
def catProdAssoc (I : SimpleGraph γ) : G ×g H ×g I ≃g G ×g (H ×g I) :=
  ⟨Equiv.prodAssoc _ _ _, fun {_ _} => by simp [and_assoc]⟩

/-- The projection of `G ×g H` onto its first factor. -/
@[simps]
def catProdFst : G ×g H →g G where
  toFun := Prod.fst
  map_rel' h := h.1

/-- The projection of `G ×g H` onto its second factor. -/
@[simps]
def catProdSnd : G ×g H →g H where
  toFun := Prod.snd
  map_rel' h := h.2

end SimpleGraph

end Lax871432Proofs
