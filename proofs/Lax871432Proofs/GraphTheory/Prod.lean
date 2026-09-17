/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Mathlib.Combinatorics.SimpleGraph.Prod

/-!
# The categorical product of graphs

This file defines the categorical product of graphs. The categorical product of `G` and `H` is
the graph on the product of the vertices such that `x` and `y` are related iff their first
components are related via `G` *and* their second components are related via `H`. For example,
the categorical product of two edges is a pair of disjoint edges.

It is also known as the tensor, Kronecker, weak, or conjunction product, and it is the product
in the category of graphs and graph homomorphisms; see `SimpleGraph.Hom.catProdEquiv` in
`Hom/Basic.lean` for the universal property.

This file complements Mathlib's `Mathlib/Combinatorics/SimpleGraph/Prod.lean`, which so far
only provides the box product `□`, and whose organisation it follows.

## Main declarations

* `SimpleGraph.catProd`: the categorical product.

## Notation

* `G ×g H`: the categorical product of `G` and `H`.

## TODO

Define the lexicographic and strong products too.
-/

variable {α β γ : Type*}

namespace Lax871432Proofs

open _root_.SimpleGraph

namespace SimpleGraph

variable {G : SimpleGraph α} {H : SimpleGraph β}

/-- Categorical product of simple graphs. It relates `(a₁, b₁)` and `(a₂, b₂)` if `G` relates
`a₁` and `a₂` and `H` relates `b₁` and `b₂`. Contrast with `SimpleGraph.boxProd`. -/
def catProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj x y := G.Adj x.1 y.1 ∧ H.Adj x.2 y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

/-- Categorical product of simple graphs. It relates `(a₁, b₁)` and `(a₂, b₂)` if `G` relates
`a₁` and `a₂` and `H` relates `b₁` and `b₂`. -/
infixl:70 " ×g " => catProd

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
