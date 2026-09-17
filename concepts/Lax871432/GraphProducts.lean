import Mathlib.Combinatorics.SimpleGraph.Prod

/-!
---
title: Products of graphs
type: definition
---
Two products of simple graphs, both on the product $V(G) \times V(H)$ of the vertex sets.

In the *categorical product* $G \times H$, the pairs $gh$ and $g'h'$ are adjacent when
$gg' \in E(G)$ **and** $hh' \in E(H)$. It is the product in the category of graphs and graph
homomorphisms, whence $\hom(F, G \times H) = \hom(F, G)\hom(F, H)$; it also goes by tensor,
Kronecker, weak or conjunction product.

In the *lexicographic product* $G \cdot H$, the pairs $gh$ and $g'h'$ are adjacent when
$gg' \in E(G)$, or else $g = g'$ and $hh' \in E(H)$. It replaces every vertex of $G$ by a copy
of $H$ and joins two copies completely whenever the corresponding vertices of $G$ are adjacent.

Mathlib supplies a third product on the same vertex set, the box product $G \square H$, in
which $gh$ and $g'h'$ are adjacent when they agree in one component and are adjacent in the
other. It is not used here, but it is what makes these two worth naming apart.
-/

namespace Lax871432.GraphProducts

variable {α β : Type*}

/-- The *categorical product* of simple graphs: it relates `(a₁, b₁)` and `(a₂, b₂)` when `G`
relates `a₁` and `a₂` and `H` relates `b₁` and `b₂`. Contrast with `SimpleGraph.boxProd`. -/
def catProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj x y := G.Adj x.1 y.1 ∧ H.Adj x.2 y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

@[inherit_doc]
scoped infixl:70 " ×g " => catProd

/-- The *lexicographic product* of simple graphs: it relates `(a₁, b₁)` and `(a₂, b₂)` when `G`
relates `a₁` and `a₂`, or when `a₁ = a₂` and `H` relates `b₁` and `b₂`. -/
def lexProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj x y := G.Adj x.1 y.1 ∨ (x.1 = y.1 ∧ H.Adj x.2 y.2)
  symm := ⟨fun _ _ h => h.imp SimpleGraph.Adj.symm fun h' => ⟨h'.1.symm, h'.2.symm⟩⟩
  loopless := ⟨fun _ h => h.elim (G.irrefl ·) fun h' => H.irrefl h'.2⟩

end Lax871432.GraphProducts
