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

variable (G H)

/-- The projection of `G ×g H` onto its first factor. -/
def catProdFst : G ×g H →g G where
  toFun := Prod.fst
  map_rel' h := h.1

/-- The projection of `G ×g H` onto its second factor. -/
def catProdSnd : G ×g H →g H where
  toFun := Prod.snd
  map_rel' h := h.2

end SimpleGraph

end Lax871432Proofs
