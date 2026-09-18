/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Lax871432.LoopGraphs
import Lax871432Proofs.GraphTheory.LoopGraph
import Lax871432Proofs.Hom.Count

/-!
# Counting homomorphisms of graphs with loops

`LoopGraph.homCount` extends `SimpleGraph.homCount` to graphs in which loops are allowed.  The
two agree on simple graphs (`SimpleGraph.homCount_toLoopGraph`), and the hom-types are in fact
definitionally equal, so no transport is needed when passing between them.

Loop graphs are only ever intermediate objects here; see `GraphTheory/LoopGraph.lean` and
`Hom/Complement.lean`.

## Main declarations

* `LoopGraph.homCount`: the number of homomorphisms between loop graphs.
* `LoopGraph.homCount_eq_zero_of_not_isLoopless`: a loop graph with a loop admits no
  homomorphism into a loopless one.
-/

namespace Lax871432Proofs

open _root_.SimpleGraph
open Lax871432.LoopGraphs
open scoped Lax871432.LoopGraphs
open Lax871432.HomomorphismCounts

open Function

variable {U V W : Type*}

namespace SimpleGraph

/-- Homomorphism counts between simple graphs agree with those between the corresponding loop
graphs; the two hom-types are definitionally equal. -/
theorem homCount_toLoopGraph (F : SimpleGraph V) (G : SimpleGraph W) :
    LoopGraph.homCount (toLoopGraph F) (toLoopGraph G) = homCount F G := rfl

end SimpleGraph

namespace LoopGraph

open scoped LoopGraph

variable {X : LoopGraph U} {Y : LoopGraph V} {Z : LoopGraph W}

/-- Homomorphism counts of loop graphs are invariant under isomorphism of the source. -/
theorem homCount_congr_left (e : X ≃lg Y) (Z : LoopGraph W) : LoopGraph.homCount X Z = LoopGraph.homCount Y Z :=
  Nat.card_congr
    { toFun f := f.comp e.symm.toRelEmbedding.toRelHom
      invFun f := f.comp e.toRelEmbedding.toRelHom
      left_inv f := by ext a; exact congrArg f (e.symm_apply_apply a)
      right_inv f := by ext a; exact congrArg f (e.apply_symm_apply a) }

/-- A loop graph with a loop admits no homomorphism into a loopless one, so the corresponding
homomorphism count vanishes.  This is what makes the terms of `SimpleGraph.homCount_looped`
indexed by an edge set whose contraction quotient has a loop drop out. -/
theorem homCount_eq_zero_of_not_isLoopless (hX : ¬ X.IsLoopless) (hY : Y.IsLoopless) :
    LoopGraph.homCount X Y = 0 := by
  rw [LoopGraph.homCount, Nat.card_eq_zero]
  simp only [LoopGraph.IsLoopless, not_forall, not_not] at hX
  obtain ⟨v, hv⟩ := hX
  exact Or.inl ⟨fun f => hY (f v) (f.map_rel hv)⟩

end LoopGraph

end Lax871432Proofs
