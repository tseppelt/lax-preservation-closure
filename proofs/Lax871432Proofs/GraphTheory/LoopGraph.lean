/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Graphs with loops

The complement `Gᶜ` of a simple graph factors through two constructions that leave the world
of simple graphs: the *looped* graph `G°`, obtained by adding a loop at every vertex, and the
*full complement* `X̂`, obtained by turning every edge into a non-edge *and* every loop into a
non-loop.  The point of the factorisation is the identity

  `(G°)^ = Gᶜ`   (`SimpleGraph.fullCompl_looped`),

which is what makes it possible to expand `hom(F, Gᶜ)` as a signed sum of homomorphism counts
into `G` itself; see `Hom/Complement.lean`.

Mathlib's `SimpleGraph` is loopless and its `Digraph` carries no symmetry, so this file
introduces `LoopGraph`: a symmetric, not necessarily irreflexive, relation on the vertices.
Only a thin API is developed — enough to state and use the two counting identities of
`Hom/Complement.lean`.  All the heavy machinery (the homomorphism matrix, the distinguishing
closure) stays on simple graphs, because loop graphs occur only as intermediate objects: in
the final identity `SimpleGraph.homCount_compl` both sides again involve simple graphs only.
Homomorphism counts of loop graphs are defined in `Hom/LoopGraph.lean`.

## Main declarations

* `LoopGraph`: a graph in which loops are allowed.
* `LoopGraph.fullCompl`: the full complement `X̂`.
* `SimpleGraph.looped`: the looped graph `G°`.
* `LoopGraph.induce`: the induced sub-loop-graph.
* `SimpleGraph.fullCompl_looped`: `(G°)^ = Gᶜ`.

## Notation

* `X →lg Y`: homomorphisms of loop graphs.
* `X ≃lg Y`: isomorphisms of loop graphs.
-/

namespace Lax871432Proofs

open _root_.SimpleGraph

open Function

variable {U V W : Type*}

/-- A graph in which loops are allowed: a symmetric relation on the vertex type.  Contrast
with `SimpleGraph`, which additionally requires irreflexivity, and with `Digraph`, which
requires nothing. -/
@[ext]
structure LoopGraph (V : Type*) where
  /-- The adjacency relation.  A vertex may be adjacent to itself, i.e. carry a loop. -/
  Adj : V → V → Prop
  /-- The adjacency relation is symmetric. -/
  symm : Std.Symm Adj := by aesop

namespace LoopGraph

/-- Adjacency in a loop graph is symmetric. -/
protected theorem Adj.symm {X : LoopGraph V} {u v : V} (h : X.Adj u v) : X.Adj v u :=
  X.symm.symm _ _ h

/-- A homomorphism of loop graphs is a map preserving adjacency; loops are therefore sent to
loops or to edges. -/
abbrev Hom (X : LoopGraph V) (Y : LoopGraph W) := X.Adj →r Y.Adj

/-- An isomorphism of loop graphs. -/
abbrev Iso (X : LoopGraph V) (Y : LoopGraph W) := X.Adj ≃r Y.Adj

@[inherit_doc] scoped infixl:50 " →lg " => LoopGraph.Hom
@[inherit_doc] scoped infixl:50 " ≃lg " => LoopGraph.Iso

/-- A loop graph is *loopless* if no vertex is adjacent to itself. -/
def IsLoopless (X : LoopGraph V) : Prop := ∀ v, ¬ X.Adj v v

/-- The simple graph underlying a loopless loop graph. -/
def toSimpleGraph (X : LoopGraph V) (h : X.IsLoopless) : SimpleGraph V where
  Adj := X.Adj
  symm := X.symm
  loopless := ⟨h⟩

@[simp]
theorem toSimpleGraph_adj (X : LoopGraph V) (h : X.IsLoopless) (u v : V) :
    (X.toSimpleGraph h).Adj u v ↔ X.Adj u v := Iff.rfl

/-- The *full complement* of `X`: every edge becomes a non-edge and every loop a non-loop. -/
def fullCompl (X : LoopGraph V) : LoopGraph V where
  Adj u v := ¬ X.Adj u v
  symm := ⟨fun _ _ h h' => h h'.symm⟩

@[simp]
theorem fullCompl_adj (X : LoopGraph V) (u v : V) : X.fullCompl.Adj u v ↔ ¬ X.Adj u v := Iff.rfl

/-- The sub-loop-graph induced on a set of vertices. -/
def induce (X : LoopGraph V) (s : Set V) : LoopGraph s where
  Adj a b := X.Adj a b
  symm := ⟨fun _ _ h => h.symm⟩

@[simp]
theorem induce_adj (X : LoopGraph V) (s : Set V) (a b : s) :
    (X.induce s).Adj a b ↔ X.Adj a b := Iff.rfl

/-- The edges (and loops) of `X`, as a set of unordered pairs.  Unlike for simple graphs this
set may contain diagonal elements `s(v, v)`, one for each loop. -/
def edgeSet (X : LoopGraph V) : Set (Sym2 V) := Sym2.fromRel X.symm

theorem mem_edgeSet {X : LoopGraph V} {a b : V} : s(a, b) ∈ X.edgeSet ↔ X.Adj a b :=
  Sym2.fromRel_prop

/-- An isomorphism of loop graphs maps edges to edges bijectively. -/
def Iso.mapEdgeSet {X : LoopGraph U} {Y : LoopGraph V} (e : X ≃lg Y) : X.edgeSet ≃ Y.edgeSet where
  toFun f := ⟨Sym2.map e f.1, by
    obtain ⟨f, hf⟩ := f
    induction f using Sym2.ind with
    | h a b => rw [Sym2.map_mk]; exact mem_edgeSet.2 (e.map_rel_iff.2 (mem_edgeSet.1 hf))⟩
  invFun f := ⟨Sym2.map e.symm f.1, by
    obtain ⟨f, hf⟩ := f
    induction f using Sym2.ind with
    | h a b =>
      rw [Sym2.map_mk]
      refine mem_edgeSet.2 (e.symm.map_rel_iff.2 (mem_edgeSet.1 hf))⟩
  left_inv f := Subtype.ext (by
    simp only [Sym2.map_map]
    rw [show ⇑e.symm ∘ ⇑e = id from funext e.symm_apply_apply, Sym2.map_id, id])
  right_inv f := Subtype.ext (by
    simp only [Sym2.map_map]
    rw [show ⇑e ∘ ⇑e.symm = id from funext e.apply_symm_apply, Sym2.map_id, id])

end LoopGraph

namespace SimpleGraph

open scoped LoopGraph

/-- A simple graph, viewed as a loop graph. -/
def toLoopGraph (G : SimpleGraph V) : LoopGraph V where
  Adj := G.Adj
  symm := G.symm

@[simp]
theorem toLoopGraph_adj (G : SimpleGraph V) (u v : V) : (toLoopGraph G).Adj u v ↔ G.Adj u v :=
  Iff.rfl

theorem toLoopGraph_isLoopless (G : SimpleGraph V) : (toLoopGraph G).IsLoopless :=
  fun _ => G.loopless.irrefl _

/-- Passing from a loopless loop graph to the underlying simple graph and back changes
nothing. -/
@[simp]
theorem _root_.Lax871432Proofs.LoopGraph.toSimpleGraph_toLoopGraph (X : LoopGraph V) (h : X.IsLoopless) :
    (toLoopGraph (X.toSimpleGraph h)) = X := rfl

/-- The *looped* graph `G°`: a loop is added at every vertex of `G`. -/
def looped (G : SimpleGraph V) : LoopGraph V where
  Adj u v := G.Adj u v ∨ u = v
  symm := ⟨fun _ _ h => h.imp (fun ha => ha.symm) (fun he => he.symm)⟩

@[simp]
theorem looped_adj (G : SimpleGraph V) (u v : V) : (looped G).Adj u v ↔ G.Adj u v ∨ u = v :=
  Iff.rfl

end SimpleGraph

namespace LoopGraph

open scoped LoopGraph

/-- The full complement is an involution. -/
@[simp]
theorem fullCompl_fullCompl (X : LoopGraph V) : X.fullCompl.fullCompl = X := by
  ext u v
  simp

end LoopGraph

namespace SimpleGraph

open scoped LoopGraph

/-- **The complement factors through the looped graph and the full complement**:
`(G°)^ = Gᶜ`.  This is the identity that drives `Hom/Complement.lean`. -/
theorem fullCompl_looped (G : SimpleGraph V) : (looped G).fullCompl = (toLoopGraph Gᶜ) := by
  ext u v
  simp [not_or, and_comm]

end SimpleGraph

end Lax871432Proofs
