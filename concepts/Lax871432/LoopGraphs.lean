import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.SetTheory.Cardinal.Finite

/-!
---
title: Graphs with loops
type: definition
---
A *loop graph* is a graph in which loops are allowed: a symmetric, not necessarily
irreflexive, relation on a vertex type. Simple graphs are the loopless case, and a loop graph
without loops is a simple graph again. A homomorphism of loop graphs sends adjacent vertices
to adjacent vertices, so a loop is sent to a loop and an edge to an edge or to a loop, and
$\hom(X, Y)$ counts these maps as for simple graphs. Besides homomorphisms and isomorphisms,
loop graphs carry here the *full complement* $\widehat{X}$, which replaces every edge by a
non-edge *and* every loop by a non-loop, the sub-loop-graph induced on a set of vertices, and
the edge set, which for a loop graph may contain a pair $vv$, one for each loop.

Loops arise from two constructions on simple graphs. The *looped graph* $G^\circ$ is obtained
from a simple graph $G$ by adding a loop at every vertex; the complement then factors as
$\overline{G} = \widehat{G^\circ}$, which is what makes a two-step expansion of homomorphism
counts into a complement possible.

The other is a quotient. For a simple graph $F$ and a set $L$ of unordered pairs of vertices,
the *contraction quotient* $F \oslash L$ has as vertices the connected components of the graph
on $V(F)$ with edge set $L$, and joins two of them when some edge of $E(F) \setminus L$ joins
a vertex of the one to a vertex of the other. It is a graph obtained from $F$ by contracting
the edges of $L$ whenever it is loopless; in general it is not, carrying a loop at a component
for every edge of $E(F) \setminus L$ with both endpoints inside it, which is why loops must be
allowed here.

Two operations on simple graphs accompany these: the *spanning subgraph* $F_s$, which keeps
all vertices of $F$ and those of its edges that lie in a set $s$, and the passage from a set
of edges of $F$ to the underlying set of unordered pairs.

# Implementation notes

A `LoopGraph` is a structure carrying an adjacency relation and a proof that it is symmetric,
with no irreflexivity field; `SimpleGraph` is the irreflexive case, `toLoopGraph` the
inclusion and `toSimpleGraph` the passage back, given a proof of `IsLoopless`. Homomorphisms
and isomorphisms, written `→lg` and `≃lg`, are those of the adjacency relations, so `F →g G`
and `toLoopGraph F →lg toLoopGraph G` are definitionally equal and `LoopGraph.homCount`
extends `homCount` along `toLoopGraph` with no transport needed.

`spanningSubgraph F s` takes an arbitrary set `s` of unordered pairs, and `edgeSetOf F s`
turns a finite set of edges of `F` into the corresponding set of pairs; together they let the
deletion part of the expansion be indexed by `Finset F.edgeSet`.

`contractionQuotient F L` likewise takes an arbitrary set `L` of pairs; its vertex type is the
connected components of `SimpleGraph.fromEdgeSet L`, which discards the diagonal pairs of `L`.

Only as much API is developed as the expansion of $\hom(F, \overline{G})$ needs. Loop graphs
enter that expansion through the contraction quotients on its right-hand side; every other
statement of the package is about simple graphs only.
-/

namespace Lax871432.LoopGraphs

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

/-- A homomorphism of loop graphs is a map preserving adjacency; loops are therefore sent to
loops, and edges to edges or to loops. -/
abbrev Hom (X : LoopGraph V) (Y : LoopGraph W) := X.Adj →r Y.Adj

/-- An isomorphism of loop graphs. -/
abbrev Iso (X : LoopGraph V) (Y : LoopGraph W) := X.Adj ≃r Y.Adj

end LoopGraph

@[inherit_doc LoopGraph.Hom] scoped infixl:50 " →lg " => Lax871432.LoopGraphs.LoopGraph.Hom
@[inherit_doc LoopGraph.Iso] scoped infixl:50 " ≃lg " => Lax871432.LoopGraphs.LoopGraph.Iso

namespace LoopGraph

/-- The number of homomorphisms from `X` to `Y`. -/
noncomputable def homCount (X : LoopGraph V) (Y : LoopGraph W) : ℕ := Nat.card (X →lg Y)

/-- A loop graph is *loopless* if no vertex is adjacent to itself. -/
def IsLoopless (X : LoopGraph V) : Prop := ∀ v, ¬ X.Adj v v

/-- The simple graph underlying a loopless loop graph. -/
def toSimpleGraph (X : LoopGraph V) (h : X.IsLoopless) : SimpleGraph V where
  Adj := X.Adj
  symm := X.symm
  loopless := ⟨h⟩

/-- The *full complement* of `X`: every edge becomes a non-edge and every loop a non-loop. -/
def fullCompl (X : LoopGraph V) : LoopGraph V where
  Adj u v := ¬ X.Adj u v
  symm := ⟨fun _ _ h h' => h (X.symm.symm _ _ h')⟩

/-- The sub-loop-graph induced on a set of vertices. -/
def induce (X : LoopGraph V) (s : Set V) : LoopGraph s where
  Adj a b := X.Adj a b
  symm := ⟨fun _ _ h => X.symm.symm _ _ h⟩

/-- The edges (and loops) of `X`, as a set of unordered pairs.  Unlike for simple graphs this
set may contain diagonal elements `s(v, v)`, one for each loop. -/
def edgeSet (X : LoopGraph V) : Set (Sym2 V) := Sym2.fromRel X.symm

end LoopGraph

/-- A simple graph, viewed as a loop graph. -/
def toLoopGraph (G : SimpleGraph V) : LoopGraph V where
  Adj := G.Adj
  symm := G.symm

/-- The *looped* graph `G°`: a loop is added at every vertex of `G`. -/
def looped (G : SimpleGraph V) : LoopGraph V where
  Adj u v := G.Adj u v ∨ u = v
  symm := ⟨fun _ _ h => h.imp (fun ha => ha.symm) (fun he => he.symm)⟩

/-- The spanning subgraph of `F` whose edges are those of `F` lying in `s`.  It has the same
vertex type as `F`. -/
def spanningSubgraph (F : SimpleGraph V) (s : Set (Sym2 V)) : SimpleGraph V where
  Adj u v := F.Adj u v ∧ s(u, v) ∈ s
  symm := ⟨fun _ _ h => ⟨h.1.symm, Sym2.eq_swap ▸ h.2⟩⟩
  loopless := ⟨fun _ h => F.irrefl h.1⟩

/-- The set of unordered pairs selected by a finite set of edges of `F`. -/
def edgeSetOf (F : SimpleGraph V) (s : Finset F.edgeSet) : Set (Sym2 V) :=
  Subtype.val '' (s : Set F.edgeSet)

/-- The *contraction quotient* `F ⊘ L`: its vertices are the connected components of the graph
on `V(F)` with edge set `L`, and `[v]` is adjacent to `[w]` when some edge of `E(F) \ L` joins
a vertex of `[v]` to a vertex of `[w]`.

The result may have loops, so it is a `LoopGraph`. -/
def contractionQuotient (F : SimpleGraph V) (L : Set (Sym2 V)) :
    LoopGraph (SimpleGraph.fromEdgeSet L).ConnectedComponent where
  Adj c d := ∃ x y, F.Adj x y ∧ s(x, y) ∉ L ∧
    (SimpleGraph.fromEdgeSet L).connectedComponentMk x = c ∧
    (SimpleGraph.fromEdgeSet L).connectedComponentMk y = d
  symm := ⟨fun _ _ ⟨x, y, hxy, hL, hx, hy⟩ =>
    ⟨y, x, hxy.symm, Sym2.eq_swap ▸ hL, hy, hx⟩⟩

@[inherit_doc] scoped notation:70 F:70 " ⊘ " L:71 => Lax871432.LoopGraphs.contractionQuotient F L

end Lax871432.LoopGraphs
