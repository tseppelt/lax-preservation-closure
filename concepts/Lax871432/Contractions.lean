import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
---
title: Contracting edges
type: definition
---
A graph $K$ is *obtained from a simple graph $F$ by contracting edges* when the vertices of
$K$ are the classes of a partition $\mathcal{R}$ of $V(F)$ into parts inducing connected
subgraphs, two distinct classes being adjacent in $K$ exactly when $F$ joins a vertex of one
to a vertex of the other. In the notation of the paper, $K \cong F/\mathcal{R}$.

# Implementation notes

The partition is presented by the map sending a vertex of $F$ to its class, rather than as a
quotient type, so that $K$ may be any graph isomorphic to $F/\mathcal{R}$ and no transport
along a quotient is needed. Surjectivity of that map is not assumed: it follows, since a
connected graph is nonempty.

Contracting edges differs from taking minors, `Lax68.GraphMinors.IsMinor`, in two ways: the
classes must cover all of $V(F)$, and every adjacency of $F$ between distinct classes must be
present in $K$, not merely permitted.
-/

namespace Lax871432.Contractions

/-- A presentation of `K` as the graph obtained from `F` by contracting the edges inside the
classes of a partition of `V(F)` into connected parts. -/
structure Contraction {V W : Type*} (K : SimpleGraph W) (F : SimpleGraph V) where
  /-- The vertex of `K` a vertex of `F` is contracted to. -/
  proj : V → W
  /-- Each class induces a connected — in particular nonempty — subgraph of `F`. -/
  connected : ∀ w, (F.induce {v | proj v = w}).Connected
  /-- Distinct classes are adjacent in `K` exactly when `F` joins them. -/
  adj_iff : ∀ a b, K.Adj a b ↔ a ≠ b ∧ ∃ x y, F.Adj x y ∧ proj x = a ∧ proj y = b

/-- `K` is *obtained from `F` by contracting edges*. -/
def IsContraction {V W : Type*} (K : SimpleGraph W) (F : SimpleGraph V) : Prop :=
  Nonempty (Contraction K F)

end Lax871432.Contractions
