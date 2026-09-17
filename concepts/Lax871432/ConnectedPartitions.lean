import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
---
title: Partitions into connected parts
type: definition
---
A *partition into connected parts* of a simple graph $F$ is a partition $\mathcal{R}$ of
$V(F)$ such that the subgraph $F[R]$ induced by every class $R \in \mathcal{R}$ is connected.

Two graphs are attached to such a partition: the *quotient* $F / \mathcal{R}$, whose vertices
are the classes and in which two distinct classes are adjacent when some edge of $F$ joins
them, and the disjoint union $\coprod_{R \in \mathcal{R}} F[R]$ of the induced subgraphs.
These are the two graphs occurring in the formula for the number of homomorphisms into a
lexicographic product.

The quotient by a partition into connected parts is exactly a contraction of $F$: its
projection has connected fibres, which is the defining property of a contraction. Conversely,
every contraction arises this way, from the partition into the fibres of its projection.

# Implementation notes

A partition of `V(F)` is given as a `Setoid V`, so that the classes are the fibres of the
canonical projection to the quotient type and no choice of representatives is involved. The
connectedness requirement is stated for the subgraph induced on the fibre over each point of
the quotient.

`parts` is the disjoint union of the induced subgraphs, indexed by the classes: its vertices
are pairs consisting of a class and a vertex of that class, and two of them are adjacent when
they are adjacent in `F` and lie in the same class. Since the ambient graph is `F` itself,
this is stated without a dependent rewrite.
-/

namespace Lax871432.ConnectedPartitions

variable {V : Type*}

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

/-- The subgraph of `F` induced by a class. -/
def part (a : Quotient 𝓡.setoid) : SimpleGraph {v | 𝓡.proj v = a} := F.induce _

/-- The quotient `F / 𝓡`: distinct classes are adjacent when `F` joins them. -/
def quotientGraph : SimpleGraph (Quotient 𝓡.setoid) where
  Adj a b := a ≠ b ∧ ∃ x y, F.Adj x y ∧ 𝓡.proj x = a ∧ 𝓡.proj y = b
  symm := ⟨fun _ _ h => by
    obtain ⟨hne, x, y, hxy, hx, hy⟩ := h
    exact ⟨hne.symm, y, x, hxy.symm, hy, hx⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- `∐ R ∈ 𝓡, F[R]`, the disjoint union of the subgraphs induced by the classes. -/
def parts : SimpleGraph (Σ a : Quotient 𝓡.setoid, {v | 𝓡.proj v = a}) where
  Adj p q := F.Adj p.2.1 q.2.1 ∧ 𝓡.proj p.2.1 = 𝓡.proj q.2.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => F.irrefl h.1⟩


/-- A finite graph has finitely many partitions into connected parts. -/
instance instFinite [Finite V] : Finite (ConnPart F) :=
  Finite.of_injective (fun 𝓡 => (𝓡.setoid.r : V → V → Prop)) <| by
    intro R S h
    obtain ⟨s, hs⟩ := R
    obtain ⟨t, ht⟩ := S
    obtain rfl : s = t := Setoid.ext fun a b => Eq.to_iff (congrFun (congrFun h a) b)
    rfl

noncomputable instance instFintype [Finite V] : Fintype (ConnPart F) := Fintype.ofFinite _

end ConnPart

end Lax871432.ConnectedPartitions
