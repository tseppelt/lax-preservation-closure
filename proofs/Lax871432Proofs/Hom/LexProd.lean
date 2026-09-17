/-
Copyright (c) 2026 Tim Seppelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Seppelt
-/
import Lax871432Proofs.GraphTheory.ConnPart
import Lax871432Proofs.Hom.Sigma
import Lax871432.GraphProducts

/-!
# Homomorphism counts into a lexicographic product

`hom(F, G ⋅ H) = ∑ 𝓡, hom(F / 𝓡, G) * hom(∐ R ∈ 𝓡, F[R], H)`, the sum ranging over the
partitions of `V(F)` into connected parts.

The bijection behind it sends `f : F →g G ⋅ H` to the partition into the connected components
of the edges of `F` whose `G`-components agree, together with the two halves of `f`.  The
partition attached to `f` is characterised without reference to components by
`SimpleGraph.Compatible`, which makes the fibres of the construction easy to describe.
-/

namespace Lax871432Proofs

open _root_.SimpleGraph
open Lax871432.GraphProducts Lax871432.HomomorphismCounts

open scoped Lax871432.GraphProducts

namespace SimpleGraph

variable {U V W : Type*} {F : SimpleGraph U} {G : SimpleGraph V} {H : SimpleGraph W}

/-! ### The partition a map induces -/

/-- The partition of `V(F)` into the connected components of the edges whose endpoints `p`
sends to the same value. -/
def ConnPart.ofMap (F : SimpleGraph U) {β : Type*} (p : U → β) : ConnPart F where
  setoid := (fibreSubgraph F p).reachableSetoid
  connected := fun a => by
    refine Connected.mono ?_ (ConnectedComponent.connected_toSimpleGraph a)
    intro x y h
    exact h.1

theorem ConnPart.proj_ofMap_eq_iff {β : Type*} {p : U → β} {u v : U} :
    (ConnPart.ofMap F p).proj u = (ConnPart.ofMap F p).proj v ↔
      (fibreSubgraph F p).Reachable u v :=
  ConnPart.proj_eq_iff _

/-! ### The partition a homomorphism induces -/

/-- `f` is *compatible* with `𝓡` when the classes of `𝓡` are exactly the connected components
of the edges of `F` whose first components under `f` agree: each class stays inside a fibre,
and no edge inside a fibre crosses classes. -/
structure Compatible (𝓡 : ConnPart F) (f : U → V × W) : Prop where
  /-- The first component of `f` is constant on classes. -/
  const : ∀ u v, 𝓡.proj u = 𝓡.proj v → (f u).1 = (f v).1
  /-- An edge of `F` whose endpoints share a first component stays inside a class. -/
  maximal : ∀ u v, F.Adj u v → (f u).1 = (f v).1 → 𝓡.proj u = 𝓡.proj v

variable {𝓡 : ConnPart F} {f : U → V × W}

/-- Inside a class, `F` and the subgraph spanned by the edges `f` does not separate agree. -/
def ConnPart.inclFibre (hc : Compatible 𝓡 f) (a : Quotient 𝓡.setoid) :
    𝓡.part a →g fibreSubgraph F (fun v => (f v).1) where
  toFun := Subtype.val
  map_rel' := fun {x y} h => ⟨h, hc.const _ _ (x.2.trans y.2.symm)⟩

/-- Vertices in one class are joined by a walk that never leaves a fibre. -/
theorem Compatible.reachable_of_proj_eq (hc : Compatible 𝓡 f) {u v : U}
    (h : 𝓡.proj u = 𝓡.proj v) :
    (fibreSubgraph F (fun w => (f w).1)).Reachable u v := by
  have hu : u ∈ {w | 𝓡.proj w = 𝓡.proj u} := rfl
  have hv : v ∈ {w | 𝓡.proj w = 𝓡.proj u} := h.symm
  have := (𝓡.connected (𝓡.proj u)).preconnected ⟨u, hu⟩ ⟨v, hv⟩
  exact (this.map (ConnPart.inclFibre hc (𝓡.proj u)))

/-- Conversely, a walk that never leaves a fibre stays inside a class. -/
theorem Compatible.proj_eq_of_reachable (hc : Compatible 𝓡 f) {u v : U}
    (h : (fibreSubgraph F (fun w => (f w).1)).Reachable u v) : 𝓡.proj u = 𝓡.proj v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hab _ ih => exact (hc.maximal _ _ hab.1 hab.2).trans ih

/-- Every map is compatible with the partition it induces. -/
theorem compatible_ofMap (F : SimpleGraph U) (f : U → V × W) :
    Compatible (ConnPart.ofMap F (fun v => (f v).1)) f where
  const u v h :=
    eq_of_reachable_fibreSubgraph (F := F) (p := fun w => (f w).1)
      ((ConnPart.proj_ofMap_eq_iff (F := F) (p := fun w => (f w).1) (u := u) (v := v)).1 h)
  maximal u v hadj heq :=
    (ConnPart.proj_ofMap_eq_iff (F := F) (p := fun w => (f w).1) (u := u) (v := v)).2
      (Adj.reachable ⟨hadj, heq⟩)

/-- A graph has at most one partition compatible with a given map. -/
theorem Compatible.unique {𝓡 𝓡' : ConnPart F} (hc : Compatible 𝓡 f) (hc' : Compatible 𝓡' f) :
    𝓡 = 𝓡' := by
  obtain ⟨s, hs⟩ := 𝓡
  obtain ⟨t, ht⟩ := 𝓡'
  obtain rfl : s = t := Setoid.ext fun a b => by
    constructor
    · intro hab
      exact (ConnPart.proj_eq_iff _).1
        (hc'.proj_eq_of_reachable (hc.reachable_of_proj_eq ((ConnPart.proj_eq_iff _).2 hab)))
    · intro hab
      exact (ConnPart.proj_eq_iff _).1
        (hc.proj_eq_of_reachable (hc'.reachable_of_proj_eq ((ConnPart.proj_eq_iff _).2 hab)))
  rfl

/-! ### The two halves of a compatible homomorphism -/

/-- `∐ R ∈ 𝓡, F[R]`, realised on the vertices of `F`: the edges of `F` that stay inside a
class.  It is isomorphic to the disjoint union `SimpleGraph.ConnPart.parts`. -/
def ConnPart.partsGraph (𝓡 : ConnPart F) : SimpleGraph U := fibreSubgraph F 𝓡.proj

@[simp]
theorem ConnPart.partsGraph_adj {𝓡 : ConnPart F} {u v : U} :
    𝓡.partsGraph.Adj u v ↔ F.Adj u v ∧ 𝓡.proj u = 𝓡.proj v := Iff.rfl

/-- Adjacency in the disjoint union of the classes. -/
theorem sigma_part_adj_iff {𝓡 : ConnPart F} {p q : Σ a : Quotient 𝓡.setoid,
    {v | 𝓡.proj v = a}} :
    (SimpleGraph.sigma 𝓡.part).Adj p q ↔ F.Adj p.2.1 q.2.1 ∧ p.1 = q.1 := by
  constructor
  · rintro ⟨i, u, v, huv, rfl, rfl⟩
    exact ⟨huv, rfl⟩
  · rintro ⟨hadj, hfst⟩
    obtain ⟨a, x, hx⟩ := p
    obtain ⟨b, y, hy⟩ := q
    cases hfst
    exact sigma_adj_mk.2 hadj

/-- Realising the disjoint union of the classes on the vertices of `F`. -/
def ConnPart.isoPartsGraph (𝓡 : ConnPart F) : SimpleGraph.sigma 𝓡.part ≃g 𝓡.partsGraph where
  toEquiv := Equiv.sigmaFiberEquiv 𝓡.proj
  map_rel_iff' := by
    intro p q
    show 𝓡.partsGraph.Adj p.2.1 q.2.1 ↔ _
    rw [ConnPart.partsGraph_adj, sigma_part_adj_iff, p.2.2, q.2.2]

/-- **`eq:coproduct` for the classes of a partition**: the disjoint union of the classes is
counted by the product over the classes, so it cannot tell apart two graphs that none of the
classes tells apart. -/
theorem homCount_partsGraph_congr [Finite U] {W' : Type*} (𝓡 : ConnPart F) (H : SimpleGraph W)
    (H' : SimpleGraph W') (h : ∀ a, homCount (𝓡.part a) H = homCount (𝓡.part a) H') :
    homCount 𝓡.partsGraph H = homCount 𝓡.partsGraph H' := by
  haveI : Finite (Quotient 𝓡.setoid) := Quotient.finite _
  haveI : Fintype (Quotient 𝓡.setoid) := Fintype.ofFinite _
  rw [← homCount_congr_left 𝓡.isoPartsGraph H, ← homCount_congr_left 𝓡.isoPartsGraph H',
    homCount_sigma, homCount_sigma]
  exact Finset.prod_congr rfl fun a _ => h a

variable {f : F →g lexProd G H}

/-- The homomorphism `F / 𝓡 → G` carried by a compatible homomorphism. -/
def Compatible.toQuotientHom (hc : Compatible 𝓡 ⇑f) : 𝓡.quotientGraph →g G where
  toFun := Quotient.lift (fun v => (f v).1)
    (fun a b hab => hc.const a b ((ConnPart.proj_eq_iff 𝓡).2 hab))
  map_rel' := by
    rintro a b ⟨hne, x, y, hxy, rfl, rfl⟩
    rcases f.map_rel' hxy with h | ⟨heq, -⟩
    · exact h
    · exact absurd (hc.maximal x y hxy heq) hne

/-- The homomorphism `∐ R ∈ 𝓡, F[R] → H` carried by a compatible homomorphism. -/
def Compatible.toPartsHom (hc : Compatible 𝓡 ⇑f) : 𝓡.partsGraph →g H where
  toFun v := (f v).2
  map_rel' := by
    intro u v huv
    rcases f.map_rel' huv.1 with h | ⟨-, h⟩
    · exact absurd (hc.const u v huv.2) h.ne
    · exact h

/-- The homomorphism assembled from a homomorphism out of the quotient and one out of the
disjoint union of the classes. -/
def ConnPart.homOfPair (𝓡 : ConnPart F) (g : 𝓡.quotientGraph →g G) (h : 𝓡.partsGraph →g H) :
    F →g lexProd G H where
  toFun v := (g (𝓡.proj v), h v)
  map_rel' := by
    intro u v huv
    by_cases hp : 𝓡.proj u = 𝓡.proj v
    · exact Or.inr ⟨by rw [hp], h.map_rel' ⟨huv, hp⟩⟩
    · exact Or.inl (g.map_rel' (𝓡.quotientGraph_adj_of_adj huv hp))

theorem compatible_homOfPair (𝓡 : ConnPart F) (g : 𝓡.quotientGraph →g G)
    (h : 𝓡.partsGraph →g H) : Compatible 𝓡 ⇑(𝓡.homOfPair g h) where
  const u v hp := by
    show g (𝓡.proj u) = g (𝓡.proj v)
    rw [hp]
  maximal u v huv heq := by
    by_contra hne
    exact (g.map_rel' (𝓡.quotientGraph_adj_of_adj huv hne)).ne heq

/-- **The bijection behind the formula**, at a fixed partition. -/
def compatibleEquiv (𝓡 : ConnPart F) :
    {f : F →g lexProd G H // Compatible 𝓡 ⇑f} ≃
      (𝓡.quotientGraph →g G) × (𝓡.partsGraph →g H) where
  toFun f := (f.2.toQuotientHom, f.2.toPartsHom)
  invFun gh := ⟨𝓡.homOfPair gh.1 gh.2, compatible_homOfPair 𝓡 gh.1 gh.2⟩
  left_inv := by
    rintro ⟨f, hc⟩
    ext v
    · rfl
    · rfl
  right_inv := by
    rintro ⟨g, h⟩
    refine Prod.ext ?_ rfl
    ext a
    induction a using Quotient.ind
    rfl

/-! ### The counting formula -/

/-- **`thm:lexprod-hom`**: homomorphisms into a lexicographic product, counted by the
partition of the source they induce. -/
theorem homCount_lexProd [Finite U] [Finite V] [Finite W] (F : SimpleGraph U)
    (G : SimpleGraph V) (H : SimpleGraph W) :
    homCount F (lexProd G H) =
      ∑ 𝓡 : ConnPart F, homCount 𝓡.quotientGraph G * homCount 𝓡.partsGraph H := by
  classical
  have key : ∀ (𝓡 : ConnPart F) (f : F →g lexProd G H),
      ConnPart.ofMap F (fun v => (f v).1) = 𝓡 ↔ Compatible 𝓡 ⇑f := by
    intro 𝓡 f
    refine ⟨?_, fun hc => (compatible_ofMap F ⇑f).unique hc⟩
    rintro rfl
    exact compatible_ofMap F ⇑f
  rw [homCount, ← Nat.card_congr
    (Equiv.sigmaFiberEquiv (fun f : F →g lexProd G H => ConnPart.ofMap F (fun v => (f v).1))),
    Nat.card_sigma]
  refine Finset.sum_congr rfl fun 𝓡 _ => ?_
  rw [Nat.card_congr (Equiv.subtypeEquivRight (key 𝓡)), Nat.card_congr (compatibleEquiv 𝓡),
    Nat.card_prod]
  rfl

end SimpleGraph

end Lax871432Proofs
