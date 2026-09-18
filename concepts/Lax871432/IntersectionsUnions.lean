import Lax871432.DistinguishingClosure

/-!
---
title: The closure of intersections and unions
type: lemma
---
Let $I$ be an arbitrary index set and let $(\mathcal{F}_i)_{i \in I}$ be a family of graph
classes. Then
$$\mathrm{cl}\Big(\bigcap_{i \in I} \mathcal{F}_i\Big) \subseteq
\bigcap_{i \in I} \mathrm{cl}(\mathcal{F}_i) \quad \text{and} \quad
\bigcup_{i \in I} \mathrm{cl}(\mathcal{F}_i) \subseteq
\mathrm{cl}\Big(\bigcup_{i \in I} \mathcal{F}_i\Big).$$
-/

open Lax871432.DistinguishingClosure Lax871432.GraphClasses

namespace Lax871432.IntersectionsUnions

/-- The closure of an intersection is contained in the intersection of the closures. -/
axiom cl_iInf_le_iInf_cl {I : Type*} (𝓕 : I → GraphClass) :
    cl (⨅ i, 𝓕 i) ≤ ⨅ i, cl (𝓕 i)

/-- The union of the closures is contained in the closure of the union. -/
axiom iSup_cl_le_cl_iSup {I : Type*} (𝓕 : I → GraphClass) :
    ⨆ i, cl (𝓕 i) ≤ cl (⨆ i, 𝓕 i)

end Lax871432.IntersectionsUnions
