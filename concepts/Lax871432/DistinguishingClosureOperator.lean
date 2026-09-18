import Mathlib.Order.Closure
import Lax871432.DistinguishingClosure

/-!
---
title: The homomorphism distinguishing closure is a closure operator
type: lemma
---
The map $\mathcal{F} \mapsto \mathrm{cl}(\mathcal{F})$ is a closure operator on graph classes
ordered by inclusion: for all graph classes $\mathcal{F}$ and $\mathcal{F}'$,

- $\mathrm{cl}(\mathcal{F}) \subseteq \mathrm{cl}(\mathcal{F}')$ if
  $\mathcal{F} \subseteq \mathcal{F}'$,
- $\mathcal{F} \subseteq \mathrm{cl}(\mathcal{F})$, and
- $\mathrm{cl}(\mathrm{cl}(\mathcal{F})) = \mathrm{cl}(\mathcal{F})$.
-/

open Lax871432.DistinguishingClosure Lax871432.GraphClasses

namespace Lax871432.DistinguishingClosureOperator

/-- $\mathrm{cl}$ is a closure operator: it is monotone, extensive and idempotent. -/
axiom isClosureOperator : ∃ c : ClosureOperator GraphClass, ∀ 𝓕, c 𝓕 = cl 𝓕

end Lax871432.DistinguishingClosureOperator
