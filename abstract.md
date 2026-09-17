Two graphs $G$ and $H$ are *homomorphism indistinguishable* over a class of graphs
$\mathcal{F}$ if $\hom(F, G) = \hom(F, H)$ for every $F \in \mathcal{F}$. Many equivalence
relations comparing graphs — isomorphism, spectral equivalences, equivalences with respect to
logic fragments — are of this form, and the classes $\mathcal{F}$ appearing in such
characterisations are invariably minor-closed.

This submission formalises the correspondence between closure properties of a graph class
$\mathcal{F}$ and preservation properties of its homomorphism indistinguishability relation
$\equiv_{\mathcal{F}}$, together with the tools it rests on. Its main results are that
$\equiv_{\mathcal{F}}$ is preserved under disjoint unions if and only if the homomorphism
distinguishing closure $\mathrm{cl}(\mathcal{F})$ is closed under taking summands, and that
$\equiv_{\mathcal{F}}$ is preserved under taking complements if and only if
$\mathrm{cl}(\mathcal{F})$ is minor-closed. The latter answers Question 8 of Roberson (2022):
an equivalence relation preserved under complements that is a homomorphism indistinguishability
relation at all is one over a minor-closed class. Both rest on a lemma of Curticapean, Dell and
Marx turning a linear combination of homomorphism counts determined by $\equiv_{\mathcal{F}}$
into membership in $\mathrm{cl}(\mathcal{F})$, which in turn rests on Lovász's theorem that
homomorphism counts determine a finite graph up to isomorphism; both are formalised here.
