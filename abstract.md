Two graphs $G$ and $H$ are *homomorphism indistinguishable* over a class of graphs
$\mathcal{F}$ if $\hom(F, G) = \hom(F, H)$ for every $F \in \mathcal{F}$. Many equivalence
relations comparing graphs — (quantum) isomorphism, spectral equivalences, equivalences with respect to logic fragments — are of this form, and the classes $\mathcal{F}$ appearing in such characterisations are often minor-closed.

This submission formalises the correspondence between closure properties of a graph class
$\mathcal{F}$ and preservation properties of its homomorphism indistinguishability relation
$\equiv_{\mathcal{F}}$. Its main results are that
$\equiv_{\mathcal{F}}$ is preserved under taking complements if and only if
$\mathrm{cl}(\mathcal{F})$ is minor-closed. Both rest on a lemma of Curticapean, Dell and
Marx turning a linear combination of homomorphism counts determined by $\equiv_{\mathcal{F}}$
into membership in $\mathrm{cl}(\mathcal{F})$, which in turn rests on Lovász's theorem that
homomorphism counts determine a finite graph up to isomorphism; both are formalised here.

The submission also formalises Roberson's conjecture (minor-closed union-closed graph classes are homomorphism distinguishing closed) and many basic notions from homomorphism indistinguishability including Lovász's theorem (homomorphism indistinguishability over all graphs is isomorphism) and the invertibility of the matrix $(\hom(F, G))_{F, G}$.