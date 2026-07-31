# Skew-adjoint graph-core resolvent

- **ID:** `deninger-skew-adjoint-graph-core-resolvent`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Label:** `DAC_SKEW_ADJOINT_GRAPH_CORE_RESOLVENT`
- **Parent:** `deninger-hodge-schwartz-resolvent-core`
- **Statement:** an off-axis resolvent of a skew-adjoint generator is
  a continuous automorphism of every common smooth graph core built
  from closed operators that strongly commute with it.

## Theorem

Let \(H\) be a complex Hilbert space and let \(A\) be skew-adjoint.
Let \((B_j)_{j\in J}\) be closed densely defined operators such that
every graph monomial \(B^\alpha\) commutes with the resolvent of \(A\)
on its natural domain.  Define
\[
  D_\infty
  =
  \bigcap_{\alpha}\operatorname{Dom}(B^\alpha)
  \cap
  \bigcap_{n\ge0}\operatorname{Dom}(A^n),                       \tag{1}
\]
with graph seminorms
\[
  p_{\alpha,n}(x)=\|B^\alpha A^n x\|.                           \tag{2}
\]

For every \(z\in\mathbb C\) with \(\operatorname{Re}z\ne0\),
\[
  A-z:D_\infty\longrightarrow D_\infty                         \tag{3}
\]
is a continuous linear automorphism.  Its inverse is the Hilbert
resolvent \(R_z=(A-z)^{-1}\), and
\[
  p_{\alpha,n}(R_zx)
  \le
  \frac1{|\operatorname{Re}z|}
  p_{\alpha,n}(x).                                              \tag{4}
\]

## Proof

`[PROVED HERE]`

Since \(A^*=-A\), the spectrum of \(A\) is contained in \(i\mathbb R\).
Hence \(z\) with \(\operatorname{Re}z\ne0\) belongs to the resolvent
set and the standard skew-adjoint resolvent estimate is
\[
  \|R_z\|\le|\operatorname{Re}z|^{-1}.                          \tag{5}
\]

Functional calculus gives \(A^nR_z=R_zA^n\) on
\(\operatorname{Dom}(A^n)\).  The strong-commutation hypothesis gives
the same identity for every \(B^\alpha\).  Therefore, for
\(x\in D_\infty\),
\[
\begin{aligned}
  p_{\alpha,n}(R_zx)
  &=\|B^\alpha A^nR_zx\|\\
  &=\|R_zB^\alpha A^nx\|\\
  &\le|\operatorname{Re}z|^{-1}p_{\alpha,n}(x),
\end{aligned}
\]
which proves `(4)` and shows \(R_zD_\infty\subset D_\infty\).

For \(y\in D_\infty\), put \(x=R_zy\).  Then \(x\in D_\infty\) and
\((A-z)x=y\), proving surjectivity.  Injectivity follows already on
\(\operatorname{Dom}A\).  The graph-seminorm estimates prove
continuity of the inverse, while continuity of \(A-z\) is immediate
from `(2)`.

## Arithmetic use

On harmonic degree one take \(B_j\) to be the source transverse,
fibred-cusp, and restricted-sum regularity operators.  The Hodge
Laplacian is used first to construct smooth harmonic representatives;
it need not commute with the conformal flow on every cochain degree.
Once the global Calderón--Green domain proves the required harmonic
strong commutation and identifies its source-smooth cohomology with a
dense subspace of this common graph core, off-axis source-resolvent
stability is automatic.

Thus the remaining arithmetic work is not a new spectral theorem.  It
is:

1. global domain construction;
2. commutation of flow with Green/Laplacian boundary conditions;
3. strict nuclear identification and density of the graph core in
   \(M_\zeta\).

## Gates

- [x] 0 → 1 in-progress: exact graph-core statement
- [x] 1 → 2 fully-proven: complete proof
- [ ] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

## References

- Stone's theorem and the spectral theorem for skew-adjoint
  generators.
- Christopher Deninger, *Arithmetic geometry and analysis on foliated
  spaces*, Theorem 4.1 and its use of Stone's theorem.
- Jesús A. Álvarez López, Yuri A. Kordyukov, Eric Leichtnam,
  *Analysis on Riemannian foliations of bounded geometry*,
  arXiv:1905.12912.
- Karsten Fritzsch, Daniel Grieser, Elmar Schrohe, *The Calderón
  Projector for Fibred Cusp Operators*, arXiv:2006.04645.

## Log

- 2026-07-27 — Extracted the abstract parameter-resolvent theorem.
  Global arithmetic source density and boundary-domain commutation
  remain separate conjectural inputs.
