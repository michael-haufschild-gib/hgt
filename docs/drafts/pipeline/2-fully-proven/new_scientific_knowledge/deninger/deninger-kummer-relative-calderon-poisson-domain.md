# Kummer relative Calderón--Poisson domain

- **ID:** `deninger-kummer-relative-calderon-poisson-domain`
- **Stage:** 2-fully-proven
- **Type:** SOURCE FINITE-STAGE GREEN-DOMAIN THEOREM
- **Labels:** `DAC_KUMMER_RELATIVE_CALDERON_POISSON_DOMAIN`,
  `DAC_KUMMER_CALDERON_GRAPH_LAGRANGIAN`
- **Parent:** `deninger-kummer-poisson-green-boundary`
- **Statement:** the Kummer phase Poisson semigroup is the exact
  Calderón extension for a homogeneous relative energy complex; its
  boundary defect is a positive Hodge space and its Cauchy-data graph
  is Lagrangian.

## Boundary operator and energy spaces

At a finite Kummer phase stage let
\[
 D_\ell\chi_a=\ell(a)\chi_a,\qquad
 A_\ell=|D_\ell|
\]
on the mean-zero trigonometric core of
\(L^2(T_L,d\eta)\), where \(\ell(a)\ne0\) for \(a\ne0\).
Let \(\mathcal B_\ell\) be its completion for
\[
 \|\varphi\|_{\mathcal B_\ell}^2
 =
 \langle\varphi,A_\ell\varphi\rangle
 =
 \sum_{a\ne0}|\ell(a)|\,|\varphi_a|^2.                         \tag{1}
\]

On the half-cylinder use the homogeneous leafwise energy
\[
 \mathcal E_\ell(u)
 =
 \int_0^\infty
 \left(
  \|\partial_ru(r)\|_2^2+\|Y_\ell u(r)\|_2^2
 \right)\,dr.                                                  \tag{2}
\]
Let \(\dot{\mathcal E}_\ell\) be the completion of the finite Fourier
energy core and let
\(\dot{\mathcal E}_{\ell,0}\) be the closure of the subspace with
zero trace at \(r=0\).

## Trace and Dirichlet principle

`[PROVED HERE] [DAC_KUMMER_RELATIVE_CALDERON_POISSON_DOMAIN]`

The trace map extends to a quotient isometry
\[
 \operatorname{Tr}:
 \dot{\mathcal E}_\ell/\dot{\mathcal E}_{\ell,0}
 \xrightarrow{\;\cong\;}
 \mathcal B_\ell.                                               \tag{3}
\]
Its minimal-energy right inverse is the Poisson operator
\[
 \mathcal P\varphi(r)=e^{-rA_\ell}\varphi,                      \tag{4}
\]
and there is an orthogonal Dirichlet decomposition
\[
 \dot{\mathcal E}_\ell
 =
 \dot{\mathcal E}_{\ell,0}
 \widehat\oplus
 \mathcal P\mathcal B_\ell.                                    \tag{5}
\]

### Proof

For one Fourier coefficient \(u_a\), put
\(m=|\ell(a)|>0\).  Completing a square gives
\[
\begin{aligned}
 \int_0^\infty(|u_a'|^2+m^2|u_a|^2)\,dr
 &=
 m|u_a(0)|^2
 +\int_0^\infty|u_a'+mu_a|^2\,dr                              \tag{6}
\end{aligned}
\]
first for compactly supported coefficients and then by closure.
Thus the trace has norm at most one into `(1)`.  Equality holds
exactly for
\[
 u_a(r)=e^{-mr}u_a(0),
\]
which is `(4)`.  Summing the orthogonal Fourier coefficients proves
`(3)` and the energy identity
\[
 \mathcal E_\ell(\mathcal P\varphi)
 =
 \|\varphi\|_{\mathcal B_\ell}^2.                              \tag{7}
\]
If \(u_0\) has zero trace, integration by parts against the harmonic
Poisson extension makes their energy cross term zero.  This proves
`(5)`.

Applying the leafwise gradient identifies the relative boundary
defect
\[
 \frac{
  d_{\mathcal F}\dot{\mathcal E}_\ell
 }{
  \overline{d_{\mathcal F}\dot{\mathcal E}_{\ell,0}}
 }
 \cong\mathcal B_\ell.                                         \tag{8}
\]
Thus \(d_{\mathcal F}\mathcal P\varphi\) is exact in the maximal
energy domain but is a nonzero degree-one class relative to the
zero-trace degree-zero domain.  This is the precise domain distinction
needed to retain the Kummer boundary modes.

## Calderón graph

The Cauchy data of `(4)` are
\[
 (\varphi,A_\ell\varphi)
\]
up to the outward-normal sign convention.  On
\(\mathcal B_\ell\oplus\mathcal B_\ell'\) use the Green symplectic
form
\[
 \Omega((\varphi,\nu),(\psi,\mu))
 =
 \langle\varphi,\mu\rangle-\langle\nu,\psi\rangle.             \tag{9}
\]

`[PROVED HERE] [DAC_KUMMER_CALDERON_GRAPH_LAGRANGIAN]`

The graph
\[
 \Lambda_\ell=\operatorname{Graph}(A_\ell)
\]
is Lagrangian for `(9)`.

Indeed self-adjointness gives isotropy:
\[
 \Omega((\varphi,A_\ell\varphi),(\psi,A_\ell\psi))=0.
\]
If \((x,y)\) is symplectically orthogonal to the graph, then
\[
 \langle x,A_\ell\psi\rangle-\langle y,\psi\rangle=0
\]
for every core vector \(\psi\).  Closed self-adjointness of
\(A_\ell\) implies \(x\in\operatorname{Dom}A_\ell\) and
\(y=A_\ell x\), so the symplectic orthogonal equals the graph.

## Cup and positive Hodge form

Put
\[
 W_\ell=i\,\operatorname{sgn}(D_\ell).
\]
For boundary packets, Green--Stokes gives the alternating form
\[
 \Psi_\ell(\varphi,\psi)
 =
 \int_{(0,\infty)\times T_L}
 d_{\mathcal F}\mathcal P\varphi
 \wedge
 d_{\mathcal F}\mathcal P\psi
 =
 -\int_{T_L}\varphi\,Y_\ell\psi\,d\eta.                       \tag{10}
\]
It is nondegenerate on each finite packet stable under
\(a\mapsto-a\).  Complex conjugation exchanges \(a\) and \(-a\), and
\[
 \Psi_\ell(\varphi,W_\ell\overline\varphi)
 =
 \langle\varphi,A_\ell\varphi\rangle
 >0                                                          \tag{11}
\]
for \(\varphi\ne0\).  Hence `(8)` has a source-positive odd Hodge
operator with square \(-1\).

## Power naturality

For a positive integer \(q\),
\[
 A_\ell F_q^*=qF_q^*A_\ell,\qquad
 W_\ell F_q^*=F_q^*W_\ell.
\]
Therefore `(1)`, `(7)`, `(10)`, and `(11)` scale by \(q\), while
\(q^{-1/2}F_q^*\) is unitary.  After rational Kummer colimit it is
surjective; smooth suspension is still required before extending the
dense rational action to a strongly continuous real flow.

## Exact boundary of the theorem

This theorem constructs a canonical finite-stage relative Green
domain and eliminates ambiguity at the unitary \(r=0\) face.  It does
not prove that the infinite projective-ray augmentation has a
nondegenerate Hilbert quotient.  Orthogonal parallel gluing is ruled
out by `DAC_UNWEIGHTED_KUMMER_RAY_HILBERT_AUGMENTATION_NO_GO`.
The full Milnor relative-cell incidence and prime/real boundary
currents must construct the cross-ray global Calderón form before
completion.

It also does not identify `(10)` with Paugam's global pairing or prove
faithfulness on Meyer generalized spectral blocks.

## Hostile audit

- The class in `(8)` is relative-domain cohomology; it is not falsely
  called non-exact in the maximal de Rham domain.
- Small divisors cause no false compact-resolvent claim.  The boundary
  norm is defined by the closed spectral form of \(A_\ell\).
- Lagrangianity uses the full graph of a self-adjoint operator, not
  only isotropy.
- Positivity precedes any zeta-divisor evaluation.
- No RH premise, CCM object, or numerical computation enters.

## References

- `DAC_KUMMER_PHASE_POISSON_GREEN_BOUNDARY`.
- Standard Dirichlet principle and Calderón graph construction.
- Eugenie Hunsicker, *Extended Hodge Theory for Fibred Cusp
  Manifolds*, arXiv:1408.3257.

## Log

- 2026-07-27 — Promoted the local Poisson formulas to an exact
  relative energy quotient, proved the trace isometry, Dirichlet
  decomposition, Lagrangian Calderón graph, cup formula, and positive
  odd Hodge identity.
