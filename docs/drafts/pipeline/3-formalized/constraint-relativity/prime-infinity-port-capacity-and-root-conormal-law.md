# Prime--infinity port capacity and root-conormal law

- **ID:** `prime-infinity-port-capacity-and-root-conormal-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / FINITE-RANK NO-GO / POSITIVE SURVIVOR (paper)
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [BRIDGE]`
  `[NEW RH-ROUTE LEVERAGE] [NO RH CLAIM] [FORMALIZED IN LEAN]`
- **Role:** rules out every fixed finite-rank diagonal infinity port as global rank-one selector;
  identifies two-prime half-density line as `A_1` shadow of `A_infinity` conormal.

## Setup

Fix `N` distinct primes and `r` proposed invertible infinity ports. Let

\[
 R=\mathbb C[x_1^{\pm1},\ldots,x_N^{\pm1},
 z_1^{\pm1},\ldots,z_r^{\pm1}].
 \tag{1}
\]

For integer matrix `M in Z^(N times r)`, put

\[
 m_i(z)=\prod_{\alpha=1}^rz_\alpha^{M_{i\alpha}},
 \qquad
 \rho_i=x_i m_i(z)-1,
 \qquad
 I=(\rho_1,\ldots,\rho_N).
 \tag{2}
\]

Then

\[
 S=R/I\cong
 \mathbb C[z_1^{\pm1},\ldots,z_r^{\pm1}],
 \tag{3}
\]

so ideal is proper. Let derivations `tilde partial_j` extend prime valuations:

\[
 \widetilde\partial_jx_i=\delta_{ji}x_i.
 \tag{4}
\]

In `S`, define

\[
 B_{j\alpha}
 =\overline{z_\alpha^{-1}
 \widetilde\partial_jz_\alpha}
 \tag{5}
\]

and transgression matrix

\[
 \Omega_{ji}
 =\overline{\widetilde\partial_j\rho_i}.
 \tag{6}
\]

## Theorem 1: sharp port-capacity bound

Over fraction field of `S`,

\[
 \boxed{
 \Omega=I_N+BM^T,
 \qquad
 \operatorname{rank}\Omega\ge N-r.}
 \tag{7}
\]

Consequently:

1. all valuation derivations descend strictly to `R/I` only if `r>=N`;
2. rank-one common anomaly requires `r>=N-1`;
3. no fixed finite `r` supports all-prime rank-one transgression;
4. one common infinity port has anomaly rank at least `N-1`.

### Proof

Leibniz gives

\[
 \widetilde\partial_j\rho_i
 =\left(
  \delta_{ji}
  +\sum_\alpha M_{i\alpha}
       z_\alpha^{-1}\widetilde\partial_jz_\alpha
  \right)x_im_i(z).
\]

In `S`, `x_i m_i(z)=1`, yielding matrix identity `(7)`. Derivations descend precisely when
derivative of each ideal generator belongs to `I`, equivalently `Omega=0`.

If `Omega v=0`, then

\[
 v=-BM^Tv\in\operatorname{im}B.
\]

Hence `dim ker Omega <= rank B <= r`; rank-nullity proves lower bound. Stated consequences are
immediate. Bound is sharp for every `0<=r<=N`: take

\[
 M=\begin{pmatrix}I_r\\0\end{pmatrix},
 \qquad
 B=\begin{pmatrix}-I_r\\0\end{pmatrix}.
\]

Then `Omega=diag(0_r,I_(N-r))`. These constants arise from Laurent derivations defined by
`tilde partial_j z_alpha=B_(j alpha)z_alpha`, so equality cases occur inside stated model. QED.

## Theorem 2: radial stabilizer classification

Give infinity ports radial weights `kappa=(kappa_alpha) in R^r` and set

\[
 \Gamma_cx_i=e^{c\log p_i}x_i,
 \qquad
 \Gamma_cz_\alpha=e^{c\kappa_\alpha}z_\alpha.
 \tag{8}
\]

Then

\[
 \operatorname{Stab}_{\mathbb R}(I)=
 \begin{cases}
 \mathbb R,&\log p+M\kappa=0,\\
 \{0\},&\log p+M\kappa\ne0.
 \end{cases}
 \tag{9}
\]

### Proof

Modulo `I`,

\[
 \Gamma_c(\rho_i)
 =e^{c(\log p_i+(M\kappa)_i)}-1.
\]

For real `c` and real weights, this vanishes for every `i` and every `c` exactly when all weights
cancel. If some component is nonzero, simultaneous vanishing holds only for `c=0`. QED.

Product-formula calibration is blind first case. Any genuine selector makes valuations
transgress rather than descend.

## Theorem 3: two-prime false friend and type-A conormal

For `N=2,r=1`, symmetric minimal-rank choice gives

\[
 \Omega_2=\frac12
 \begin{pmatrix}
 1&-1\\
 -1&1
 \end{pmatrix},
 \tag{10}
\]

one antisymmetric half-density line. For `N` primes, symmetric one-port choice is

\[
 \Omega_N=I_N-\frac1N\mathbf1\mathbf1^T,
 \tag{11}
\]

whose image is mean-zero type-`A_(N-1)` root space and rank `N-1`.

### Proof

With `M=1` column, permutation symmetry forces `B=b1`. Thus

\[
 \Omega=I_N+b\mathbf1\mathbf1^T.
\]

It has eigenvalue `1+Nb` on common line `C1` and eigenvalue `1` on mean-zero space. Its minimum
rank `N-1` occurs uniquely at `b=-1/N`, yielding `(11)`. It is orthogonal projection to hyperplane
`sum_i v_i=0`. For `N=2`, this is `(10)`. QED.

Scalar Kummer covector on `(10)` is

\[
 (\log p,\log q)\Omega_2
 =\frac{\log p-\log q}{2}(1,-1).
\]

Two-prime rank one is dimensional accident, not global one-port law.

## Literal-source warning

Model relation `x_i z=1` for all `i` identifies distinct prime units in quotient. Actual rational
scaling group and valuation coframe forbid this. The theorem is capacity no-go and normal-form
calculation, not construction of literal arithmetic relation.

Genuine source must realize relative conormal without imposing false equality `U_p=U_q`.

## Positive survivor

All-prime candidate must have shape

\[
 A_\infty\text{ raw prime--infinity conormal}
 \longrightarrow
 \text{singular source cohomology}
 \longrightarrow
 \text{one physical Stokes orientation}.
 \tag{12}
\]

No bounded fixed finite-rank port, strict coframe quotient, or common inverse suffices. Finite
two-prime route remains possible only if literal source constructs exact `A_1` conormal without
fictitious common inverse and proves coefficient-faithful landing.

## Hostile audit

1. Rank theorem is elementary matrix algebra; novelty is route-level closure and root-conormal
   identification.
2. Infinite-rank singular transgression is prediction, not construction.
3. Rank-one physical Stokes port may arise only after cohomology; raw rank cannot already be one
   uniformly in prime cutoff.
4. This card does not prove source-nullity or RH.

## Literature boundary

Occupied parents include crossed-product cyclic theory (arXiv:2205.08880), paracyclic theory
(arXiv:1810.04835), Kummer comparison (arXiv:2501.16916), infinite prime-torus dynamics
(arXiv:2604.02213), and CCM noncommutative arithmetic (arXiv:math/0703392).

## Lean-return note

No Lean work authorized. If later requested, generic rank inequality and projection formula are
finite linear algebra targets. Literal source realization remains paper-open.

## Log

- 2026-08-08 — seven-loop prime--infinity transgression audit; proof promoted.

## Formalized companion

`prime-infinity-port-capacity-and-root-conormal-law-formalized.md` (same directory).
