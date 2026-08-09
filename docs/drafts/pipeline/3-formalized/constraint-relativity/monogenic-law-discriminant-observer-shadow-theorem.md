# Monogenic law-discriminant observer-shadow theorem

- **ID:** `monogenic-law-discriminant-observer-shadow-theorem`
- **Stage:** 3-formalized
- **Type:** THEOREM / CROSS-FACE UNIFICATION (paper)
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [FINITE MONOGENIC BRIDGE]`
  `[NO RH CLAIM] [FORMALIZED IN LEAN]`
- **Role:** ties relative cotangent, framed root orientation, observer determinant, positive
  magnitude, and ramification locus inside finite monogenic split-fibre package.
- **Novelty:** underlying algebra is classical. Candidate-new contribution is exact corpus
  dictionary and use as finite Source Execution Geometry model.

## Setup

Let `B` be commutative ring, let `n>=1`, and let

\[
 f(T)=T^n+a_{n-1}T^{n-1}+\cdots+a_0\in B[T]
 \tag{1}
\]

be monic, and put

\[
 A=B[T]/(f),
 \qquad t=T\bmod f.
 \tag{2}
\]

Then `A` is finite free `B`-module with basis `1,t,...,t^(n-1)`.

## Theorem 1: cotangent complex and Fitting ideal are controlled by different/discriminant

There are natural descriptions

\[
 \mathbb L_{A/B}
 \simeq
 \bigl[A\xrightarrow{\,f'(t)\,}A\,dt\bigr]
 \tag{3}
\]

in homological degrees `1->0`, and

\[
 \boxed{
 \Omega_{A/B}\cong A/(f'(t))\,dt.}
 \tag{4}
\]

Thus

\[
 H_1(\mathbb L_{A/B})
 =\operatorname{Ann}_A(f'(t)),
 \qquad
 H_0(\mathbb L_{A/B})=\Omega_{A/B}.
 \tag{5}
\]

As `B`-module, zeroth Fitting ideal is

\[
 \boxed{
 \operatorname{Fitt}_0^B(\Omega_{A/B})
 =\bigl(\operatorname{Disc}(f)\bigr),}
 \tag{6}
\]

up to conventional sign/unit.

### Proof

Because monic `f` is nonzerodivisor in `B[T]`, hypersurface cotangent complex is conormal complex

\[
 (f)/(f)^2\longrightarrow A\,dT.
\]

First map sends class of `f` to `f'(t)dt`, proving `(3)`--`(5)`. As `B`-module this gives square
presentation

\[
 A\xrightarrow{\,m_{f'(t)}\,}A
 \longrightarrow\Omega_{A/B}\longrightarrow0
\]

between free rank-`n` modules. Hence zeroth Fitting ideal is determinant of multiplication by
`f'(t)`, namely norm `N_(A/B)(f'(t))`. Resultant identity gives

\[
 N_{A/B}(f'(t))
 =(-1)^{n(n-1)/2}\operatorname{Disc}(f),
\]

proving `(6)`. QED.

## Theorem 2: split observer determinant is oriented square root

Choose ring map `phi:B->C`, write `A_phi=A tensor_(B,phi) C`, and suppose fibre polynomial

\[
 f(T)=\prod_{i=1}^n(T-r_i)
\]

has distinct roots, character observer

\[
 J_f:A_\phi\longrightarrow\mathbb C^n,
 \qquad
 g(t)\longmapsto(g(r_1),\ldots,g(r_n))
 \tag{7}
\]

has matrix in monomial basis

\[
 V_f=(r_i^{j-1})_{1\le i,j\le n}.
 \tag{8}
\]

Thus

\[
 \det V_f=\Delta_f
 :=\prod_{1\le i<j\le n}(r_j-r_i),
 \tag{9}
\]

and

\[
 \boxed{
 (\det V_f)^2=\operatorname{Disc}(f),
 \qquad
 |\det V_f|^2=|\operatorname{Disc}(f)|.}
 \tag{10}
\]

### Proof

Matrix is Vandermonde. Its determinant is product `(9)`. Standard root formula for monic
discriminant is square of Vandermonde, giving `(10)`. QED.

Ordering roots and choosing monomial trivialization orients `Delta_f`; permutation changes sign.
Globally square root is orientation/sign torsor and may have monodromy. Discriminant and positive
magnitude forget chosen orientation.

## Corollary 3: exact determinant-conditioning law

Give monomial domain basis and target character basis standard Hermitian norms. For singular values
`sigma_1,...,sigma_n` of resulting framed complex observer `V_f`,

\[
 \boxed{
 \prod_{j=1}^n\sigma_j(V_f)
 =|\det V_f|
 =|\operatorname{Disc}(f)|^{1/2}.}
 \tag{11}
\]

Observer loses invertibility exactly on discriminant locus. Discriminant controls product
conditioning; smallest singular value needs additional bounds on others and is not determined by
discriminant alone.

### Proof

Product singular values equals absolute determinant. Apply `(10)`. QED.

## Framed five-shadow dictionary

Framed package `(B,f,phi, ordered roots, monomial basis, Hermitian norms)` gives:

\[
 \begin{array}{c|c}
 \text{realization}&\text{shadow}\\ \hline
 \text{relative law geometry}&\mathbb L_{A/B}=[A\xrightarrow{f'}A],\quad
   \Omega_{A/B}=A/(f')dt\\
 \text{root orientation}&\Delta_f=\prod_{i<j}(r_j-r_i)\\
 \text{framed spectral observer}&V_f\text{ and its singular values}\\
 \text{positive magnitude}&|\Delta_f|^2=|\operatorname{Disc}f|\\
 \text{topology/support}&V(\operatorname{Disc}f)
 \end{array}
 \tag{12}
\]

Their determinant magnitudes and degeneracy loci are tied by:

\[
 \Delta_f
 \longmapsto|\Delta_f|^2
 \longmapsto[\Delta_f=0],
 \tag{13}
\]

while framed spectral observer retains basis-dependent conditioning but can lose conormal under
specialization. Derived Tor recovers lost direction in explicit quadratic family. Cotangent
complex alone does not recover root ordering, Hermitian norms, or singular values.

This finite model realizes corpus “uncertainty”: positive magnitude squares away orientation;
support erases multiplicity; diagonalizing observer loses nilpotent family direction; cotangent
retains algebraic thickness but does not determine analytic norm.

## RH specialization boundary

Quadratic mate law takes `f(T)=(T-1)(T-delta)`. Then

\[
 \Delta_f=\delta-1,
 \qquad
 \operatorname{Disc}(f)=(\delta-1)^2,
 \tag{14}
\]

formally reproducing oriented linear factor, squared discriminant/Fitting ideal, exact wall, and
two-character collision. This substitution is not comparison theorem identifying literal source
residue or Stokes form with algebra package.

The theorem does **not** force `delta=1`. Discriminant geometry organizes all routes but provides
no source selection equation. Literal source-normal anomaly must still prove physical divisor
lies on discriminant locus.

## Higher predictions

1. Framed `m`-sheet law collision carries Vandermonde line before positive scalarization;
   intrinsic version requires determinant/orientation torsor.
2. Raw anomaly/conormal rank grows with independent sheet collisions, while one physical port may
   arise only after cohomological transgression.
3. Positive route can detect branch locus but cannot recover ordering/coorientation.
4. Decoder determinant exponent is half discriminant order; individual inverse exponent depends
   ramification partition and other singular values.
5. Hypertranscendental infinite-sheet limits require pro-discriminant or determinant-line theory,
   not finite scalar discriminant.

## Hostile audit

1. Monogenic cotangent/discriminant/Vandermonde theorem is classical, not new field.
2. Cross-face dictionary is exact only for stated framed finite monogenic package and is still
   kinematical.
3. Nonmonogenic, infinite, noncommutative, or bornological events need different determinant
   objects; do not extrapolate automatically.
4. Discriminant vanishing is target conclusion in RH specialization, not source theorem.
5. Singular values and conditioning change under basis or norm change while discriminant ideal
   does not; no intrinsic spectral metric is claimed.
6. Finite etale changes can have zero cotangent complex, so theorem does not detect every
   non-Morita event.

## Lean-return note

No Lean work authorized. Later possible files: generic monogenic Kähler differential,
Fitting/resultant identity, Vandermonde determinant, singular-value determinant. Verify mathlib
before formal plan.

## Log

- 2026-08-08 — generalized quadratic four-shadow law to finite monogenic execution.

## Formalized companion

`monogenic-law-discriminant-observer-shadow-theorem-formalized.md` (same directory).
