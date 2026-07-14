# Xi reciprocal-square rank-one Cauchy source criterion

- **ID:** `xi-reciprocal-square-one-cauchy-source`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / SOURCE-INTERFACE REDUCTION
- **Scientific status:** `[PROVED] [FORMALIZED] [BRIDGE] [NOT AN RH PROOF]`
- **Lean file:** `formal/GaloisForLFunctions/RHTower/XiReciprocalSquareOneCauchySource.lean`
- **Statement:** Reality of the reciprocal-square Xi quadratic value separately on every single
  regular continued-Cauchy source vector is equivalent to RH; no finite Cauchy packet
  cross-relations are required.

## Goal

Shrink the existing reciprocal-square source-core obligation

```text
quadratic reality on every finite algebraic continued-Cauchy packet
  -> RH
```

to the rank-one value family

```text
quadratic reality on each individual continued-Cauchy source vector
  -> RH.
```

This removes every off-diagonal relation between distinct source points.  It is not obtained by
polarizing the rank-one hypothesis: reality on an arbitrary collection of vectors does not in
general imply reality on their linear span.  Instead, the actual Xi Cauchy family has a stronger
source-specific property: scalar multiples of individual Cauchy vectors exhaust every complete
analytic-multiplicity fibre.

## Exact chain

For each multiplicity copy `q`, the corpus constructs regular points

\[
z_n=\lambda_q+\frac{c}{n+1}
\]

inside the analytically continued prime--Gamma domain such that

\[
(\lambda_q-z_n)k_{z_n}
\longrightarrow
\mathbf 1_{\{\lambda=\lambda_q\}}
\quad\text{in }\ell^2(Z_\Xi).
\]

Quadratic reality is invariant under complex rescaling and defines a norm-closed subset.  Hence
rank-one source reality passes to the complete fibre indicator.  That indicator is an eigenvector
of the reciprocal-square operator with eigenvalue `lambda_q^-2`, so its nonzero norm cancels and
forces

\[
\overline{\lambda_q^{-2}}=\lambda_q^{-2}.
\]

The open critical-strip geometry then removes the square ambiguity:

\[
\operatorname{Im}(\lambda_q^{-2})=0
\Longrightarrow
\operatorname{Re}\rho_q=\frac12.
\]

Thus

```text
single continued-Cauchy quadratic values are real
  -> exact fibre quadratic values are real
  -> every reciprocal-square coordinate is real
  -> every Xi zero lies on the critical line
  -> RH.
```

Conversely RH makes the complete reciprocal-square operator self-adjoint, so the rank-one
condition follows immediately.

## What changed

The previous smallest formal obligation quantified over the algebraic span of the source vectors,
so a source proof had to control all finite coefficient choices and all mixed Cauchy terms.  The
new theorem quantifies only over one source point at a time.  The subsequent
`xi-reciprocal-square-countable-cauchy-source` theorem reduces this further to regular
Gaussian-rational points in the centered strip.  A future source attack may therefore seek the
countable scalar reflection/value relation

\[
\langle R_\Xi^2 k_z,k_z\rangle\in\mathbb R
\]

for each regular Gaussian-rational continued point `z`; it no longer needs a matrix, packet
theorem, or uncountable quantifier.

The condition is still terminal and RH-strength.  The remaining open part is an unconditional
prime--Gamma identity or reflection law producing the countable scalar reality family without
using Xi divisor orientation, Weil positivity, real-rootedness, or an RH-equivalent positive
measure.

## Literature calibration

Aronszajn's foundational reproducing-kernel theory explains the standard role of kernel vectors,
their spans, and closure in Hilbert-space operator questions: [Theory of Reproducing Kernels,
Trans. AMS 68 (1950)](https://doi.org/10.1090/S0002-9947-1950-0051437-7).  The present reduction is
more specialized than the generic kernel-span principle because it deliberately avoids
polarization and uses the Xi-specific moving-pole limit to reach each exact divisor fibre from
individual kernels.  No novelty claim is needed for the proof-route contribution.

## Lean certificate

The public declarations are:

```text
XiReciprocalSquareOneCauchyQuadraticReal
xiReciprocalSquare_quadraticReal_smul
xiZeroCopyReciprocalSquare_star_eq_of_oneCauchyQuadraticReal
riemannHypothesis_of_xiReciprocalSquareOneCauchyQuadraticReal
xiReciprocalSquareOneCauchyQuadraticReal_of_riemannHypothesis
xiReciprocalSquareOneCauchyQuadraticReal_iff_riemannHypothesis
xiReciprocalSquareContinuedCauchyQuadraticReal_of_oneCauchy
```

The module is imported by `GaloisForLFunctions.RHTower`.

## Gates

- [x] 0 → 1 in-progress: distinct rank-one interface and pole-exhaustion attack identified
- [x] 1 → 2 fully-proven: fibre-limit proof and square-ambiguity exclusion complete
- [x] 2 → 3 formalized: Lean module is placeholder-free and umbrella-wired
- [ ] 3 → 4 publication-ready: only after an unconditional source-side scalar reality theorem
