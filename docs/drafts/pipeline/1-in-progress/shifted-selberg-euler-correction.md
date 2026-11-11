# Shifted harmonic limits for the linear detector

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** A111, `levinson-gate-from-below-square-root-twists.md`.

## Target

For `L=log N`, a polynomial `P` with `P(0)=0`, and `v_N→v`, prove the
coupled arithmetic limit

`L Σ_{h,k≤N} μ(h)μ(k)(hk)^(v_N/L) gcd(h,k)^(1−2v_N/L)/(hk)`
`·P(1−log h/L)P(1−log k/L) → ∫₀¹ [P′(1−t)−vP(1−t)]² dt`.

Also prove its first two directional derivatives in the independent
parameters `(c,v)`, evaluated at `c=−2v`. The direct detector uses direction
`(κ,ν)=(−2,2)` and the reflected detector uses `(2,0)`.

## Established inputs

The exact Euler convolution writes the finite gcd form as corrected
harmonic rows. Absolute correction fibres push forward to a summable
pair majorant; their unshifted total mass is one.
See `3-formalized/shifted-selberg-euler-factorization.md`.

For the normalized Möbius transform `K_P(L,u,v)`, the kernel error is
controlled by `|F(Lu)−1|` and `∫₀¹|F(Lx)−1| dx`, where `F(y)→1` is bounded.
Thus `K_P→P′−vP` uniformly for `δ≤u≤1` and compact shift intervals, with a
common bound on the full cutoff. The harmonic endpoint mass is at most
`2/(k+1)` in the limit, using the majorant `2t^k` near `t=1`.

The endpoint estimate, mean absolute profile replacement, product
replacement, and fixed-dilation polynomial row limits are formalized.
`TheCoupledPolynomialRowsConverge` allows every fixed logarithmic power
and every convergent normalized-shift sequence.

Complex continuation and Cauchy's estimate bound the normalized
correction jet of order `j` by `j! exp(4(|C|+1))` times its absolute fibre.
Positive-order jets vanish along every bounded moving-centre sequence.
These fibre statements are formalized in
`TheCorrectionJetsKeepTheSummableEnvelope`.

## Derivative mechanism

Write `RP(x)=(1−x)P(x)`. A directional derivative of a harmonic row
inserts `κt` or replaces either profile by `νRP`. Differentiating the
Euler correction gives a fourth term. Its positive-order normalized
jets vanish under the common summable majorant.

With `A_P=P′−vP`, `A_Q=Q′−vQ`, and `β=κ+2ν`, the limiting first and
second derivative integrands are

`βt A_P A_Q − ν(P A_Q + A_P Q)`,

`β²t² A_P A_Q − 2νβt(P A_Q + A_P Q) + 2ν² P Q`.

All profiles are evaluated at `1−t`. For `P=Q`, the direct integrands
are `A²`, `2tA²−4PA`, and `4t²A²−16tPA+8P²`; the reflected ones are
`A²`, `2tA²`, and `4t²A²`, with their respective normalized shifts.

## Formalization boundary

`TheCoupledEulerCorrectionPreservesThePolynomialLimit` now formalizes
summation over all correction pairs, with one bound for all retained
dilations and logarithmic powers. The coefficient-jet pair majorants,
principal-row derivative recurrence, and literal coupled gcd-form limit
also passed Lean. `TheCorrectedRowDerivativesHaveVanishingCorrectionTerms`
formalizes the exact summed derivative recurrence and vanishing summed
positive-order correction jets. `TheCorrectedPolynomialJetsConverge` and
`TheShiftedSelbergFormKeepsItsFirstTwoDerivatives` prove both literal
gcd-form derivative limits. `TheCorrectedJetsAreUniformlyLipschitz` and
`TheCorrectedJetLimitsAllowArbitraryHeights` prove joint convergence for
arbitrary cutoffs tending to infinity and convergent shifts. The frozen
original gcd-sum formulation awaits compilation.

The parent gate additionally needs varying detector-profile coefficients,
the zeta-pole and chi-weight main-term jets, fixed-mollifier coefficient
perturbation, and uniform dyadic block assembly. The pole residue and
its first two scaled zeta derivatives have separate Lean proof drafts.
