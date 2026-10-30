# A Gamma reserve for logarithmic atoms at every fixed overlap

- **ID:** tilted-spline-gamma-reserve-at-bounded-overlap
- **Stage:** 3-formalized
- **Type:** THEOREM

## Target

For the explicit unit-supported profile `φ(u)=e^(8u-4) B(8u-4)`, where
`B=U_1^{*4}`, and every `c>0`, there are constants `a_c>0`, `b_c≥0` such that,
for every `N≥1`,

`Gamma(Σ_(n≤N)x_n φ((u-log n)/(c/N))) / ((c/N)∫φ²)
 ≥ (a_c log N-b_c) Σ_(n≤N)x_n²`.

All real coefficient packets are included. No real Fourier nonvanishing,
frame lower bound, or source estimate is left as an analytic premise.

Put `M=∫φ²` and `m_c=min_[c,101c]|φ̂|²>0`. The proof gives
`a_c=48c m_c/(2πM)` and `b_c=(G₀+log 2)(1+2ce^c)`, where `G₀` is the
established global Gamma offset.

## Source mechanism

The existing cubic-spline transform has only real zeros. Multiplication by
`e^u` shifts its argument off the real axis, so the normalized profile has
strictly positive squared Fourier modulus on `[c,101c]`.
The established logarithmic Montgomery–Vaughan bound retains `48N Σx_n²`
on `[N,101N]`. Exact atomic Fourier factorization transfers this reserve to
the actual test. The Gamma symbol is at least `log N-O(1)` there and globally
bounded below. Finite overlap bounds the total physical mass by
`(1+2ce^c)(c/N)(∫φ²)Σx_n²`, paying the global negative part.

## Complete-form connection

At a sufficiently small fixed-fraction cutoff, the low block is separated.
`abs_archCross_le_of_ordered` already bounds its Gamma interaction with the
high block by section mass. Prime-edge localization and the directed
non-ratio defect estimate then supply arithmetic payments. The full Weil
reserve remains a separate obligation; this card asserts only the actual
Gamma source bound. Profile and frame helpers receive no separate credit.

## Formal inputs

`TheOverlapGramHasBoundedRows.lean`, declaration
`integral_atomicTest_sq_le_fixed_overlap`, proves the physical mass upper bound.
Direct Lean check passed with
standard logical axioms only; SSHA umbrella import added. The main Gamma
source leaf is `TheTiltedSplineKeepsAGammaReserveAtEveryOverlap.lean`, declaration
`GaloisForLFunctions.SpacingScaleHarmonicAnalysis.exists_tiltedUnitSpline_archForm_reserve`.
Its exact raw source and normalization passed the direct no-olean Lean check.
The Fourier nonvanishing theorem and the final source theorem depend only on
`propext`, `Classical.choice`, and `Quot.sound`. Both leaves are in the SSHA umbrella.

## Significance

Supplies the high-block Gamma coercivity missing from the macroscopic-overlap
complete-Weil programme. Counted as one actual source contribution, including
the profile, Fourier floor, and Gram helpers.
