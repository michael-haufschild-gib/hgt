# The Dirichlet series as a Mellin transform of its partial sums

- **ID:** partial-sum-mellin-bridge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For `f : ℕ → ℂ` with `f 0 = 0` and `‖f n‖ ≤ 1`, and `Re s > 1`,

  `L(f, s) = s · ∫_1^∞ S_f(⌊t⌋) · t^(-s-1) dt`,   `S_f(m) = ∑_{k ≤ m} f(k)`.

  Two instances, both unconditional:

  * `ζ(s) = s ∫_1^∞ ⌊t⌋ t^(-s-1) dt`;
  * `1/ζ(s) = s ∫_1^∞ M(⌊t⌋) t^(-s-1) dt`, `M` the Mertens function.

## Module

`formal/GaloisForLFunctions/RHTower/Sieve/PartialSumMellinBridge.lean` —
`LSeries_eq_mul_integral_sum_Icc`, `riemannZeta_eq_mul_integral_floor`,
`inv_riemannZeta_eq_mul_integral_mertens`, plus `norm_sum_Icc_zero_le`.

## What it is built from

Nothing analytic was rebuilt. mathlib's improper Abel summation
(`tendsto_sum_mul_atTop_nhds_one_sub_integral₀`) does the interchange; the corpus's own cpow lemmas
(`RHTower.differentiableAt_ofReal_cpow_neg`, `RHTower.deriv_ofReal_cpow_neg` from
`ZetaPartialSumStrip`) discharge the differentiability and the derivative; `RHTower.zetaSeriesCoeff`
and `RHTower.sum_zetaCoeff` give the zeta instance; `RHTower.LSeries_moebius_eq_inv_riemannZeta`
(`SquarefreeMoebiusNormalization`) gives the Mertens instance. The three hypotheses of the Abel
theorem — the limit `n^(-s) S(n) → 0`, the domination `deriv · S = O(t^(-σ))`, and integrability at
infinity — are discharged from `‖S_f(m)‖ ≤ m` alone.

## Why it matters

The kernel attached to the vertical line here is `1/s`, decaying like `1/|t|`. Every earlier Perron
passage in the corpus goes through a *smoothed* cutoff, whose kernel is the Mellin transform of the
smoothing profile: that is what forced the two integrations by parts and the `∫‖W‖ ≍ N log N` estimate
behind the `(log N)²` loss of the pointwise Halász route
(`halasz-programme-session-index.md`, no-go 1). The bridge is exact — no truncation error, no smoothing
profile, no parameter `H` — and it holds for every bounded coefficient sequence.

It is also the identity underlying the Mertens-type criteria: `M(x) = O(x^θ)` makes the right-hand side
of the second instance converge for `Re s > θ`. No criterion is stated here — the corpus's own audit
(`rh-criterion-reencoding-template`) records that re-encoding RH as another criterion does not advance
the proof — but the identity is the unconditional half that any such argument consumes, and it was
missing.

## Next

The mean-square input named by no-go 3, in the form free of the length obstruction: Plancherel for the
Mellin transform on the line `Re s = σ > 1`,

`∫_0^∞ ‖S_f(e^u)‖² e^(-2σu) du = (1/2π) ∫_ℝ ‖L(f, σ+iτ)/(σ+iτ)‖² dτ`,

whose right-hand side pairs the corpus's damped Euler bound against an *integrable* kernel.
