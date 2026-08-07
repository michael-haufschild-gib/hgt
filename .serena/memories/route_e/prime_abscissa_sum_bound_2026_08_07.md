# The trivial size of the prime sum, and the Halász input (2026-08-07)

`RHTower/Sieve/PrimeAbscissaSumBound.lean` — green (9022 jobs), axiom-clean, in the umbrella.

`primeAbscissaSum_le (hσ : 1 < σ) : primeAbscissaSum σ ≤ Real.log (1 + 1/(σ-1)) + 1`

and the capstone

`norm_tsum_twistedSummand_le_mul_exp_neg_dist :
  ‖∑' n, f n * n^(-s)‖ ≤ (1 + 1/(s.re - 1)) * exp(7/2 - mulDistSqTsum f s)`.

## Chain used (all reuse, nothing reproved)

- mathlib integral test `AntitoneOn.tsum_comp_add_le_integral 1` + `integral_Ioi_rpow_of_lt` +
  `integrableOn_Ioi_rpow_of_lt` ⇒ `∑_{n≥2} n^{-σ} ≤ 1/(σ-1)` (`tsum_shift_rpow_neg_le`).
- corpus `GaloisForLFunctions.norm_riemannZeta_le_halfPlane` + `zetaHalfPlaneBound` ⇒
  `ζ(σ) ≤ 1 + 1/(σ-1)`.
- corpus `Sieve/ZetaLogPrimeSum.abs_log_norm_riemannZeta_sub_tsum_re_le` ⇒ `P(σ) ≤ log ζ(σ) + defect`,
  with the defect `∑_p ‖p^{-σ}‖² ≤ 49/100` from my own `tsum_primes_rpow_two_le`.

**Why `log ζ` and not `ζ`:** bounding `P(σ)` by the whole ζ-sum gives `1/(σ-1) = log x` and makes the
Euler bound vacuous. The log is the whole point.

## Traps hit

- `HTGeometry/ZetaGammaFieldHypertranscendence.lean` is in namespace **`GaloisForLFunctions`**, NOT
  `GaloisForLFunctions.HTGeometry` (it does `open _root_.HTGeometry` internally). Qualify as
  `GaloisForLFunctions.zetaHalfPlaneBound` / `.norm_riemannZeta_le_halfPlane`.
- `inv_le_inv_of_le` is gone; use `one_div_le_one_div_of_le` + `simpa [one_div]`.
- `ring` will NOT prove `-1 / -(σ-1) = 1/(σ-1)` (it cannot push the negation through the inverse);
  use `rw [neg_div, div_neg, neg_neg]`.
- `Complex.ofReal_cpow (hx : 0 ≤ x) (y : ℝ) : ((x^y : ℝ) : ℂ) = (x:ℂ)^(y:ℂ)` lives in
  `Analysis/SpecialFunctions/Pow/Real.lean` — this is the cast for reading a real abscissa power as a
  cpow, and it is what the polar split `p^{-s} = p^{-σ}·p^{-it}` will need.

See `mem:route_e/multiplicative_euler_bound_built_2026_08_07`,
`mem:route_e/multiplicative_euler_bound_distance_form_2026_08_07`.
