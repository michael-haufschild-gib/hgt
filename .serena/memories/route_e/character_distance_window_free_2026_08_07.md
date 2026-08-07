# Window-free character-distance lower bound (2026-08-07)

Repair (1) of `mem:route_e/halasz_parameter_audit_no_decay_yet_2026_08_07`, first half. Two modules,
green (9339 jobs), axiom-clean, umbrella-wired.

`RHTower/Sieve/PrimeCosineSumUpper.sum_cos_div_prime_le_of_ge` — the mirror of the corpus's
`PrimeCosineSum.sum_cos_div_prime_ge_of_le`. Both passage devices are two-sided
(`abs_tsum_prime_tail_re_le`, `PrimeSigmaShift.abs_sum_weight_shift_le`), so the upper direction is the
same proof with the final `linarith` flipped. Constants identical:
`+ 2(log 2 + 2(2·mertensFirstConst + 1/2))/log 2 + (1 + log 4)`.

`RHTower/Sieve/CharacterDistanceLower`:
- `charFn_mul_conj_re : (charFn t p * conj (charFn u p)).re = cos((t-u) log p)` (via
  `Complex.exp_ofReal_mul_I_re`).
- `mulDistSqPair_charFn_eq_sub : D(χ_t, χ_u; P)² = ∑_{p∈P} 1/p - ∑_{p∈P} cos((t-u) log p)/p`.
- `le_mulDistSqPair_charFn (hz : 3 ≤ z) (hL : series ≤ L) :
   logLog z - mertensSecondLowerConst - L - C_tail - (1 + log 4) ≤ D(χ_t,χ_u; primesLE z)²`
  using `MertensSecond.le_mertensS`.

**No `|t-u| log z ≤ π` restriction anywhere** — that is the whole point, and it is what
`HalaszWindow.sq_sub_mul_logSqWeight_le` cannot give.

## To finish repair (1)

Need `L ≍ log log(2+|t-u|)`: feed `ZetaTruncated.norm_riemannZeta_le_log_uniform`
(`‖ζ w‖ ≤ 2 + e·log N + e/‖w-1‖ + 2e`, for `1 - 1/log N ≤ w.re`, `‖w‖ ≤ N`) through
`ZetaLogPrimeSum.abs_log_norm_riemannZeta_sub_tsum_re_le` (`|log‖ζ‖ - ∑'_p Re(p^{-s})| ≤ ∑'_p‖p^{-s}‖²`,
and my `tsum_primes_rpow_two_le` bounds that defect by 49/100). Then `DistanceTriangle` gives global
uniqueness of the close frequency, replacing the lossy covering step.
