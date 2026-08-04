import GaloisForLFunctions.RHTower.Sieve.LogComparison

/-!
# Monotonicity of the majorant, and the size of the ratio

Two small facts needed to turn the majorant's variable from `t` into `v`.

The majorant is increasing in its last argument when all its coefficients are nonnegative, so the
comparison `t ≤ 2v²` may be substituted directly.  And the smoothing ratio satisfies
`L + 2 ≤ 3·exp(v)`, so the price it contributes is `exp(2v)` up to an absolute constant.
-/

namespace RHTower.Sieve

open Real

/-- **The majorant is increasing in its variable.** -/
theorem coeffMajorant_mono_t {C C' M₀ a : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (ha : 0 ≤ a) {t t' : ℝ} (ht : 0 ≤ t) (htt : t ≤ t') :
    coeffMajorant C C' M₀ a t ≤ coeffMajorant C C' M₀ a t' := by
  have ht' : (0 : ℝ) ≤ t' := le_trans ht htt
  have hexp : (0 : ℝ) ≤ Real.exp (22 / 4) := (Real.exp_pos _).le
  have hcoef : (0 : ℝ) ≤ 8 * C' + 4 + 2 * C := by linarith
  rw [coeffMajorant, coeffMajorant]
  gcongr

/-- **The ratio is at most three exponentials.** -/
theorem smoothRatio_add_two_le {N : ℝ} (hlog : 0 ≤ Real.log N) :
    smoothRatio N + 2 ≤ 3 * Real.exp ((Real.log N) ^ ((1 : ℝ) / 20)) := by
  have h1 : (1 : ℝ) ≤ Real.exp ((Real.log N) ^ ((1 : ℝ) / 20)) :=
    Real.one_le_exp (by positivity)
  rw [smoothRatio]
  linarith

/-- The ratio is nonnegative after the shift. -/
theorem zero_le_smoothRatio_add_two (N : ℝ) : 0 ≤ smoothRatio N + 2 := by
  have := smoothRatio_pos N
  linarith

end RHTower.Sieve
