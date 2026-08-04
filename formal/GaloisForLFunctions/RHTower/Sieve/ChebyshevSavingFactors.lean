import GaloisForLFunctions.RHTower.Sieve.ChebyshevLimitTool
import GaloisForLFunctions.RHTower.Sieve.ChebyshevDecayAtChoice

/-!
# The two decaying factors

Every error term of the contour bound is a polynomial in `t = (log x)^{1/10}` times one of

    E(x) = exp(2(log x)^{1/20})·exp(-A t)          (the left edge's saving)
    G(x) = exp(2(log x)^{1/20})·exp(-(1-A) t)      (the right edge, divided by the height)

and both tend to `0` against any power of `t`, the first because `A > 0` and the second because
`A ≤ 1/2 < 1`.  The bound `A ≤ 1/2` is exactly what makes the truncation height beat the growth of
the right-edge decay constant.
-/

namespace RHTower.Sieve

open Filter Topology RHTower

/-- The left edge's saving. -/
noncomputable def savingE (x : ℝ) : ℝ :=
  Real.exp (2 * (Real.log x) ^ ((1 : ℝ) / 20))
    * Real.exp (-(zetaLowerA * (Real.log x) ^ ((1 : ℝ) / 10)))

/-- The right edge's saving, after division by the truncation height. -/
noncomputable def savingG (x : ℝ) : ℝ :=
  Real.exp (2 * (Real.log x) ^ ((1 : ℝ) / 20))
    * Real.exp (-((1 - zetaLowerA) * (Real.log x) ^ ((1 : ℝ) / 10)))

/-- The zero-free constant is at most one half. -/
theorem zetaLowerA_le_half : zetaLowerA ≤ 1 / 2 := by
  rw [zetaLowerA]
  norm_num

theorem savingE_pos (x : ℝ) : 0 < savingE x := by
  rw [savingE]; positivity

theorem savingG_pos (x : ℝ) : 0 < savingG x := by
  rw [savingG]; positivity

/-- **Any power of `t` against the left edge's saving.** -/
theorem tendsto_pow_savingE (n : ℕ) :
    Tendsto (fun x : ℝ => ((Real.log x) ^ ((1 : ℝ) / 10)) ^ n * savingE x) atTop (𝓝 0) := by
  have h := tendsto_logPoly_sqrt_saving n zetaLowerA_pos
  refine h.congr fun x => ?_
  rw [savingE]
  ring

/-- **Any power of `t` against the right edge's saving.** -/
theorem tendsto_pow_savingG (n : ℕ) :
    Tendsto (fun x : ℝ => ((Real.log x) ^ ((1 : ℝ) / 10)) ^ n * savingG x) atTop (𝓝 0) := by
  have hκ : (0 : ℝ) < 1 - zetaLowerA := by
    have := zetaLowerA_le_half
    linarith
  have h := tendsto_logPoly_sqrt_saving n hκ
  refine h.congr fun x => ?_
  rw [savingG]
  ring

/-- The ninth power of the height's exponent is the strip's denominator. -/
theorem rpow_nine_tenths_eq {L : ℝ} (hL : 0 ≤ L) :
    L ^ ((9 : ℝ) / 10) = (L ^ ((1 : ℝ) / 10)) ^ 9 := by
  rw [← Real.rpow_natCast (L ^ ((1 : ℝ) / 10)) 9, ← Real.rpow_mul hL]
  norm_num

/-- The height's exponent is at least one. -/
theorem one_le_logRoot {L : ℝ} (hL : 1 ≤ L) : 1 ≤ L ^ ((1 : ℝ) / 10) := by
  have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hL (by norm_num : (0 : ℝ) ≤ 1 / 10)
  rwa [Real.one_rpow] at h

end RHTower.Sieve
