import GaloisForLFunctions.RHTower.XiGaussianHeatTraceDisproof
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Schwartz energy on the real ordinates of the actual Xi divisor

The real spectral coordinates retain every analytic multiplicity. Schwartz
decay and the unconditional spectral sector bound give square summability at
every positive scale, providing a real-axis reference for complex heat energy.
-/

open scoped SchwartzMap
noncomputable section

namespace RHTower

/-- Sampling a Schwartz function at all scaled Xi ordinates has finite square energy. -/
theorem summable_xiRealAxisSchwartz_norm_sq (f : SchwartzMap ℝ ℂ)
    (r : {r : ℝ // 0 < r}) :
    Summable (fun q : XiZeroCopy => ‖f ((r : ℝ) * (xiSpectralPoint q).re)‖ ^ 2) := by
  obtain ⟨C, hCpos, hC⟩ := f.decay 1 0
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _
    (xiSpectralPoint_inv_sq_summable.mul_left (2 * C ^ 2 / (r : ℝ) ^ 2))
  · intro q
    have hN : 0 < ‖xiSpectralPoint q‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)) _
    have hsector : ‖xiSpectralPoint q‖ ^ 2 ≤ 2 * (xiSpectralPoint q).re ^ 2 := by
      have hs := xiSpectralPoint_normSq_lt_two_mul_sq_re q
      rw [Complex.sq_norm]
      simp only [Complex.normSq_apply, pow_two, Complex.mul_re] at hs ⊢
      nlinarith only [hs, sq_nonneg (xiSpectralPoint q).im]
    have hd := hC ((r : ℝ) * (xiSpectralPoint q).re)
    rw [norm_iteratedFDeriv_zero, pow_one, Real.norm_eq_abs] at hd
    have hd2 := pow_le_pow_left₀ (by positivity) hd 2
    rw [mul_pow, sq_abs, mul_pow] at hd2
    have hs := mul_le_mul_of_nonneg_right hsector
      (mul_nonneg (sq_nonneg (r : ℝ))
        (sq_nonneg ‖f ((r : ℝ) * (xiSpectralPoint q).re)‖))
    calc
      _ ≤ (2 * C ^ 2) / ((r : ℝ) ^ 2 * ‖xiSpectralPoint q‖ ^ 2) := by
        apply (le_div_iff₀ (mul_pos (pow_pos r.property _) hN)).mpr
        nlinarith only [hd2, hs]
      _ = _ := by ring

/-- Positive reference energy on the real ordinates, retaining the full divisor multiplicities. -/
def xiRealAxisSchwartzEnergy (f : SchwartzMap ℝ ℂ) (r : {r : ℝ // 0 < r}) : ℝ :=
  ∑' q : XiZeroCopy, ‖f ((r : ℝ) * (xiSpectralPoint q).re)‖ ^ 2

theorem xiRealAxisSchwartzEnergy_nonneg (f : SchwartzMap ℝ ℂ)
    (r : {r : ℝ // 0 < r}) : 0 ≤ xiRealAxisSchwartzEnergy f r :=
  tsum_nonneg fun _ => sq_nonneg _

end RHTower
