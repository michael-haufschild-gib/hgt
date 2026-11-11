import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailReferenceRemainder
import GaloisForLFunctions.RHTower.EulerDeletionPowerSumRemainder

/-!
# The finite part of a power prefix

The centered Euler continuation identifies the constant left after the
power integral is removed. The elementary uniform discrepancy bound also
shows that every negative power kills the remaining finite-prefix error.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open _root_.RHTower.DeletionMixedRefinement

theorem ofReal_powerTailPrefix (a : ℝ) (N : ℕ) :
    (powerTailPrefix a N : ℂ) = rawPrefix (a : ℂ) N := by
  have he : powerTailPrefix a N = ∑ n ∈ range N, powerTailWeight a (n + 1) := by
    simpa only [powerTailPrefix, Nat.floor_natCast, RHTower.sourcePartialSum] using
      (RHTower.sum_range_succ_eq_sourcePartialSum (powerTailWeight a) N).symm
  rw [he, Complex.ofReal_sum, rawPrefix]
  apply sum_congr rfl
  intro n _
  rw [powerTailWeight, Complex.ofReal_cpow (Nat.cast_nonneg _)]
  simp only [Complex.ofReal_neg, Complex.ofReal_natCast, kernel]

/-- Removing the power integral leaves the continued zeta value. -/
theorem tendsto_powerTailPrefix_finitePart {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun N : ℕ =>
      ((powerTailPrefix a N - (N : ℝ) ^ (1 - a) / (1 - a) : ℝ) : ℂ)) atTop
      (𝓝 (riemannZeta (a : ℂ))) := by
  have hs : -1 < (a : ℂ).re := by simpa only [Complex.ofReal_re] using
    (show -1 < a by linarith only [ha])
  have hs1 : (a : ℂ) ≠ 1 := by exact_mod_cast ha1.ne
  have hz := (tendsto_nat_cpow_zero (z := -(a : ℂ)) (by
    simp only [Complex.neg_re, Complex.ofReal_re]
    linarith only [ha])).div_const (2 : ℂ)
  have h := (tendsto_centeredPowerPrefix hs hs1).add hz
  simp only [zero_div, add_zero] at h
  refine h.congr fun N => ?_
  simp only [kernel, sub_add_cancel, Complex.ofReal_sub, Complex.ofReal_div,
    ofReal_powerTailPrefix, Complex.ofReal_cpow (Nat.cast_nonneg N),
    Complex.ofReal_one, Complex.ofReal_natCast]

/-- Every strictly negative power kills the bounded prefix discrepancy. -/
theorem tendsto_rpow_mul_powerTailPrefix_error {a θ : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hθ : 0 < θ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (-θ) *
      (powerTailPrefix a N - (N : ℝ) ^ (1 - a) / (1 - a))) atTop (𝓝 0) := by
  have hb : 0 < 1 - a := by linarith only [ha1]
  have hz := ((tendsto_rpow_neg_atTop hθ).comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    .mul_const (1 / (1 - a))
  simp only [zero_mul] at hz
  apply squeeze_zero_norm' _ hz
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hp := powerTailPrefix_sub_integral_bounds ha ha1 hNp.le
  have he : |powerTailPrefix a N - (N : ℝ) ^ (1 - a) / (1 - a)| ≤ 1 / (1 - a) :=
    abs_le.mpr ⟨hp.1, hp.2.trans (by positivity)⟩
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hNp.le _)]
  exact mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hNp.le _)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
