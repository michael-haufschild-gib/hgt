import GaloisForLFunctions.RHTower.ZetaChiDualAtomStationary
import Mathlib.Analysis.Real.Pi.Bounds

open Complex
noncomputable section
namespace RHTower

/-- The compact-row dual coefficient has an exact real power norm. -/
theorem norm_zetaChiDualRowCoefficient {N x : ℝ} (hN : 0 < N) (hx : 0 < x)
    (s : ℂ) :
    ‖zetaChiDualRowCoefficient s N x‖ = (N / x) ^ (1 - s.re) / Real.sqrt N := by
  unfold zetaChiDualRowCoefficient
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg N),
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_cpow_eq_rpow_re_of_pos hN,
    Complex.sub_re, Complex.one_re]
  rw [show s.re - 1 = -(1 - s.re) by ring,
    Real.rpow_neg hx.le, Real.rpow_neg hN.le,
    Real.div_rpow hN.le hx.le]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- An eligible arithmetic saddle has coefficient of order `1/sqrt(N)`.
The estimate is uniform in the imaginary part and needs only `Re(s)>=0`. -/
theorem norm_zetaChiDualRowCoefficient_le {s : ℂ} (hs : 0 ≤ s.re)
    {N x M : ℝ} (hN : 0 < N) (hx : 0 < x) (hxN : x ≤ N) (hNM : N ≤ M * x) :
    ‖zetaChiDualRowCoefficient s N x‖ ≤ M / Real.sqrt N := by
  rw [norm_zetaChiDualRowCoefficient hN hx]
  have hbase : 1 ≤ N / x := (le_div_iff₀ hx).mpr (by simpa using hxN)
  have hp : (N / x) ^ (1 - s.re) ≤ N / x := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hbase (show 1 - s.re ≤ 1 by linarith)
  have hquot : N / x ≤ M := (div_le_iff₀ hx).mpr hNM
  exact div_le_div_of_nonneg_right (hp.trans hquot) (Real.sqrt_nonneg _)

/-- Integer or real saddles inside the dyadic height window have a uniform
coefficient bound independent of the compact variable's imaginary part. -/
theorem norm_zetaChiDualRowCoefficient_saddle_le {s : ℂ} (hs : 0 ≤ s.re)
    {N x : ℝ} (hN : 0 < N) (hx : 0 < x)
    (hl : N ≤ 2 * Real.pi * x) (hu : 2 * Real.pi * x ≤ 2 * N) :
    ‖zetaChiDualRowCoefficient s N x‖ ≤ (2 * Real.pi) / Real.sqrt N := by
  have hxN : x ≤ N := by nlinarith [Real.pi_gt_three]
  exact norm_zetaChiDualRowCoefficient_le hs hN hx hxN hl

end RHTower
