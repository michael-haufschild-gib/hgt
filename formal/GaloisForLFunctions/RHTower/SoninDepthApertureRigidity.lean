import GaloisForLFunctions.RHTower.BurnolSoninCrossApertureRiesz
import GaloisForLFunctions.RHTower.SoninDepthMatching

/-!
# `(18c)`–`(18e)` with the aperture rigidity discharged

`prime-wold-accelerated-type-modular-drift-law` §5.4 matches the Sonin aperture depth to the Wold
first trace and concludes that the aperture escape of an off-axis annihilator character is exactly
the reflected Wold–Gamma gauge `exp(2 d_rho / a_x)`.

The two-sided aperture rigidity `(18c)` is the tree's own cross-aperture theorem
(`norm_burnolExtendedSoninEvaluationVector_geometric_lower` and `..._geometric_upper`), so the
conclusion `(18e)` needs no hypothesis at all: it is the depth schedule applied to that theorem.
-/

open Complex Real

noncomputable section

namespace RHTower

/-- **`(18e)`, unconditional.**  Under the source-defined depth schedule
`N_x = ⌊2 / (a_x log r)⌋` the completed Mellin evaluation vector at the aperture `b_x = r^(-N_x) a`
is squeezed between two fixed multiples of the reflected Wold–Gamma gauge `exp(2 d / a_x)`, with
`d = |Re w - 1/2|` the horizontal displacement.  Both constants are independent of the cutoff. -/
theorem norm_burnolExtendedSoninEvaluationVector_soninDepth_bounds
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a r ax : ℝ} (ha : 0 < a) (hr : 1 < r)
    (hax : 0 < ax) :
    ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ *
        (r ^ (-|w.re - 1 / 2|) * Real.exp (2 * |w.re - 1 / 2| / ax)) ≤
      ‖burnolExtendedSoninEvaluationVector w ((r ^ soninDepth ax r)⁻¹ * a) hlo hhi
        (mul_pos (inv_pos.mpr (pow_pos (lt_trans zero_lt_one hr) (soninDepth ax r))) ha)‖ ∧
      ‖burnolExtendedSoninEvaluationVector w ((r ^ soninDepth ax r)⁻¹ * a) hlo hhi
        (mul_pos (inv_pos.mpr (pow_pos (lt_trans zero_lt_one hr) (soninDepth ax r))) ha)‖ ≤
      soninApertureConstant w / Real.sqrt 2 * a ^ (-|w.re - 1 / 2|) *
        Real.exp (2 * |w.re - 1 / 2| / ax) := by
  have hd : (0 : ℝ) ≤ |w.re - 1 / 2| := abs_nonneg _
  have hlow := norm_burnolExtendedSoninEvaluationVector_geometric_lower hlo hhi ha hr.le
    (soninDepth ax r)
  have hup := norm_burnolExtendedSoninEvaluationVector_geometric_upper hlo hhi ha hr.le
    (soninDepth ax r)
  have hC₁ : (0 : ℝ) ≤ ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ := norm_nonneg _
  have hC₂ : (0 : ℝ) ≤ soninApertureConstant w / Real.sqrt 2 * a ^ (-|w.re - 1 / 2|) := by
    have := soninApertureConstant_nonneg w
    positivity
  exact norm_le_of_soninDepth_rigidity (a := ax) (r := r) (d := |w.re - 1 / 2|)
    (C₁ := ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖)
    (C₂ := soninApertureConstant w / Real.sqrt 2 * a ^ (-|w.re - 1 / 2|))
    (K := ‖burnolExtendedSoninEvaluationVector w ((r ^ soninDepth ax r)⁻¹ * a) hlo hhi
        (mul_pos (inv_pos.mpr (pow_pos (lt_trans zero_lt_one hr) (soninDepth ax r))) ha)‖)
    hax hr hd hC₁ hlow hup hC₂

end RHTower
