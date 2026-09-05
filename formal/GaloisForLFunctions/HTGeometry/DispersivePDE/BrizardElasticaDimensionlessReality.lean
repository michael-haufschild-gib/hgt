import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaDimensionlessDynamics
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaInvariantRegions
import Mathlib.Tactic

/-!
# Reality of the dimensionless coordinate

The change `v = k₀s/(2√q₀)` used after paper equation (62) is a real coordinate only when
`q₀ > 0`.  Region II has `q₀ < 0`; there the same square-root formula has no real Jacobian and must
be interpreted through the paper's imaginary/extended-variable transport.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Squared Jacobian relating arclength to the paper's dimensionless variable. -/
noncomputable def dimensionlessArclengthFactor (k₀ q₀ : ℝˣ) : ℝ :=
  (k₀ : ℝ) ^ 2 / (4 * (q₀ : ℝ))

theorem regionI_dimensionlessArclengthFactor_pos
    (P : RegionIParameters) (k₀ : ℝˣ) :
    0 < dimensionlessArclengthFactor k₀ P.val.q₀ := by
  rw [dimensionlessArclengthFactor]
  exact div_pos ((show Even 2 by decide).pow_pos k₀.ne_zero)
    (mul_pos (by norm_num) P.property.2.2)

/-- Canonical positive real Jacobian in region I. -/
noncomputable def regionIDimensionlessJacobian
    (P : RegionIParameters) (k₀ : ℝˣ) : ℝ :=
  |(k₀ : ℝ)| / (2 * Real.sqrt (P.val.q₀ : ℝ))

theorem regionIDimensionlessJacobian_pos
    (P : RegionIParameters) (k₀ : ℝˣ) :
    0 < regionIDimensionlessJacobian P k₀ := by
  rw [regionIDimensionlessJacobian]
  exact div_pos (abs_pos.mpr k₀.ne_zero)
    (mul_pos (by norm_num) (Real.sqrt_pos.2 P.property.2.2))

theorem regionIDimensionlessJacobian_sq
    (P : RegionIParameters) (k₀ : ℝˣ) :
    regionIDimensionlessJacobian P k₀ ^ 2 =
      dimensionlessArclengthFactor k₀ P.val.q₀ := by
  rw [regionIDimensionlessJacobian, dimensionlessArclengthFactor, div_pow,
    sq_abs, mul_pow, Real.sq_sqrt (le_of_lt P.property.2.2)]
  ring

theorem regionII_dimensionlessArclengthFactor_neg
    (P : RegionIIParameters) (k₀ : ℝˣ) :
    dimensionlessArclengthFactor k₀ P.val.q₀ < 0 := by
  rw [dimensionlessArclengthFactor]
  exact div_neg_of_pos_of_neg ((show Even 2 by decide).pow_pos k₀.ne_zero)
    (mul_neg_of_pos_of_neg (by norm_num) P.property.2)

/-- No real change of variable can have the squared Jacobian printed in the paper on region II. -/
theorem regionII_no_real_dimensionlessJacobian
    (P : RegionIIParameters) (k₀ : ℝˣ) (σ : ℝ) :
    σ ^ 2 ≠ dimensionlessArclengthFactor k₀ P.val.q₀ := by
  intro h
  have hneg := regionII_dimensionlessArclengthFactor_neg P k₀
  nlinarith [sq_nonneg σ]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
