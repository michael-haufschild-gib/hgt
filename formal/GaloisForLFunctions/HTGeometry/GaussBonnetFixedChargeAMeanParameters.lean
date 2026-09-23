import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceASymmetricCoordinates
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalLimits
import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAKernelMomentLimits

/-!
# Physical coexistence recentered at the arithmetic mean radius

The actual two radii equal (1 ± d) times their mean. The effective
charge weight and thermodynamic denominator then depend on d² and the
logarithmic kernel. These are exact identities along the fixed-charge
curve, including both zero electric charge and zero Gauss–Bonnet coupling.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbFixedChargeAMeanRadius (w φ τ : ℝ) : ℝ :=
  (egbFixedChargeALargeRadius w φ τ + egbFixedChargeASmallRadius w φ τ) / 2

def egbFixedChargeAMeanWeight (τ φ : ℝ) : ℝ :=
  egbFixedChargeAWeight τ φ * (1 + egbCoexistenceASymmetricRatio τ) ^ (2 : ℕ)

def egbFixedChargeAMeanCoupling (τ φ : ℝ) : ℝ :=
  egbFixedChargeAFraction φ * egbFixedChargeAMeanWeight τ φ

def egbFixedChargeAMeanDenominator (τ φ : ℝ) : ℝ :=
  6 - 2 * egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) +
    4 * egbFixedChargeAMeanCoupling τ φ * egbCoexistenceALogKernel τ

theorem egbFixedChargeAMeanRadius_pos (w φ τ : ℝ) : 0 < egbFixedChargeAMeanRadius w φ τ :=
  div_pos (add_pos (egbFixedChargeALargeRadius_pos w φ τ) (egbFixedChargeA_radii_order w φ τ).1) (by norm_num)

theorem egbFixedChargeAMeanWeight_pos (τ φ : ℝ) : 0 < egbFixedChargeAMeanWeight τ φ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAMeanWeight
  exact mul_pos (egbFixedChargeAWeight_pos τ φ) (by positivity)

theorem egbFixedChargeAMeanCoupling_nonneg (τ φ : ℝ) : 0 ≤ egbFixedChargeAMeanCoupling τ φ :=
  mul_nonneg (egbFixedChargeAFraction_bounds φ).1 (egbFixedChargeAMeanWeight_pos τ φ).le

theorem egbFixedChargeAMeanRadius_formula (w φ τ : ℝ) :
    egbFixedChargeAMeanRadius w φ τ = egbFixedChargeALargeRadius w φ τ / (1 + egbCoexistenceASymmetricRatio τ) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAMeanRadius egbFixedChargeASmallRadius
  calc
    _ = egbFixedChargeALargeRadius w φ τ * (1 + thermalRatio τ) / 2 := by ring
    _ = _ := by rw [egbCoexistenceASymmetricRatio_radius_sum]; ring

theorem egbFixedChargeA_large_radius_mean (w φ τ : ℝ) :
    egbFixedChargeALargeRadius w φ τ = (1 + egbCoexistenceASymmetricRatio τ) * egbFixedChargeAMeanRadius w φ τ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbFixedChargeAMeanRadius_formula]
  field_simp

theorem egbFixedChargeA_small_radius_mean (w φ τ : ℝ) :
    egbFixedChargeASmallRadius w φ τ = (1 - egbCoexistenceASymmetricRatio τ) * egbFixedChargeAMeanRadius w φ τ := by
  unfold egbFixedChargeASmallRadius
  rw [egbFixedChargeA_large_radius_mean, ← mul_assoc, egbCoexistenceASymmetricRatio_cross]

theorem egbFixedChargeA_radius_gap_mean (w φ τ : ℝ) :
    egbFixedChargeALargeRadius w φ τ - egbFixedChargeASmallRadius w φ τ =
      2 * egbCoexistenceASymmetricRatio τ * egbFixedChargeAMeanRadius w φ τ := by
  rw [egbFixedChargeA_large_radius_mean, egbFixedChargeA_small_radius_mean]
  ring

theorem egbFixedChargeA_mean_effective_scale (w φ τ : ℝ) :
    egbFixedChargeAMeanRadius w φ τ ^ (2 : ℕ) * egbFixedChargeAMeanWeight τ φ = exp w ^ (2 : ℕ) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbFixedChargeAMeanRadius_formula]
  unfold egbFixedChargeAMeanWeight
  calc
    _ = egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ) * egbFixedChargeAWeight τ φ := by field_simp
    _ = _ := egbFixedChargeA_effective_scale w φ τ

theorem egbFixedChargeA_mean_coupling_scale (w φ τ : ℝ) :
    egbFixedChargeAMeanRadius w φ τ ^ (2 : ℕ) * egbFixedChargeAMeanCoupling τ φ = (exp w * sin φ) ^ (2 : ℕ) := by
  unfold egbFixedChargeAMeanCoupling egbFixedChargeAFraction
  calc
    _ = (egbFixedChargeAMeanRadius w φ τ ^ (2 : ℕ) * egbFixedChargeAMeanWeight τ φ) * sin φ ^ (2 : ℕ) := by ring
    _ = _ := by rw [egbFixedChargeA_mean_effective_scale]; ring

theorem egbFixedChargeAMeanCoupling_formula (τ φ : ℝ) :
    egbFixedChargeAMeanCoupling τ φ = egbFixedChargeACouplingWeight τ φ * (1 + egbCoexistenceASymmetricRatio τ) ^ (2 : ℕ) := by
  unfold egbFixedChargeAMeanCoupling egbFixedChargeAMeanWeight egbFixedChargeACouplingWeight
  ring

theorem egbFixedChargeAMeanDenominator_formula (τ φ : ℝ) :
    egbFixedChargeAMeanDenominator τ φ = (1 + egbCoexistenceASymmetricRatio τ) ^ (2 : ℕ) * egbFixedChargeADenominator τ φ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAMeanDenominator egbFixedChargeADenominator
  rw [egbFixedChargeAMeanCoupling_formula, egbCoexistenceASymmetricRatio_shape]
  field_simp

theorem egbFixedChargeAMeanDenominator_pos (τ φ : ℝ) : 0 < egbFixedChargeAMeanDenominator τ φ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbFixedChargeAMeanDenominator_formula]
  exact mul_pos (by positivity) (egbFixedChargeADenominator_pos τ φ)

theorem egbFixedChargeAMeanRadius_critical_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeAMeanRadius w φ) atBot (𝓝 (egbFixedChargeACriticalRadius w φ)) := by
  have h := ((egbFixedChargeALargeRadius_critical_limit w φ).add (egbFixedChargeASmallRadius_critical_limit w φ)).div_const 2
  convert h using 1 <;> first | rfl | ring

theorem egbFixedChargeAMeanWeight_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanWeight τ φ) atBot (𝓝 (egbFixedChargeACriticalWeight φ)) := by
  have hd : Tendsto (fun τ => (1 + egbCoexistenceASymmetricRatio τ) ^ (2 : ℕ)) atBot (𝓝 (1 : ℝ)) := by
    simpa only [add_zero, one_pow] using ((tendsto_const_nhds (x := (1 : ℝ))).add egbCoexistenceASymmetricRatio_critical_limit).pow 2
  simpa only [egbFixedChargeAMeanWeight, mul_one] using (egbFixedChargeAWeight_critical_limit φ).mul hd

theorem egbFixedChargeAMeanCoupling_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanCoupling τ φ) atBot (𝓝 (egbFixedChargeACriticalCouplingWeight φ)) := by
  exact (tendsto_const_nhds (x := egbFixedChargeAFraction φ)).mul (egbFixedChargeAMeanWeight_critical_limit φ)

theorem egbFixedChargeAMeanDenominator_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanDenominator τ φ) atBot (𝓝 (6 + 12 * egbFixedChargeACriticalCouplingWeight φ)) := by
  have hd : Tendsto (fun τ => (1 + egbCoexistenceASymmetricRatio τ) ^ (2 : ℕ)) atBot (𝓝 (1 : ℝ)) := by
    simpa only [add_zero, one_pow] using ((tendsto_const_nhds (x := (1 : ℝ))).add egbCoexistenceASymmetricRatio_critical_limit).pow 2
  simp only [egbFixedChargeAMeanDenominator_formula]
  simpa only [one_mul] using hd.mul (egbFixedChargeADenominator_critical_limit φ)

end GaloisForLFunctions.HTGeometry
