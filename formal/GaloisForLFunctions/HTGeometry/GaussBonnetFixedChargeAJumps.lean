import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAClapeyron

/-!
# Actual entropy and volume discontinuities on the fixed-charge model-A curve

Both jumps are strictly positive. Their exact normalized formulas will
bound the Clapeyron tangent between the two local thermal responses. The
entropy reference cancels; equal Gibbs values give positive latent heat.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbFixedChargeAClapeyronSlope (w φ τ : ℝ) : ℝ :=
  egbFixedChargeAEntropyJump w φ τ / egbFixedChargeAVolumeJump w φ τ

theorem egbFixedChargeA_coupling_scaling (w φ τ : ℝ) :
    (exp w * sin φ) ^ 2 = egbFixedChargeALargeRadius w φ τ ^ 2 * egbFixedChargeACouplingWeight τ φ := by
  have h := egbFixedChargeA_coupling_square w φ τ
  rw [egbCoexistenceACouplingRoot_sq, egbFixedChargeALogScale_exp, egbFixedChargeAAngle_coupling] at h
  exact h.symm

theorem egbFixedChargeA_entropy_jump_reference (w φ τ l : ℝ) :
    egbEntropyA (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) -
      egbEntropyA (exp w * sin φ) l (egbFixedChargeASmallRadius w φ τ) = egbFixedChargeAEntropyJump w φ τ := by
  have h := egbCoexistenceA_entropy_jump (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ) l
  have h0 := egbCoexistenceA_entropy_jump (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ) 0
  rw [egbFixedChargeA_entropy_function, egbFixedChargeA_large_radius_transfer, egbFixedChargeA_small_radius_transfer] at h h0
  exact h.trans h0.symm

theorem egbFixedChargeAEntropyJump_pos (w φ τ : ℝ) : 0 < egbFixedChargeAEntropyJump w φ τ := by
  have h := egbCoexistenceA_entropy_jump (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ) 0
  rw [egbFixedChargeA_entropy_function, egbFixedChargeA_large_radius_transfer, egbFixedChargeA_small_radius_transfer] at h
  change egbFixedChargeAEntropyJump w φ τ = _ at h
  rw [h]
  exact egbCoexistenceAEntropyJump_pos _ _ _

theorem egbFixedChargeAEntropyJump_formula (w φ τ : ℝ) :
    egbFixedChargeAEntropyJump w φ τ = Real.pi * egbFixedChargeALargeRadius w φ τ ^ 2 *
      (1 - thermalRatio τ ^ 2 - 4 * egbFixedChargeACouplingWeight τ φ * log (thermalRatio τ)) := by
  have h := egbCoexistenceA_entropy_jump (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ) 0
  rw [egbFixedChargeA_entropy_function, egbFixedChargeA_large_radius_transfer, egbFixedChargeA_small_radius_transfer] at h
  change egbFixedChargeAEntropyJump w φ τ = _ at h
  rw [h]
  unfold egbCoexistenceAEntropyJump
  rw [egbFixedChargeALogScale_exp, egbFixedChargeAAngle_coupling]
  have hlog : log (thermalRatio τ) = -exp τ := log_exp _
  rw [hlog]
  ring

theorem egbFixedChargeAVolumeJump_formula (w φ τ : ℝ) :
    egbFixedChargeAVolumeJump w φ τ = 4 * Real.pi * egbFixedChargeALargeRadius w φ τ ^ 3 * (1 - thermalRatio τ ^ 3) / 3 := by
  unfold egbFixedChargeAVolumeJump egbThermodynamicVolume egbFixedChargeASmallRadius
  ring

theorem egbFixedChargeAVolumeJump_pos (w φ τ : ℝ) : 0 < egbFixedChargeAVolumeJump w φ τ := by
  have hz := thermalRatio_pos τ
  have hz1 := thermalRatio_lt_one τ
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  have h₁ : 0 < 1 - thermalRatio τ := sub_pos.mpr hz1
  have hgap : 0 < 1 - thermalRatio τ ^ 3 := by
    have h := mul_pos h₁ (show 0 < 1 + thermalRatio τ + thermalRatio τ ^ 2 by positivity)
    nlinarith
  rw [egbFixedChargeAVolumeJump_formula]
  positivity

theorem egbFixedChargeAClapeyronSlope_pos (w φ τ : ℝ) : 0 < egbFixedChargeAClapeyronSlope w φ τ :=
  div_pos (egbFixedChargeAEntropyJump_pos w φ τ) (egbFixedChargeAVolumeJump_pos w φ τ)

/-- Normalize only by the strictly positive volume jump; no temperature-derivative premise is used. -/
theorem egbFixedChargeA_pressure_derivative_relation (w φ τ : ℝ) :
    deriv (egbFixedChargeAPressure w φ) τ =
      egbFixedChargeAClapeyronSlope w φ τ * deriv (egbFixedChargeATemperature w φ) τ := by
  have h := egbFixedChargeA_clapeyron_cross w φ τ
  have hV := egbFixedChargeAVolumeJump_pos w φ τ
  calc
    _ = (egbFixedChargeAEntropyJump w φ τ * deriv (egbFixedChargeATemperature w φ) τ) /
        egbFixedChargeAVolumeJump w φ τ := (eq_div_iff hV.ne').2 (by simpa only [mul_comm] using h)
    _ = _ := by unfold egbFixedChargeAClapeyronSlope; ring

theorem egbFixedChargeA_enthalpy_jump (w φ τ : ℝ) :
    egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ) -
      egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ) =
    egbFixedChargeATemperature w φ τ * egbFixedChargeAEntropyJump w φ τ := by
  have h := egbFixedChargeA_equal_gibbs w φ τ 0
  unfold egbOffShellGibbsA at h
  unfold egbFixedChargeAEntropyJump
  linear_combination -h

theorem egbFixedChargeA_enthalpy_jump_pos (w φ τ : ℝ) :
    0 < egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ) -
      egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ) := by
  rw [egbFixedChargeA_enthalpy_jump]
  exact mul_pos (egbFixedChargeATemperature_pos w φ τ) (egbFixedChargeAEntropyJump_pos w φ τ)

end GaloisForLFunctions.HTGeometry
