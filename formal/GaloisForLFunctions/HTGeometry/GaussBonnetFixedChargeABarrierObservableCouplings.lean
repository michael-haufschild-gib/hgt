import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeABarrierCriticalLimit
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalJumpExponents
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalHeatAmplitude

/-!
# Barrier couplings to the actual thermodynamic jumps and responses

The barrier has a finite positive ratio to the fourth power of each
vanishing phase jump. Its product with either squared divergent phase
heat capacity also has the same finite positive limit.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAGibbsBarrier_entropy_quartic_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsBarrier w φ τ l / egbFixedChargeAEntropyJump w φ τ ^ 4)
      atBot (𝓝 (egbFixedChargeAGibbsBarrierCoefficient w φ /
        (4 * Real.pi * egbFixedChargeACriticalRadius w φ ^ 2 * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ)) ^ 4)) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hp := Real.pi_pos
  have h := (egbFixedChargeAGibbsBarrier_quartic_critical_limit w φ l).div
    ((egbFixedChargeA_entropy_asymmetry_critical_limit w φ).pow 4) (by positivity)
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAGibbsBarrier_volume_quartic_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsBarrier w φ τ l / egbFixedChargeAVolumeJump w φ τ ^ 4)
      atBot (𝓝 (egbFixedChargeAGibbsBarrierCoefficient w φ /
        (8 * Real.pi * egbFixedChargeACriticalRadius w φ ^ 3) ^ 4)) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hp := Real.pi_pos
  have h := (egbFixedChargeAGibbsBarrier_quartic_critical_limit w φ l).div
    ((egbFixedChargeA_volume_asymmetry_critical_limit w φ).pow 4) (by positivity)
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAGibbsBarrier_latent_heat_quartic_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsBarrier w φ τ l /
      (egbFixedChargeATemperature w φ τ * egbFixedChargeAEntropyJump w φ τ) ^ 4)
      atBot (𝓝 (egbFixedChargeAGibbsBarrierCoefficient w φ / (4 * egbFixedChargeACriticalRadius w φ / 3) ^ 4)) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have h := (egbFixedChargeAGibbsBarrier_quartic_critical_limit w φ l).div
    ((egbFixedChargeA_latent_heat_asymmetry_critical_limit w φ).pow 4) (by positivity)
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

def egbFixedChargeABarrierHeatCoupling (w φ : ℝ) : ℝ :=
  Real.pi ^ 2 * egbFixedChargeACriticalRadius w φ ^ 5 * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) ^ 3 /
    (3 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ))

theorem egbFixedChargeABarrierHeatCoupling_pos (w φ : ℝ) : 0 < egbFixedChargeABarrierHeatCoupling w φ := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have hp := Real.pi_pos
  unfold egbFixedChargeABarrierHeatCoupling
  positivity

theorem egbFixedChargeAGibbsBarrier_heat_amplitude_product (w φ : ℝ) :
    egbFixedChargeAGibbsBarrierCoefficient w φ * egbFixedChargeACriticalHeatAmplitude w φ ^ 2 =
      egbFixedChargeABarrierHeatCoupling w φ := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have hp := Real.pi_pos
  unfold egbFixedChargeAGibbsBarrierCoefficient egbFixedChargeACriticalHeatAmplitude egbFixedChargeABarrierHeatCoupling
  field_simp <;> ring

theorem egbFixedChargeAGibbsBarrier_small_heat_squared_limit (w φ l₁ l₂ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsBarrier w φ τ l₁ *
      egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l₂
        (egbFixedChargeASmallRadius w φ τ) ^ 2)
      atBot (𝓝 (egbFixedChargeABarrierHeatCoupling w φ)) := by
  have h := (egbFixedChargeAGibbsBarrier_quartic_critical_limit w φ l₁).mul
    ((egbFixedChargeA_small_heat_capacity_amplitude w φ l₂).pow 2)
  rw [egbFixedChargeAGibbsBarrier_heat_amplitude_product] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

theorem egbFixedChargeAGibbsBarrier_large_heat_squared_limit (w φ l₁ l₂ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsBarrier w φ τ l₁ *
      egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l₂
        (egbFixedChargeALargeRadius w φ τ) ^ 2)
      atBot (𝓝 (egbFixedChargeABarrierHeatCoupling w φ)) := by
  have h := (egbFixedChargeAGibbsBarrier_quartic_critical_limit w φ l₁).mul
    ((egbFixedChargeA_large_heat_capacity_amplitude w φ l₂).pow 2)
  rw [egbFixedChargeAGibbsBarrier_heat_amplitude_product] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

end GaloisForLFunctions.HTGeometry
