import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAInteriorGibbsProfile
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeABarrierCriticalRates
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeABarrierObservableCouplings

/-!
# Observable critical laws throughout the interior Gibbs profile

Each previously established barrier law extends to every interior
coordinate with the common factor cos⁴ψ. These are limits of the actual
Gibbs gap, physical phase jumps and phase heat capacities.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAInteriorGibbsGap_temperature_quadratic_limit (w φ l ψ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAInteriorGibbsGap w φ τ l ψ / ((egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ) ^ 2))
      atBot (𝓝 (cos ψ ^ 4 * (egbFixedChargeAGibbsBarrierCoefficient w φ / egbFixedChargeATemperatureGapCoefficient w φ ^ 2))) := by
  have hbarrier := egbFixedChargeAGibbsBarrier_temperature_quadratic_limit w φ l
  rw [← egbFixedChargeAGibbsBarrier_temperature_amplitude] at hbarrier
  have h := (egbFixedChargeAInteriorGibbsGap_barrier_ratio_limit w φ l l ψ).mul hbarrier
  convert h using 1
  funext τ
  have hB := egbFixedChargeAGibbsBarrier_pos w φ τ l
  field_simp

theorem egbFixedChargeAInteriorGibbsGap_pressure_quadratic_limit (w φ l ψ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAInteriorGibbsGap w φ τ l ψ / ((egbFixedChargeACriticalPressure w φ - egbFixedChargeAPressure w φ τ) ^ 2))
      atBot (𝓝 (cos ψ ^ 4 * (egbFixedChargeAGibbsBarrierCoefficient w φ / egbFixedChargeAPressureGapCoefficient w φ ^ 2))) := by
  have hbarrier := egbFixedChargeAGibbsBarrier_pressure_quadratic_limit w φ l
  rw [← egbFixedChargeAGibbsBarrier_pressure_amplitude] at hbarrier
  have h := (egbFixedChargeAInteriorGibbsGap_barrier_ratio_limit w φ l l ψ).mul hbarrier
  convert h using 1
  funext τ
  have hB := egbFixedChargeAGibbsBarrier_pos w φ τ l
  field_simp

theorem egbFixedChargeAInteriorGibbsGap_radius_quartic_limit (w φ l ψ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAInteriorGibbsGap w φ τ l ψ / ((egbFixedChargeALargeRadius w φ τ - egbFixedChargeASmallRadius w φ τ) ^ 4))
      atBot (𝓝 (cos ψ ^ 4 * (egbFixedChargeACriticalQuarticCoefficient w φ / 16))) := by
  have hbarrier := egbFixedChargeAGibbsBarrier_radius_quartic_limit w φ l
  have h := (egbFixedChargeAInteriorGibbsGap_barrier_ratio_limit w φ l l ψ).mul hbarrier
  convert h using 1
  funext τ
  have hB := egbFixedChargeAGibbsBarrier_pos w φ τ l
  field_simp

theorem egbFixedChargeAInteriorGibbsGap_entropy_quartic_limit (w φ l ψ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAInteriorGibbsGap w φ τ l ψ / (egbFixedChargeAEntropyJump w φ τ ^ 4))
      atBot (𝓝 (cos ψ ^ 4 * (egbFixedChargeAGibbsBarrierCoefficient w φ / (4 * Real.pi * egbFixedChargeACriticalRadius w φ ^ 2 * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ)) ^ 4))) := by
  have hbarrier := egbFixedChargeAGibbsBarrier_entropy_quartic_limit w φ l
  have h := (egbFixedChargeAInteriorGibbsGap_barrier_ratio_limit w φ l l ψ).mul hbarrier
  convert h using 1
  funext τ
  have hB := egbFixedChargeAGibbsBarrier_pos w φ τ l
  field_simp

theorem egbFixedChargeAInteriorGibbsGap_volume_quartic_limit (w φ l ψ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAInteriorGibbsGap w φ τ l ψ / (egbFixedChargeAVolumeJump w φ τ ^ 4))
      atBot (𝓝 (cos ψ ^ 4 * (egbFixedChargeAGibbsBarrierCoefficient w φ / (8 * Real.pi * egbFixedChargeACriticalRadius w φ ^ 3) ^ 4))) := by
  have hbarrier := egbFixedChargeAGibbsBarrier_volume_quartic_limit w φ l
  have h := (egbFixedChargeAInteriorGibbsGap_barrier_ratio_limit w φ l l ψ).mul hbarrier
  convert h using 1
  funext τ
  have hB := egbFixedChargeAGibbsBarrier_pos w φ τ l
  field_simp

theorem egbFixedChargeAInteriorGibbsGap_latent_heat_quartic_limit (w φ l ψ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAInteriorGibbsGap w φ τ l ψ / ((egbFixedChargeATemperature w φ τ * egbFixedChargeAEntropyJump w φ τ) ^ 4))
      atBot (𝓝 (cos ψ ^ 4 * (egbFixedChargeAGibbsBarrierCoefficient w φ / (4 * egbFixedChargeACriticalRadius w φ / 3) ^ 4))) := by
  have hbarrier := egbFixedChargeAGibbsBarrier_latent_heat_quartic_limit w φ l
  have h := (egbFixedChargeAInteriorGibbsGap_barrier_ratio_limit w φ l l ψ).mul hbarrier
  convert h using 1
  funext τ
  have hB := egbFixedChargeAGibbsBarrier_pos w φ τ l
  field_simp

theorem egbFixedChargeAInteriorGibbsGap_small_heat_squared_limit (w φ l₁ l₂ ψ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAInteriorGibbsGap w φ τ l₁ ψ *
      egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l₂
        (egbFixedChargeASmallRadius w φ τ) ^ 2)
      atBot (𝓝 (cos ψ ^ 4 * egbFixedChargeABarrierHeatCoupling w φ)) := by
  have h := (egbFixedChargeAInteriorGibbsGap_barrier_ratio_limit w φ l₁ l₁ ψ).mul
    (egbFixedChargeAGibbsBarrier_small_heat_squared_limit w φ l₁ l₂)
  convert h using 1
  funext τ
  have hB := egbFixedChargeAGibbsBarrier_pos w φ τ l₁
  field_simp

theorem egbFixedChargeAInteriorGibbsGap_large_heat_squared_limit (w φ l₁ l₂ ψ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAInteriorGibbsGap w φ τ l₁ ψ *
      egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l₂
        (egbFixedChargeALargeRadius w φ τ) ^ 2)
      atBot (𝓝 (cos ψ ^ 4 * egbFixedChargeABarrierHeatCoupling w φ)) := by
  have h := (egbFixedChargeAInteriorGibbsGap_barrier_ratio_limit w φ l₁ l₁ ψ).mul
    (egbFixedChargeAGibbsBarrier_large_heat_squared_limit w φ l₁ l₂)
  convert h using 1
  funext τ
  have hB := egbFixedChargeAGibbsBarrier_pos w φ τ l₁
  field_simp

end GaloisForLFunctions.HTGeometry
