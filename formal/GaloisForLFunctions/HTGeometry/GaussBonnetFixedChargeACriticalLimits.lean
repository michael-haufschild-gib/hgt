import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAKernelLimits
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalParameters

/-!
# Critical endpoint of the actual fixed-charge model-A coexistence curve

Every weight, both physical phase radii, and the actual pressure and
temperature converge to the matched critical state with unchanged charge
and coupling. The limits follow from the exact kernel and quadratic root.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open CPV

theorem egbFixedChargeAQuadraticB_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAQuadraticB τ φ) atBot (𝓝 (egbFixedChargeACriticalB φ)) := by
  have h : Tendsto (fun τ => egbFixedChargeAQuadraticB τ φ) atBot
      (𝓝 (12 - egbFixedChargeAFraction φ * (-12))) :=
    egbFixedChargeABase_critical_limit.sub (tendsto_const_nhds.mul egbFixedChargeALinearCorrection_critical_limit)
  have he : 12 - egbFixedChargeAFraction φ * (-12) = egbFixedChargeACriticalB φ := by
    unfold egbFixedChargeACriticalB
    ring
  rwa [he] at h

theorem egbFixedChargeADiscriminant_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeADiscriminant τ φ) atBot (𝓝 (egbFixedChargeACriticalDiscriminant φ)) := by
  have h : Tendsto (fun τ => egbFixedChargeADiscriminant τ φ) atBot
      (𝓝 (egbFixedChargeACriticalB φ ^ (2 : ℕ) + 4 * 24 * egbFixedChargeAFraction φ * 2)) :=
    ((egbFixedChargeAQuadraticB_critical_limit φ).pow 2).add
      (((tendsto_const_nhds.mul egbCoexistenceAQuadraticA_critical_limit).mul tendsto_const_nhds).mul
        egbCoexistenceAQuadraticC_critical_limit)
  have he : egbFixedChargeACriticalB φ ^ (2 : ℕ) + 4 * 24 * egbFixedChargeAFraction φ * 2 =
      egbFixedChargeACriticalDiscriminant φ := by unfold egbFixedChargeACriticalDiscriminant; ring
  rwa [he] at h

theorem egbFixedChargeAWeight_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAWeight τ φ) atBot (𝓝 (egbFixedChargeACriticalWeight φ)) := by
  have hB := egbFixedChargeACriticalB_pos φ
  have h : Tendsto (fun τ => egbFixedChargeAWeight τ φ) atBot
      (𝓝 ((2 * 2) / (egbFixedChargeACriticalB φ + sqrt (egbFixedChargeACriticalDiscriminant φ)))) :=
    (tendsto_const_nhds.mul egbCoexistenceAQuadraticC_critical_limit).div
      ((egbFixedChargeAQuadraticB_critical_limit φ).add (egbFixedChargeADiscriminant_critical_limit φ).sqrt) (by positivity)
  simpa only [show (2 : ℝ) * 2 = 4 by ring, egbFixedChargeACriticalWeight] using h

theorem egbFixedChargeACouplingWeight_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeACouplingWeight τ φ) atBot (𝓝 (egbFixedChargeACriticalCouplingWeight φ)) :=
  tendsto_const_nhds.mul (egbFixedChargeAWeight_critical_limit φ)

theorem egbFixedChargeADenominator_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeADenominator τ φ) atBot (𝓝 (6 + 12 * egbFixedChargeACriticalCouplingWeight φ)) := by
  have h : Tendsto (fun τ => egbFixedChargeADenominator τ φ) atBot
      (𝓝 (6 + 4 * egbFixedChargeACriticalCouplingWeight φ * 3)) :=
    egbCoexistenceShape_tendsto_critical.add
      ((tendsto_const_nhds.mul (egbFixedChargeACouplingWeight_critical_limit φ)).mul egbCoexistenceALogKernel_tendsto_critical)
  have he : 6 + 4 * egbFixedChargeACriticalCouplingWeight φ * 3 = 6 + 12 * egbFixedChargeACriticalCouplingWeight φ := by ring
  rwa [he] at h

theorem egbFixedChargeATemperatureWeight_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeATemperatureWeight τ φ) atBot
      (𝓝 (8 / (6 + 12 * egbFixedChargeACriticalCouplingWeight φ))) := by
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have h : Tendsto (fun τ => egbFixedChargeATemperatureWeight τ φ) atBot
      (𝓝 ((4 * (1 + 1)) / (6 + 12 * egbFixedChargeACriticalCouplingWeight φ))) :=
    (tendsto_const_nhds.mul (thermalRatio_tendsto_atBot_one.add tendsto_const_nhds)).div
      (egbFixedChargeADenominator_critical_limit φ) (by positivity)
  simpa only [show (4 : ℝ) * (1 + 1) = 8 by ring] using h

theorem egbFixedChargeAPressureWeight_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAPressureWeight τ φ) atBot
      (𝓝 ((3 - 2 * egbFixedChargeACriticalCouplingWeight φ) / (6 + 12 * egbFixedChargeACriticalCouplingWeight φ))) := by
  have hz := thermalRatio_tendsto_atBot_one
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have h : Tendsto (fun τ => egbFixedChargeAPressureWeight τ φ) atBot
      (𝓝 ((3 * ((1 : ℝ) ^ (2 : ℕ) + 1) + 4 * egbFixedChargeACriticalCouplingWeight φ * (2 - 3)) /
        ((6 + 12 * egbFixedChargeACriticalCouplingWeight φ) * (1 ^ (2 : ℕ) + 1)))) :=
    ((tendsto_const_nhds.mul ((hz.pow 2).add tendsto_const_nhds)).add
      ((tendsto_const_nhds.mul (egbFixedChargeACouplingWeight_critical_limit φ)).mul
        (tendsto_const_nhds.sub egbCoexistenceALogKernel_tendsto_critical))).div
          ((egbFixedChargeADenominator_critical_limit φ).mul ((hz.pow 2).add tendsto_const_nhds)) (by positivity)
  have he : (3 * ((1 : ℝ) ^ (2 : ℕ) + 1) + 4 * egbFixedChargeACriticalCouplingWeight φ * (2 - 3)) /
      ((6 + 12 * egbFixedChargeACriticalCouplingWeight φ) * (1 ^ (2 : ℕ) + 1)) =
    (3 - 2 * egbFixedChargeACriticalCouplingWeight φ) / (6 + 12 * egbFixedChargeACriticalCouplingWeight φ) := by
    field_simp <;> ring
  rwa [he] at h

theorem egbFixedChargeALargeRadius_critical_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeALargeRadius w φ) atBot (𝓝 (egbFixedChargeACriticalRadius w φ)) :=
  tendsto_const_nhds.div (egbFixedChargeAWeight_critical_limit φ).sqrt
    (sqrt_pos.mpr (egbFixedChargeACriticalWeight_pos φ)).ne'

theorem egbFixedChargeASmallRadius_critical_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeASmallRadius w φ) atBot (𝓝 (egbFixedChargeACriticalRadius w φ)) := by
  change Tendsto (fun τ => thermalRatio τ * egbFixedChargeALargeRadius w φ τ) atBot (𝓝 (egbFixedChargeACriticalRadius w φ))
  have h := thermalRatio_tendsto_atBot_one.mul (egbFixedChargeALargeRadius_critical_limit w φ)
  simpa only [one_mul] using h

theorem egbFixedChargeALogScale_critical_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeALogScale w φ) atBot (𝓝 (egbFixedChargeACriticalLogScale w φ)) :=
  (egbFixedChargeALargeRadius_critical_limit w φ).log (egbFixedChargeACriticalRadius_pos w φ).ne'

theorem egbFixedChargeATemperature_critical_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeATemperature w φ) atBot (𝓝 (egbFixedChargeACriticalTemperature w φ)) := by
  have hR := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have h : Tendsto (egbFixedChargeATemperature w φ) atBot
      (𝓝 ((8 / (6 + 12 * egbFixedChargeACriticalCouplingWeight φ)) / (4 * Real.pi * egbFixedChargeACriticalRadius w φ))) :=
    (egbFixedChargeATemperatureWeight_critical_limit φ).div
      (tendsto_const_nhds.mul (egbFixedChargeALargeRadius_critical_limit w φ)) (by positivity)
  have he : (8 / (6 + 12 * egbFixedChargeACriticalCouplingWeight φ)) / (4 * Real.pi * egbFixedChargeACriticalRadius w φ) =
      egbFixedChargeACriticalTemperature w φ := by
    unfold egbFixedChargeACriticalTemperature
    field_simp <;> ring
  rwa [he] at h

theorem egbFixedChargeAPressure_critical_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeAPressure w φ) atBot (𝓝 (egbFixedChargeACriticalPressure w φ)) := by
  have hR := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have h : Tendsto (egbFixedChargeAPressure w φ) atBot
      (𝓝 (((3 - 2 * egbFixedChargeACriticalCouplingWeight φ) / (6 + 12 * egbFixedChargeACriticalCouplingWeight φ)) /
        (8 * Real.pi * egbFixedChargeACriticalRadius w φ ^ (2 : ℕ)))) :=
    (egbFixedChargeAPressureWeight_critical_limit φ).div
      (tendsto_const_nhds.mul ((egbFixedChargeALargeRadius_critical_limit w φ).pow 2)) (by positivity)
  have he : ((3 - 2 * egbFixedChargeACriticalCouplingWeight φ) / (6 + 12 * egbFixedChargeACriticalCouplingWeight φ)) /
      (8 * Real.pi * egbFixedChargeACriticalRadius w φ ^ (2 : ℕ)) = egbFixedChargeACriticalPressure w φ := by
    unfold egbFixedChargeACriticalPressure
    field_simp <;> ring
  rwa [he] at h

end GaloisForLFunctions.HTGeometry
