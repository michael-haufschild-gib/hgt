import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolApertureDefectFirstFlux
import GaloisForLFunctions.RHTower.HedenmalmStokesFirstTraceMomentDualityWall

/-!
# Route P critical Gamma--sewn Green threshold for aperture defect flux
-/

open Complex Set MeasureTheory Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- One Green smoothing of the critical Gamma--sewn positive current. -/
def routePPrimitiveGammaSewnCriticalLinearGreenFlux
    (pe : Nat.Primes × ℕ) : ℝ :=
  gammaSewnMobiusApertureStokesFirstTracePositiveMoment 1 pe /
    deningerFreq (gammaSewnMobiusApertureStokesPrimePowerAxis pe)

/-- Half the double Green smoothing of the critical Gamma--sewn positive current. -/
def routePPrimitiveGammaSewnCriticalQuadraticGreenFlux
    (pe : Nat.Primes × ℕ) : ℝ :=
  (1 / 2 : ℝ) *
    gammaSewnMobiusApertureStokesFirstTracePositiveMoment 1 pe /
      deningerFreq (gammaSewnMobiusApertureStokesPrimePowerAxis pe) ^ (2 : ℕ)

private theorem criticalPositiveMoment_eq
    (pe : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesFirstTracePositiveMoment 1 pe =
      Real.log (pe.1 : ℝ) *
        (((pe.1 : ℝ)⁻¹) ^ (pe.2 + 1)) := by
  have hnode : xiMobiusContinuousApertureDiskNode 1 pe.1 = ((pe.1 : ℝ)⁻¹) := by
    simpa [xiMobiusContinuousApertureDiskNode,
      xiTransversePrimeApertureDiskNode] using
        xiTransversePrimeApertureDiskNode_one_eq_inv pe.1
  have hn : ((pe.2 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hedge := gammaSewnMobiusApertureStokesInverseTilt_mul_edge
    (s := (1 : ℝ)) (by norm_num) pe.1 pe.2
  rw [gammaSewnMobiusContinuousApertureFeature_zero, sub_zero, hnode] at hedge
  rw [gammaSewnMobiusApertureStokesFirstTracePositiveMoment,
    gammaSewnMobiusApertureStokesDualFeatureCoefficient,
    gammaSewnMobiusApertureStokesGap]
  calc
    gammaSewnMobiusContinuousApertureFeature 1 pe.1 pe.2 /
          (pe.2 + 1 : ℝ) *
        ((pe.2 + 1 : ℝ) *
          gammaSewnMobiusApertureStokesInverseTilt 1 pe.1) =
          gammaSewnMobiusApertureStokesInverseTilt 1 pe.1 *
        gammaSewnMobiusContinuousApertureFeature 1 pe.1 pe.2 := by
          field_simp [hn]
    _ = Real.log (pe.1 : ℝ) * ((pe.1 : ℝ)⁻¹) ^ (pe.2 + 1) := hedge

/-- A single critical Green smoothing retains exactly the prime-harmonic slice. -/
theorem routePPrimitiveGammaSewnCriticalLinearGreenFlux_primeSlice
    (p : Nat.Primes) :
    routePPrimitiveGammaSewnCriticalLinearGreenFlux (p, 0) =
      1 / (p : ℝ) := by
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne'
  rw [routePPrimitiveGammaSewnCriticalLinearGreenFlux,
    criticalPositiveMoment_eq,
    deningerFreq_gammaSewnMobiusApertureStokesPrimePowerAxis]
  norm_num
  field_simp [hlog]

/-- One Green step is below the scalar trace threshold. -/
theorem not_summable_routePPrimitiveGammaSewnCriticalLinearGreenFlux :
    ¬ Summable routePPrimitiveGammaSewnCriticalLinearGreenFlux := by
  intro hsum
  have hslice : Summable (fun p : Nat.Primes =>
      routePPrimitiveGammaSewnCriticalLinearGreenFlux (p, 0)) :=
    hsum.comp_injective (by
      intro p q h
      exact congrArg Prod.fst h)
  apply Nat.Primes.not_summable_one_div
  simpa only [routePPrimitiveGammaSewnCriticalLinearGreenFlux_primeSlice] using hslice

/-- Two Green steps land exactly on the P-G189 aperture defect flux, with the colligation factor
`1/2`. -/
theorem routePPrimitiveGammaSewnCriticalQuadraticGreenFlux_eq_defectFlux
    (pe : Nat.Primes × ℕ) :
    routePPrimitiveGammaSewnCriticalQuadraticGreenFlux pe =
      routePPrimitiveBurnolApertureDefectFlux pe := by
  have hp : (0 : ℝ) < (pe.1 : ℝ) := by exact_mod_cast pe.1.2.pos
  have hlog : Real.log (pe.1 : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast pe.1.2.one_lt)).ne'
  have hk : (pe.2 : ℝ) + 1 ≠ 0 := by positivity
  rw [routePPrimitiveGammaSewnCriticalQuadraticGreenFlux,
    criticalPositiveMoment_eq,
    deningerFreq_gammaSewnMobiusApertureStokesPrimePowerAxis,
    routePPrimitiveBurnolApertureDefectFlux_eq]
  field_simp [hp.ne', hlog, hk]
  rw [pow_succ]
  field_simp [hp.ne']

theorem summable_routePPrimitiveGammaSewnCriticalQuadraticGreenFlux :
    Summable routePPrimitiveGammaSewnCriticalQuadraticGreenFlux := by
  exact summable_routePPrimitiveBurnolApertureDefectFlux.congr
    (fun pe => (routePPrimitiveGammaSewnCriticalQuadraticGreenFlux_eq_defectFlux pe).symm)

theorem routePPrimitiveGammaSewnCriticalQuadraticGreenFlux_pos
    (pe : Nat.Primes × ℕ) :
    0 < routePPrimitiveGammaSewnCriticalQuadraticGreenFlux pe := by
  rw [routePPrimitiveGammaSewnCriticalQuadraticGreenFlux_eq_defectFlux]
  exact routePPrimitiveBurnolApertureDefectFlux_pos pe

/-- The trace-class threshold is sharp: one Green inverse diverges, while half the square of the
Green inverse is precisely the finite P-G189 Wold defect current. -/
theorem routePPrimitiveGammaSewnCriticalGreen_traceThreshold :
    (¬ Summable routePPrimitiveGammaSewnCriticalLinearGreenFlux) ∧
      Summable routePPrimitiveGammaSewnCriticalQuadraticGreenFlux :=
  ⟨not_summable_routePPrimitiveGammaSewnCriticalLinearGreenFlux,
    summable_routePPrimitiveGammaSewnCriticalQuadraticGreenFlux⟩

/-- The trace-finite quadratic Green current evaluated on a rapid Kummer test. -/
def routePPrimitiveGammaSewnCriticalQuadraticGreenPairing
    (a : DeningerHeightKothe) : ℂ :=
  ∑' pe : Nat.Primes × ℕ,
    (routePPrimitiveGammaSewnCriticalQuadraticGreenFlux pe : ℂ) *
      (a : DeningerPrimeLattice → ℂ)
        (gammaSewnMobiusApertureStokesPrimePowerAxis pe)

theorem summable_routePPrimitiveGammaSewnCriticalQuadraticGreenPairing
    (a : DeningerHeightKothe) :
    Summable (fun pe : Nat.Primes × ℕ =>
      (routePPrimitiveGammaSewnCriticalQuadraticGreenFlux pe : ℂ) *
        (a : DeningerPrimeLattice → ℂ)
          (gammaSewnMobiusApertureStokesPrimePowerAxis pe)) := by
  refine Summable.of_norm_bounded
    (summable_routePPrimitiveGammaSewnCriticalQuadraticGreenFlux.mul_right
      (deningerHeightSeminorm 0 a)) (fun pe => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (routePPrimitiveGammaSewnCriticalQuadraticGreenFlux_pos pe)]
  exact mul_le_mul_of_nonneg_left
    (deningerHeightKothe_norm_le a
      (gammaSewnMobiusApertureStokesPrimePowerAxis pe))
    (routePPrimitiveGammaSewnCriticalQuadraticGreenFlux_pos pe).le

/-- Double Green smoothing upgrades the critical current to an order-zero functional: no height
seminorm loss remains. -/
theorem norm_routePPrimitiveGammaSewnCriticalQuadraticGreenPairing_le
    (a : DeningerHeightKothe) :
    ‖routePPrimitiveGammaSewnCriticalQuadraticGreenPairing a‖ ≤
      (∑' pe : Nat.Primes × ℕ,
        routePPrimitiveGammaSewnCriticalQuadraticGreenFlux pe) *
          deningerHeightSeminorm 0 a := by
  have hpair :=
    summable_routePPrimitiveGammaSewnCriticalQuadraticGreenPairing a
  have hmajor :=
    summable_routePPrimitiveGammaSewnCriticalQuadraticGreenFlux.mul_right
      (deningerHeightSeminorm 0 a)
  calc
    ‖routePPrimitiveGammaSewnCriticalQuadraticGreenPairing a‖ ≤
        ∑' pe : Nat.Primes × ℕ,
          ‖(routePPrimitiveGammaSewnCriticalQuadraticGreenFlux pe : ℂ) *
            (a : DeningerPrimeLattice → ℂ)
              (gammaSewnMobiusApertureStokesPrimePowerAxis pe)‖ := by
      exact norm_tsum_le_tsum_norm hpair.norm
    _ ≤ ∑' pe : Nat.Primes × ℕ,
        routePPrimitiveGammaSewnCriticalQuadraticGreenFlux pe *
          deningerHeightSeminorm 0 a := by
      refine Summable.tsum_le_tsum (fun pe => ?_) hpair.norm hmajor
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (routePPrimitiveGammaSewnCriticalQuadraticGreenFlux_pos pe)]
      exact mul_le_mul_of_nonneg_left
        (deningerHeightKothe_norm_le a
          (gammaSewnMobiusApertureStokesPrimePowerAxis pe))
        (routePPrimitiveGammaSewnCriticalQuadraticGreenFlux_pos pe).le
    _ = (∑' pe : Nat.Primes × ℕ,
        routePPrimitiveGammaSewnCriticalQuadraticGreenFlux pe) *
          deningerHeightSeminorm 0 a := by
      rw [tsum_mul_right]

/-- The P-G189 flux functional is literally the critical Gamma--sewn Euler current pulled back
through half the square of Deninger's Green inverse. -/
theorem routePPrimitiveGammaSewnCriticalQuadraticGreenPairing_eq_eulerDual_green_sq
    (a : DeningerHeightKothe) :
    routePPrimitiveGammaSewnCriticalQuadraticGreenPairing a =
      gammaSewnMobiusApertureStokesEulerDualPairing 1
        ((1 / 2 : ℂ) • deningerGreen (deningerGreen a)) := by
  rw [routePPrimitiveGammaSewnCriticalQuadraticGreenPairing,
    gammaSewnMobiusApertureStokesEulerDualPairing]
  refine tsum_congr fun pe => ?_
  rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    deningerGreen_coe, deningerGreen_coe]
  rw [← ofReal_gammaSewnMobiusApertureStokesFirstTracePositiveMoment_eq_flux
    (s := (1 : ℝ)) (by norm_num) pe]
  rw [routePPrimitiveGammaSewnCriticalQuadraticGreenFlux]
  push_cast
  ring

/-- The global aperture derivative is the scalar mass of the double-Green-smoothed critical
Gamma--sewn current. -/
theorem tendsto_routePPrimitiveBurnolApertureTotalDefectMass_div_zero_quadraticGreen :
    Tendsto
      (fun c : ℝ => routePPrimitiveBurnolApertureTotalDefectMass c / c)
      (nhdsWithin 0 (Ioi 0))
      (nhds (∑' pe : Nat.Primes × ℕ,
        routePPrimitiveGammaSewnCriticalQuadraticGreenFlux pe)) := by
  rw [tsum_congr routePPrimitiveGammaSewnCriticalQuadraticGreenFlux_eq_defectFlux]
  exact tendsto_routePPrimitiveBurnolApertureTotalDefectMass_div_zero

end

end RHTower
