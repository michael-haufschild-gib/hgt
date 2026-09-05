import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaCorrectedJacobiNLS
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaTravelingHydrodynamics
import Mathlib.Tactic

/-!
# Hydrodynamics of the corrected Jacobi traveling wave

The corrected Jacobi curvature is everywhere positive, so it defines the unit-valued curvature
profile required by the paper's Hasimoto hydrodynamics.  This module identifies its density with
the NLS modulus, its full fluid velocity with twice the phase slope, and its constant torsion flux.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- The corrected physical Jacobi curvature as a derivative-certified nonvanishing profile. -/
noncomputable def correctedJacobiCurvatureProfileJet
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) : CurvatureProfileJet where
  κ := fun s => Units.mk0 (physicalJacobiCurvature k₀ P J s)
    (ne_of_gt (physicalJacobiCurvature_pos k₀ P J s))
  κ₁ := physicalJacobiCurvatureVelocity k₀ P J
  hasDerivAt := by
    intro s
    convert physicalJacobiCurvature_hasDerivAt k₀ P J s using 1
    funext y
    rfl

/-- Constant torsion scale selected by the corrected inverse-square phase. -/
noncomputable def physicalJacobiTorsionScale
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI) : ℝ :=
  (k₀ : ℝ) * physicalNu P / 2

theorem correctedJacobiTravelingDensity_eq_curvature_sq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    travelingDensity (correctedJacobiCurvatureProfileJet k₀ P J)
        (physicalJacobiWaveSpeed D k₀ P) t s =
      physicalJacobiCurvature k₀ P J
          (s - physicalJacobiWaveSpeed D k₀ P * t) ^ 2 := by
  rfl

theorem correctedJacobiTravelingDensity_eq_amplitude_sq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    travelingDensity (correctedJacobiCurvatureProfileJet k₀ P J)
        (physicalJacobiWaveSpeed D k₀ P) t s =
      (k₀ : ℝ) ^ 2 *
        correctedJacobiAmplitude P J
          (physicalJacobiArgument k₀ P
            (s - physicalJacobiWaveSpeed D k₀ P * t)) ^ 2 := by
  rw [correctedJacobiTravelingDensity_eq_curvature_sq,
    physicalJacobiCurvature]
  ring

/-- NLS intensity and Hasimoto mass density are literally the same traveling field. -/
theorem correctedJacobiNLS_normSq_eq_travelingDensity
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    ‖(travelingPolarJet (correctedJacobiPolarProfile k₀ P J)
        (physicalJacobiWaveSpeed D k₀ P)).u t s‖ ^ 2 =
      travelingDensity (correctedJacobiCurvatureProfileJet k₀ P J)
        (physicalJacobiWaveSpeed D k₀ P) t s := by
  change ‖polarProfile (correctedJacobiPolarProfile k₀ P J)
      (s - physicalJacobiWaveSpeed D k₀ P * t)‖ ^ 2 = _
  rw [correctedJacobiPolarProfile_normSq,
    correctedJacobiTravelingDensity_eq_curvature_sq]

/-- The Hasimoto fluid velocity is exactly twice dispersion times the corrected phase slope. -/
theorem correctedJacobiHydroVelocity_eq_phaseSlope
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    travelingHydroVelocity (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t s =
      2 * (D : ℝ) * physicalJacobiPhaseSlope k₀ P J
        (s - physicalJacobiWaveSpeed D k₀ P * t) := by
  rw [travelingHydroVelocity, fluidSpeed, torsion,
    physicalJacobiTorsionScale, physicalJacobiWaveSpeed,
    physicalJacobiPhaseSlope]
  change (D : ℝ) * (k₀ : ℝ) * physicalGamma P +
      2 * (D : ℝ) *
        ((k₀ : ℝ) ^ 2 * ((k₀ : ℝ) * physicalNu P / 2) /
          physicalJacobiCurvature k₀ P J
            (s - (D : ℝ) * (k₀ : ℝ) * physicalGamma P * t) ^ 2) = _
  rw [physicalJacobiCurvature]
  field_simp [ne_of_gt k₀.property,
    ne_of_gt (correctedJacobiAmplitude_pos P J
      (physicalJacobiArgument k₀ P
        (s - (D : ℝ) * (k₀ : ℝ) * physicalGamma P * t)))]

theorem correctedJacobiTravelingMassCurrent_eq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    travelingMassCurrent (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t s =
      physicalJacobiWaveSpeed D k₀ P *
          travelingDensity (correctedJacobiCurvatureProfileJet k₀ P J)
            (physicalJacobiWaveSpeed D k₀ P) t s +
        (D : ℝ) * (k₀ : ℝ) ^ 3 * physicalNu P := by
  rw [travelingMassCurrent_eq, physicalJacobiTorsionScale]
  ring

/-- The full mass current is also density times twice dispersion times phase gradient. -/
theorem correctedJacobiTravelingMassCurrent_eq_phaseCurrent
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    travelingMassCurrent (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t s =
      travelingDensity (correctedJacobiCurvatureProfileJet k₀ P J)
          (physicalJacobiWaveSpeed D k₀ P) t s *
        (2 * (D : ℝ) * physicalJacobiPhaseSlope k₀ P J
          (s - physicalJacobiWaveSpeed D k₀ P * t)) := by
  rw [travelingMassCurrent, correctedJacobiHydroVelocity_eq_phaseSlope]

/-- Omitting the traveling drift leaves the paper's constant torsion mass flux. -/
theorem correctedJacobiUnboostedMassCurrent_eq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    unboostedMassCurrent (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t s =
      (D : ℝ) * (k₀ : ℝ) ^ 3 * physicalNu P := by
  rw [unboostedMassCurrent_eq, physicalJacobiTorsionScale]
  ring

/-- The corrected Jacobi wave satisfies the full traveling continuity equation. -/
theorem correctedJacobiContinuityEquation
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    travelingDensityT (correctedJacobiCurvatureProfileJet k₀ P J)
          (physicalJacobiWaveSpeed D k₀ P) t s +
        physicalJacobiWaveSpeed D k₀ P *
          travelingDensityX (correctedJacobiCurvatureProfileJet k₀ P J)
            (physicalJacobiWaveSpeed D k₀ P) t s = 0 ∧
      HasDerivAt
        (fun r : ℝ => travelingDensity
          (correctedJacobiCurvatureProfileJet k₀ P J)
          (physicalJacobiWaveSpeed D k₀ P) r s)
        (travelingDensityT (correctedJacobiCurvatureProfileJet k₀ P J)
          (physicalJacobiWaveSpeed D k₀ P) t s) t ∧
      HasDerivAt
        (travelingMassCurrent (D : ℝ) (k₀ : ℝ)
          (physicalJacobiTorsionScale k₀ P)
          (physicalJacobiWaveSpeed D k₀ P)
          (correctedJacobiCurvatureProfileJet k₀ P J) t)
        (physicalJacobiWaveSpeed D k₀ P *
          travelingDensityX (correctedJacobiCurvatureProfileJet k₀ P J)
            (physicalJacobiWaveSpeed D k₀ P) t s) s := by
  exact travelingContinuityEquation (D : ℝ) (k₀ : ℝ)
    (physicalJacobiTorsionScale k₀ P)
    (physicalJacobiWaveSpeed D k₀ P)
    (correctedJacobiCurvatureProfileJet k₀ P J) t s

/-- Momentum flux of the unboosted Hasimoto fluid, specialized to the Jacobi curvature. -/
theorem correctedJacobiMomentumFlux_eq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    travelingDensity (correctedJacobiCurvatureProfileJet k₀ P J)
          (physicalJacobiWaveSpeed D k₀ P) t s *
        fluidSpeed (D : ℝ) (k₀ : ℝ) (physicalJacobiTorsionScale k₀ P)
          ((correctedJacobiCurvatureProfileJet k₀ P J).κ
            (s - physicalJacobiWaveSpeed D k₀ P * t)) ^ 2 =
      (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 6 * physicalNu P ^ 2 /
        physicalJacobiCurvature k₀ P J
          (s - physicalJacobiWaveSpeed D k₀ P * t) ^ 2 := by
  change density
      ((correctedJacobiCurvatureProfileJet k₀ P J).κ
        (s - physicalJacobiWaveSpeed D k₀ P * t)) *
      fluidSpeed (D : ℝ) (k₀ : ℝ) (physicalJacobiTorsionScale k₀ P)
        ((correctedJacobiCurvatureProfileJet k₀ P J).κ
          (s - physicalJacobiWaveSpeed D k₀ P * t)) ^ 2 = _
  rw [density_mul_fluidSpeed_sq, physicalJacobiTorsionScale]
  change 4 * (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 *
      ((k₀ : ℝ) * physicalNu P / 2) ^ 2 /
        physicalJacobiCurvature k₀ P J
          (s - physicalJacobiWaveSpeed D k₀ P * t) ^ 2 = _
  ring

theorem correctedJacobiTravelingDensity_center
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t : ℝ) :
    travelingDensity (correctedJacobiCurvatureProfileJet k₀ P J)
        (physicalJacobiWaveSpeed D k₀ P) t
        (physicalJacobiWaveSpeed D k₀ P * t) = (k₀ : ℝ) ^ 2 := by
  rw [correctedJacobiTravelingDensity_eq_curvature_sq]
  have hz : physicalJacobiWaveSpeed D k₀ P * t -
      physicalJacobiWaveSpeed D k₀ P * t = 0 := by ring
  rw [hz, physicalJacobiCurvature_zero]

theorem correctedJacobiHydroVelocity_center
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t : ℝ) :
    travelingHydroVelocity (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t
        (physicalJacobiWaveSpeed D k₀ P * t) =
      (D : ℝ) * (k₀ : ℝ) * (physicalGamma P + physicalNu P) := by
  rw [correctedJacobiHydroVelocity_eq_phaseSlope]
  have hz : physicalJacobiWaveSpeed D k₀ P * t -
      physicalJacobiWaveSpeed D k₀ P * t = 0 := by ring
  rw [hz, physicalJacobiPhaseSlope, physicalJacobiArgument]
  simp only [mul_zero, correctedJacobiAmplitude_zero, one_pow, div_one]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
