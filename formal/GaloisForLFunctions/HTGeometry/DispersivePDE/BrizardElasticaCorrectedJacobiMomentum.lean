import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaCorrectedJacobiHydrodynamics
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaTravelingMomentum
import Mathlib.Tactic

/-!
# Momentum balance of the corrected Jacobi wave

This specializes the paper's acceleration and momentum laws to the exact corrected Jacobi NLS
solution.  Every coefficient is reduced to the physical parameters `k₀`, `γ`, and `ν`.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

theorem correctedJacobiAccelerationForce_eq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    travelingHydroAccelerationForce (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t s =
      -2 * (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 6 * physicalNu P ^ 2 *
          physicalJacobiCurvatureVelocity k₀ P J
            (s - physicalJacobiWaveSpeed D k₀ P * t) /
        physicalJacobiCurvature k₀ P J
          (s - physicalJacobiWaveSpeed D k₀ P * t) ^ 5 := by
  rw [travelingHydroAccelerationForce, physicalJacobiTorsionScale]
  change -8 * (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 *
      ((k₀ : ℝ) * physicalNu P / 2) ^ 2 *
        physicalJacobiCurvatureVelocity k₀ P J
          (s - physicalJacobiWaveSpeed D k₀ P * t) /
      physicalJacobiCurvature k₀ P J
        (s - physicalJacobiWaveSpeed D k₀ P * t) ^ 5 = _
  ring

/-- Paper equation (54) for the exact corrected Jacobi traveling solution. -/
theorem correctedJacobiAccelerationEquation
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    travelingHydroVelocityT (D : ℝ) (k₀ : ℝ)
          (physicalJacobiTorsionScale k₀ P)
          (physicalJacobiWaveSpeed D k₀ P)
          (correctedJacobiCurvatureProfileJet k₀ P J) t s +
        travelingHydroVelocity (D : ℝ) (k₀ : ℝ)
          (physicalJacobiTorsionScale k₀ P)
          (physicalJacobiWaveSpeed D k₀ P)
          (correctedJacobiCurvatureProfileJet k₀ P J) t s *
        travelingHydroVelocityX (D : ℝ) (k₀ : ℝ)
          (physicalJacobiTorsionScale k₀ P)
          (physicalJacobiWaveSpeed D k₀ P)
          (correctedJacobiCurvatureProfileJet k₀ P J) t s =
      travelingHydroAccelerationForce (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t s ∧
    HasDerivAt
      (fun r : ℝ => travelingHydroVelocity (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) r s)
      (travelingHydroVelocityT (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t s) t ∧
    HasDerivAt
      (travelingHydroVelocity (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t)
      (travelingHydroVelocityX (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t s) s := by
  exact travelingHydroAccelerationEquation (D : ℝ) (k₀ : ℝ)
    (physicalJacobiTorsionScale k₀ P)
    (physicalJacobiWaveSpeed D k₀ P)
    (correctedJacobiCurvatureProfileJet k₀ P J) t s

theorem correctedJacobiQuantumStress_eq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    travelingQuantumStress (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t s =
      (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 6 * physicalNu P ^ 2 /
        physicalJacobiCurvature k₀ P J
          (s - physicalJacobiWaveSpeed D k₀ P * t) ^ 2 := by
  rw [travelingQuantumStress, physicalJacobiTorsionScale]
  change 4 * (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 *
      ((k₀ : ℝ) * physicalNu P / 2) ^ 2 /
        physicalJacobiCurvature k₀ P J
          (s - physicalJacobiWaveSpeed D k₀ P * t) ^ 2 = _
  ring

theorem correctedJacobiQuantumStressX_eq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    travelingQuantumStressX (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t s =
      -2 * (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 6 * physicalNu P ^ 2 *
          physicalJacobiCurvatureVelocity k₀ P J
            (s - physicalJacobiWaveSpeed D k₀ P * t) /
        physicalJacobiCurvature k₀ P J
          (s - physicalJacobiWaveSpeed D k₀ P * t) ^ 3 := by
  rw [travelingQuantumStressX, physicalJacobiTorsionScale]
  change -8 * (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 *
      ((k₀ : ℝ) * physicalNu P / 2) ^ 2 *
        physicalJacobiCurvatureVelocity k₀ P J
          (s - physicalJacobiWaveSpeed D k₀ P * t) /
      physicalJacobiCurvature k₀ P J
        (s - physicalJacobiWaveSpeed D k₀ P * t) ^ 3 = _
  ring

/-- Paper equation (56) for the exact corrected Jacobi traveling solution. -/
theorem correctedJacobiMomentumEquation
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    travelingMomentumDensityT (correctedJacobiCurvatureProfileJet k₀ P J)
          (physicalJacobiWaveSpeed D k₀ P) t s +
        travelingMomentumFluxX (D : ℝ) (k₀ : ℝ)
          (physicalJacobiTorsionScale k₀ P)
          (physicalJacobiWaveSpeed D k₀ P)
          (correctedJacobiCurvatureProfileJet k₀ P J) t s =
      travelingQuantumStressX (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t s ∧
    HasDerivAt
      (fun r : ℝ => travelingMomentumDensity (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) r s)
      (travelingMomentumDensityT (correctedJacobiCurvatureProfileJet k₀ P J)
        (physicalJacobiWaveSpeed D k₀ P) t s) t ∧
    HasDerivAt
      (travelingMomentumFlux (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t)
      (travelingMomentumFluxX (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t s) s ∧
    HasDerivAt
      (travelingQuantumStress (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t)
      (travelingQuantumStressX (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t s) s := by
  exact travelingMomentumEquation (D : ℝ) (k₀ : ℝ)
    (physicalJacobiTorsionScale k₀ P)
    (physicalJacobiWaveSpeed D k₀ P)
    (correctedJacobiCurvatureProfileJet k₀ P J) t s

theorem correctedJacobiQuantumStress_center
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t : ℝ) :
    travelingQuantumStress (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t
        (physicalJacobiWaveSpeed D k₀ P * t) =
      (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * physicalNu P ^ 2 := by
  rw [correctedJacobiQuantumStress_eq]
  have hz : physicalJacobiWaveSpeed D k₀ P * t -
      physicalJacobiWaveSpeed D k₀ P * t = 0 := by ring
  rw [hz, physicalJacobiCurvature_zero]
  field_simp [ne_of_gt k₀.property]

theorem correctedJacobiAccelerationForce_center
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t : ℝ) :
    travelingHydroAccelerationForce (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t
        (physicalJacobiWaveSpeed D k₀ P * t) = 0 := by
  rw [correctedJacobiAccelerationForce_eq]
  have hz : physicalJacobiWaveSpeed D k₀ P * t -
      physicalJacobiWaveSpeed D k₀ P * t = 0 := by ring
  rw [hz, physicalJacobiCurvatureVelocity_zero]
  ring

theorem correctedJacobiMomentumDensity_center
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t : ℝ) :
    travelingMomentumDensity (D : ℝ) (k₀ : ℝ)
        (physicalJacobiTorsionScale k₀ P)
        (physicalJacobiWaveSpeed D k₀ P)
        (correctedJacobiCurvatureProfileJet k₀ P J) t
        (physicalJacobiWaveSpeed D k₀ P * t) =
      (D : ℝ) * (k₀ : ℝ) ^ 3 * (physicalGamma P + physicalNu P) := by
  rw [travelingMomentumDensity, travelingMassCurrent,
    correctedJacobiTravelingDensity_center,
    correctedJacobiHydroVelocity_center]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
