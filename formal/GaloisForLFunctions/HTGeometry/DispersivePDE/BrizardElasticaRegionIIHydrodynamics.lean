import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAmplitudeHydrodynamics
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAmplitudeInstances

/-!
# Complete hydrodynamics of the Region II `sd` wave

Named specializations expose the density, current, Bohm potential, and conservation laws of the
paper's extended real `sd` solution.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def regionIIPhysicalDensity
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) : ℝ :=
  travelingDensity
    (compiledCurvatureProfileJet k₀ (regionIIAmplitudeOscillator P J))
    (compiledWaveSpeed D k₀ (regionIIAmplitudeOscillator P J)) t s

noncomputable def regionIIPhysicalFluidVelocity
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) : ℝ :=
  travelingHydroVelocity (D : ℝ) (k₀ : ℝ)
    (compiledTorsionScale k₀ (regionIIAmplitudeOscillator P J))
    (compiledWaveSpeed D k₀ (regionIIAmplitudeOscillator P J))
    (compiledCurvatureProfileJet k₀ (regionIIAmplitudeOscillator P J)) t s

noncomputable def regionIIPhysicalMassCurrent
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) : ℝ :=
  travelingMassCurrent (D : ℝ) (k₀ : ℝ)
    (compiledTorsionScale k₀ (regionIIAmplitudeOscillator P J))
    (compiledWaveSpeed D k₀ (regionIIAmplitudeOscillator P J))
    (compiledCurvatureProfileJet k₀ (regionIIAmplitudeOscillator P J)) t s

theorem regionIIPhysicalDensity_eq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    regionIIPhysicalDensity D k₀ P J t s =
      (k₀ : ℝ) ^ 2 *
        (1 + regionIITransformedModulus P / (-(P.val.q₀ : ℝ)) *
          jacobiSd J
            (compiledArgument k₀ (regionIIAmplitudeOscillator P J)
              (s - regionIIPhysicalWaveSpeed D k₀ P * t)) ^ 2) := by
  rw [regionIIPhysicalDensity, compiledTravelingDensity_eq_amplitude_sq,
    show (regionIIAmplitudeOscillator P J).amplitude =
      regionIIJacobiAmplitude P J by rfl,
    regionIIJacobiAmplitude_sq,
    regionIIPhysicalWaveSpeed_eq_compiled D k₀ P J]

theorem regionIINLS_normSq_eq_density
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    ‖(travelingPolarJet (regionIIPhysicalPolarProfile k₀ P J)
        (regionIIPhysicalWaveSpeed D k₀ P)).u t s‖ ^ 2 =
      regionIIPhysicalDensity D k₀ P J t s := by
  rw [regionIIPhysicalPolarProfile, regionIIPhysicalDensity,
    regionIIPhysicalWaveSpeed_eq_compiled D k₀ P J]
  exact compiledNLS_normSq_eq_travelingDensity D k₀
    (regionIIAmplitudeOscillator P J) t s

theorem regionIIPhysicalVelocity_eq_phaseSlope
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    regionIIPhysicalFluidVelocity D k₀ P J t s =
      2 * (D : ℝ) * compiledPhaseSlope k₀ (regionIIAmplitudeOscillator P J)
        (s - regionIIPhysicalWaveSpeed D k₀ P * t) := by
  rw [regionIIPhysicalFluidVelocity,
    regionIIPhysicalWaveSpeed_eq_compiled D k₀ P J]
  exact compiledHydroVelocity_eq_phaseSlope D k₀
    (regionIIAmplitudeOscillator P J) t s

theorem regionIIPhysicalMassCurrent_eq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    regionIIPhysicalMassCurrent D k₀ P J t s =
      regionIIPhysicalWaveSpeed D k₀ P * regionIIPhysicalDensity D k₀ P J t s +
        (D : ℝ) * (k₀ : ℝ) ^ 3 * regionIINu P := by
  rw [regionIIPhysicalMassCurrent, regionIIPhysicalDensity,
    regionIIPhysicalWaveSpeed_eq_compiled D k₀ P J]
  simpa only [show (regionIIAmplitudeOscillator P J).nu = regionIINu P by rfl] using
    compiledTravelingMassCurrent_eq D k₀ (regionIIAmplitudeOscillator P J) t s

theorem regionIIPhysicalUnboostedCurrent_eq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    unboostedMassCurrent (D : ℝ) (k₀ : ℝ)
        (compiledTorsionScale k₀ (regionIIAmplitudeOscillator P J))
        (compiledWaveSpeed D k₀ (regionIIAmplitudeOscillator P J))
        (compiledCurvatureProfileJet k₀ (regionIIAmplitudeOscillator P J)) t s =
      (D : ℝ) * (k₀ : ℝ) ^ 3 * regionIINu P := by
  simpa only [show (regionIIAmplitudeOscillator P J).nu = regionIINu P by rfl] using
    compiledUnboostedMassCurrent_eq D k₀ (regionIIAmplitudeOscillator P J) t s

theorem regionIIPhysicalContinuityEquation
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    travelingDensityT
          (compiledCurvatureProfileJet k₀ (regionIIAmplitudeOscillator P J))
          (compiledWaveSpeed D k₀ (regionIIAmplitudeOscillator P J)) t s +
        compiledWaveSpeed D k₀ (regionIIAmplitudeOscillator P J) *
          travelingDensityX
            (compiledCurvatureProfileJet k₀ (regionIIAmplitudeOscillator P J))
            (compiledWaveSpeed D k₀ (regionIIAmplitudeOscillator P J)) t s = 0 :=
  compiledContinuityEquation D k₀ (regionIIAmplitudeOscillator P J) t s

theorem regionIIPhysicalAccelerationEquation
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    travelingHydroVelocityT (D : ℝ) (k₀ : ℝ)
          (compiledTorsionScale k₀ (regionIIAmplitudeOscillator P J))
          (compiledWaveSpeed D k₀ (regionIIAmplitudeOscillator P J))
          (compiledCurvatureProfileJet k₀ (regionIIAmplitudeOscillator P J)) t s +
        regionIIPhysicalFluidVelocity D k₀ P J t s *
          travelingHydroVelocityX (D : ℝ) (k₀ : ℝ)
            (compiledTorsionScale k₀ (regionIIAmplitudeOscillator P J))
            (compiledWaveSpeed D k₀ (regionIIAmplitudeOscillator P J))
            (compiledCurvatureProfileJet k₀ (regionIIAmplitudeOscillator P J)) t s =
      travelingHydroAccelerationForce (D : ℝ) (k₀ : ℝ)
        (compiledTorsionScale k₀ (regionIIAmplitudeOscillator P J))
        (compiledWaveSpeed D k₀ (regionIIAmplitudeOscillator P J))
        (compiledCurvatureProfileJet k₀ (regionIIAmplitudeOscillator P J)) t s := by
  rw [regionIIPhysicalFluidVelocity]
  exact compiledAccelerationEquation D k₀ (regionIIAmplitudeOscillator P J) t s

theorem regionIIPhysicalMomentumEquation
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    travelingMomentumDensityT
          (compiledCurvatureProfileJet k₀ (regionIIAmplitudeOscillator P J))
          (compiledWaveSpeed D k₀ (regionIIAmplitudeOscillator P J)) t s +
        travelingMomentumFluxX (D : ℝ) (k₀ : ℝ)
          (compiledTorsionScale k₀ (regionIIAmplitudeOscillator P J))
          (compiledWaveSpeed D k₀ (regionIIAmplitudeOscillator P J))
          (compiledCurvatureProfileJet k₀ (regionIIAmplitudeOscillator P J)) t s =
      travelingQuantumStressX (D : ℝ) (k₀ : ℝ)
        (compiledTorsionScale k₀ (regionIIAmplitudeOscillator P J))
        (compiledWaveSpeed D k₀ (regionIIAmplitudeOscillator P J))
        (compiledCurvatureProfileJet k₀ (regionIIAmplitudeOscillator P J)) t s :=
  compiledMomentumEquation D k₀ (regionIIAmplitudeOscillator P J) t s

theorem regionIIPhysicalHydroPhaseEquation
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    compiledHydroPhaseT D k₀ (regionIIAmplitudeOscillator P J) t s +
        regionIIPhysicalFluidVelocity D k₀ P J t s ^ 2 / (2 * (D : ℝ)) =
      (D : ℝ) *
        (regionIIPhysicalDensity D k₀ P J t s +
          2 * compiledBohmTerm k₀ (regionIIAmplitudeOscillator P J)
            (s - compiledWaveSpeed D k₀ (regionIIAmplitudeOscillator P J) * t)) := by
  rw [regionIIPhysicalFluidVelocity, regionIIPhysicalDensity]
  exact compiledHydroPhaseEquation D k₀ (regionIIAmplitudeOscillator P J) t s

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
