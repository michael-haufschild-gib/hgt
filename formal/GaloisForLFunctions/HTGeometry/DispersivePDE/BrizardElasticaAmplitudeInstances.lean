import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAmplitudeCompiler
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaCorrectedJacobiNLS
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaRegionIIAmplitude
import Mathlib.Tactic

/-!
# Region I and II instances of the amplitude compiler

The corrected Region I wave and the paper's real `sd` Region II continuation are both instances of
one positive inverse-cubic oscillator.  The second instance supplies the previously absent exact
Region II traveling NLS solution.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def regionIAmplitudeOscillator
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) :
    PositiveAmplitudeOscillator where
  q := (P.val.q₀ : ℝ)
  q_pos := P.property.1
  gamma := physicalGamma P
  nu := physicalNu P
  amplitude := correctedJacobiAmplitude P J
  amplitude₁ := correctedJacobiAmplitudeVelocity P J
  amplitude₂ := correctedJacobiAmplitudeAcceleration P J
  amplitude_pos := correctedJacobiAmplitude_pos P J
  amplitude_deriv := correctedJacobiAmplitude_hasDerivAt P J
  amplitude₁_deriv := correctedJacobiAmplitudeVelocity_hasDerivAt P J
  oscillator := by
    intro x
    rw [physicalGamma_sq, physicalNu_sq]
    exact correctedJacobiAmplitude_secondOrderEquation P J x

theorem regionI_compiledCurvature_eq
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) :
    compiledCurvature k₀ (regionIAmplitudeOscillator P J) =
      physicalJacobiCurvature k₀ P J := by
  rfl

theorem regionI_compiledPhase_eq
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) :
    compiledPhase k₀ (regionIAmplitudeOscillator P J) =
      physicalJacobiPhase k₀ P J := by
  rfl

theorem regionI_compiledPolarProfile_eq
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) :
    compiledPolarProfile k₀ (regionIAmplitudeOscillator P J) =
      correctedJacobiPolarProfile k₀ P J := by
  rfl

theorem regionI_compiledWaveSpeed_eq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) :
    compiledWaveSpeed D k₀ (regionIAmplitudeOscillator P J) =
      physicalJacobiWaveSpeed D k₀ P := by
  rfl

/-- Existing corrected Region I solution is exactly the universal compiler output. -/
theorem regionI_compiledNLS_solves
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) :
    SolvesNLS (D : ℝ)
      (travelingPolarJet (correctedJacobiPolarProfile k₀ P J)
        (physicalJacobiWaveSpeed D k₀ P)) := by
  simpa only [regionI_compiledPolarProfile_eq, regionI_compiledWaveSpeed_eq] using
    compiledNLS_solves D k₀ (regionIAmplitudeOscillator P J)

noncomputable def regionIIGamma (P : PhysicalRegionII) : ℝ :=
  Real.sqrt (gammaSq P.val)

noncomputable def regionIINu (P : PhysicalRegionII) : ℝ :=
  Real.sqrt (nuSq P.val)

theorem regionIIGamma_pos (P : PhysicalRegionII) : 0 < regionIIGamma P := by
  rw [regionIIGamma]
  exact Real.sqrt_pos.2 (physicalRegionII_gammaSq_pos P)

theorem regionIINu_pos (P : PhysicalRegionII) : 0 < regionIINu P := by
  rw [regionIINu]
  exact Real.sqrt_pos.2 (physicalRegionII_nuSq_pos P)

theorem regionIIGamma_sq (P : PhysicalRegionII) :
    regionIIGamma P ^ 2 = gammaSq P.val := by
  rw [regionIIGamma, Real.sq_sqrt (physicalRegionII_gammaSq_pos P).le]

theorem regionIINu_sq (P : PhysicalRegionII) :
    regionIINu P ^ 2 = nuSq P.val := by
  rw [regionIINu, Real.sq_sqrt (physicalRegionII_nuSq_pos P).le]

noncomputable def regionIIAmplitudeOscillator
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    PositiveAmplitudeOscillator where
  q := regionIIRealScale P
  q_pos := regionIIRealScale_pos P
  gamma := regionIIGamma P
  nu := regionIINu P
  amplitude := regionIIJacobiAmplitude P J
  amplitude₁ := regionIIJacobiAmplitudeVelocity P J
  amplitude₂ := regionIIJacobiAmplitudeAcceleration P J
  amplitude_pos := regionIIJacobiAmplitude_pos P J
  amplitude_deriv := regionIIJacobiAmplitude_hasDerivAt P J
  amplitude₁_deriv := regionIIJacobiAmplitudeVelocity_hasDerivAt P J
  oscillator := by
    intro x
    rw [regionIIGamma_sq, regionIINu_sq]
    exact regionIIJacobiAmplitude_secondOrderEquation P J x

noncomputable def regionIIPhysicalCurvature
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) : ℝ → ℝ :=
  compiledCurvature k₀ (regionIIAmplitudeOscillator P J)

noncomputable def regionIIPhysicalCurvatureVelocity
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) : ℝ → ℝ :=
  compiledCurvatureVelocity k₀ (regionIIAmplitudeOscillator P J)

noncomputable def regionIIPhysicalCurvatureAcceleration
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) : ℝ → ℝ :=
  compiledCurvatureAcceleration k₀ (regionIIAmplitudeOscillator P J)

noncomputable def regionIIPhysicalPhase
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) : ℝ → ℝ :=
  compiledPhase k₀ (regionIIAmplitudeOscillator P J)

noncomputable def regionIIPhysicalPolarProfile
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) : TravelingPolarProfile :=
  compiledPolarProfile k₀ (regionIIAmplitudeOscillator P J)

noncomputable def regionIIPhysicalWaveSpeed
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII) : ℝ :=
  (D : ℝ) * (k₀ : ℝ) * regionIIGamma P

theorem regionIIPhysicalWaveSpeed_eq_compiled
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    regionIIPhysicalWaveSpeed D k₀ P =
      compiledWaveSpeed D k₀ (regionIIAmplitudeOscillator P J) := by
  rfl

theorem regionIIPhysicalCurvature_pos
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (s : ℝ) :
    0 < regionIIPhysicalCurvature k₀ P J s :=
  compiledCurvature_pos k₀ (regionIIAmplitudeOscillator P J) s

/-- Paper equation (67): global real `sd` curvature in Region II. -/
theorem regionIIPhysicalCurvature_sq
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (s : ℝ) :
    regionIIPhysicalCurvature k₀ P J s ^ 2 =
      (k₀ : ℝ) ^ 2 *
        (1 + regionIITransformedModulus P / (-(P.val.q₀ : ℝ)) *
          jacobiSd J
            (compiledArgument k₀ (regionIIAmplitudeOscillator P J) s) ^ 2) := by
  rw [regionIIPhysicalCurvature, compiledCurvature, mul_pow,
    show (regionIIAmplitudeOscillator P J).amplitude =
        regionIIJacobiAmplitude P J by rfl,
    regionIIJacobiAmplitude_sq]

theorem regionIIPhysicalCurvature_equation
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (s : ℝ) :
    regionIIPhysicalCurvatureAcceleration k₀ P J s =
      -regionIIPhysicalCurvature k₀ P J s ^ 3 / 2 -
        (k₀ : ℝ) ^ 2 * regionIIGamma P ^ 2 *
          regionIIPhysicalCurvature k₀ P J s / 4 +
        (k₀ : ℝ) ^ 6 * regionIINu P ^ 2 /
          (4 * regionIIPhysicalCurvature k₀ P J s ^ 3) :=
  compiledCurvature_equation k₀ (regionIIAmplitudeOscillator P J) s

theorem regionIIPhysicalCurvature_zero
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    regionIIPhysicalCurvature k₀ P J 0 = (k₀ : ℝ) := by
  rw [regionIIPhysicalCurvature, compiledCurvature, compiledArgument,
    mul_zero,
    show (regionIIAmplitudeOscillator P J).amplitude =
        regionIIJacobiAmplitude P J by rfl,
    regionIIJacobiAmplitude_zero]
  ring

theorem regionIIPhysicalCurvatureVelocity_zero
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    regionIIPhysicalCurvatureVelocity k₀ P J 0 = 0 := by
  rw [regionIIPhysicalCurvatureVelocity, compiledCurvatureVelocity,
    compiledArgument, mul_zero,
    show (regionIIAmplitudeOscillator P J).amplitude₁ =
        regionIIJacobiAmplitudeVelocity P J by rfl,
    regionIIJacobiAmplitudeVelocity_zero]
  ring

theorem regionIIPhysicalCurvatureAcceleration_zero_pos
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    0 < regionIIPhysicalCurvatureAcceleration k₀ P J 0 := by
  rw [regionIIPhysicalCurvatureAcceleration, compiledCurvatureAcceleration,
    compiledArgument, mul_zero]
  exact mul_pos (mul_pos k₀.property
    (sq_pos_of_pos (compiledArclengthScale_pos k₀ (regionIIAmplitudeOscillator P J))))
    (regionIIJacobiAmplitudeAcceleration_zero_pos P J)

theorem regionIIPhysicalWaveSpeed_ne_zero
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII) :
    regionIIPhysicalWaveSpeed D k₀ P ≠ 0 := by
  rw [regionIIPhysicalWaveSpeed]
  exact mul_ne_zero (mul_ne_zero D.ne_zero (ne_of_gt k₀.property))
    (ne_of_gt (regionIIGamma_pos P))

/-- Exact traveling NLS solution on the paper's extended Region II branch. -/
theorem regionIIJacobiNLS_solves
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    SolvesNLS (D : ℝ)
      (travelingPolarJet (regionIIPhysicalPolarProfile k₀ P J)
        (regionIIPhysicalWaveSpeed D k₀ P)) := by
  rw [regionIIPhysicalPolarProfile,
    regionIIPhysicalWaveSpeed_eq_compiled D k₀ P J]
  exact compiledNLS_solves D k₀ (regionIIAmplitudeOscillator P J)

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
