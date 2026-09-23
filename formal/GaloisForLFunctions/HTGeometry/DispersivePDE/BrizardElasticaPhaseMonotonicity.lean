import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAmplitudeInstances
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaRegionIIFlowBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# Global monotonicity of the Jacobi phases

Positive curvature scale, positive reconstructed torsion, and the inverse-square phase law force
strictly positive phase slope in both physical regions.  Each phase is therefore a global
orientation-preserving coordinate, with its unique zero at the centered point.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

theorem physicalJacobiPhaseSlope_pos
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (s : ℝ) :
    0 < physicalJacobiPhaseSlope k₀ P J s := by
  rw [physicalJacobiPhaseSlope]
  have hfirst : 0 < (k₀ : ℝ) * physicalGamma P / 2 :=
    div_pos (mul_pos k₀.property (physicalGamma_pos P)) (by norm_num)
  have hsecond : 0 < ((k₀ : ℝ) * physicalNu P / 2) /
      correctedJacobiAmplitude P J (physicalJacobiArgument k₀ P s) ^ (2 : ℕ) :=
    div_pos
      (div_pos (mul_pos k₀.property (physicalNu_pos P)) (by norm_num))
      (sq_pos_of_pos (correctedJacobiAmplitude_pos P J _))
  exact add_pos hfirst hsecond

theorem physicalJacobiPhase_strictMono
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) :
    StrictMono (physicalJacobiPhase k₀ P J) :=
  strictMono_of_hasDerivAt_pos
    (physicalJacobiPhase_hasDerivAt k₀ P J)
    (physicalJacobiPhaseSlope_pos k₀ P J)

theorem physicalJacobiPhase_injective
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) :
    Function.Injective (physicalJacobiPhase k₀ P J) :=
  (physicalJacobiPhase_strictMono k₀ P J).injective

theorem physicalJacobiPhase_pos_iff
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (s : ℝ) :
    0 < physicalJacobiPhase k₀ P J s ↔ 0 < s := by
  have h : physicalJacobiPhase k₀ P J 0 < physicalJacobiPhase k₀ P J s ↔ 0 < s :=
    (physicalJacobiPhase_strictMono k₀ P J).lt_iff_lt
  simpa only [physicalJacobiPhase_zero] using h

theorem physicalJacobiPhase_neg_iff
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (s : ℝ) :
    physicalJacobiPhase k₀ P J s < 0 ↔ s < 0 := by
  have h : physicalJacobiPhase k₀ P J s < physicalJacobiPhase k₀ P J 0 ↔ s < 0 :=
    (physicalJacobiPhase_strictMono k₀ P J).lt_iff_lt
  simpa only [physicalJacobiPhase_zero] using h

theorem physicalJacobiPhase_eq_zero_iff
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (s : ℝ) :
    physicalJacobiPhase k₀ P J s = 0 ↔ s = 0 := by
  have h : physicalJacobiPhase k₀ P J s = physicalJacobiPhase k₀ P J 0 ↔ s = 0 :=
    (physicalJacobiPhase_injective k₀ P J).eq_iff
  simpa only [physicalJacobiPhase_zero] using h

theorem regionIIPhysicalPhase_hasDerivAt
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (s : ℝ) :
    HasDerivAt (regionIIPhysicalPhase k₀ P J)
      (compiledPhaseSlope k₀ (regionIIAmplitudeOscillator P J) s) s := by
  rw [regionIIPhysicalPhase]
  exact compiledPhase_hasDerivAt k₀ (regionIIAmplitudeOscillator P J) s

theorem regionIIPhysicalPhase_strictMono
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    StrictMono (regionIIPhysicalPhase k₀ P J) :=
  strictMono_of_hasDerivAt_pos
    (regionIIPhysicalPhase_hasDerivAt k₀ P J)
    (regionIICompiledPhaseSlope_pos k₀ P J)

theorem regionIIPhysicalPhase_injective
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    Function.Injective (regionIIPhysicalPhase k₀ P J) :=
  (regionIIPhysicalPhase_strictMono k₀ P J).injective

@[simp] theorem regionIIPhysicalPhase_zero
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    regionIIPhysicalPhase k₀ P J 0 = 0 := by
  rw [regionIIPhysicalPhase, compiledPhase]
  simp

theorem regionIIPhysicalPhase_pos_iff
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (s : ℝ) :
    0 < regionIIPhysicalPhase k₀ P J s ↔ 0 < s := by
  have h : regionIIPhysicalPhase k₀ P J 0 < regionIIPhysicalPhase k₀ P J s ↔ 0 < s :=
    (regionIIPhysicalPhase_strictMono k₀ P J).lt_iff_lt
  simpa only [regionIIPhysicalPhase_zero] using h

theorem regionIIPhysicalPhase_neg_iff
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (s : ℝ) :
    regionIIPhysicalPhase k₀ P J s < 0 ↔ s < 0 := by
  have h : regionIIPhysicalPhase k₀ P J s < regionIIPhysicalPhase k₀ P J 0 ↔ s < 0 :=
    (regionIIPhysicalPhase_strictMono k₀ P J).lt_iff_lt
  simpa only [regionIIPhysicalPhase_zero] using h

theorem regionIIPhysicalPhase_eq_zero_iff
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (s : ℝ) :
    regionIIPhysicalPhase k₀ P J s = 0 ↔ s = 0 := by
  have h : regionIIPhysicalPhase k₀ P J s = regionIIPhysicalPhase k₀ P J 0 ↔ s = 0 :=
    (regionIIPhysicalPhase_injective k₀ P J).eq_iff
  simpa only [regionIIPhysicalPhase_zero] using h

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
