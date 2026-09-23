import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaRegionIIJacobi
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Positive Region II Jacobi amplitude

The real `sd` curvature is normalized by its positive transformed scale and square-rooted.  Its
derivatives, inverse-cubic oscillator, velocity first integral, and conserved energy are all global.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def regionIIJacobiAmplitude
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) : ℝ :=
  Real.sqrt (regionIIJacobiSquaredCurvature P J x / regionIIRealScale P)

theorem regionIIJacobiAmplitude_pos
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) :
    0 < regionIIJacobiAmplitude P J x := by
  rw [regionIIJacobiAmplitude]
  exact Real.sqrt_pos.2
    (div_pos (regionIIJacobiSquaredCurvature_pos P J x) (regionIIRealScale_pos P))

theorem regionIIJacobiAmplitude_sq
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) :
    regionIIJacobiAmplitude P J x ^ (2 : ℕ) =
      1 + regionIITransformedModulus P / (-(P.val.q₀ : ℝ)) *
        jacobiSd J x ^ (2 : ℕ) := by
  rw [regionIIJacobiAmplitude,
    Real.sq_sqrt (div_nonneg
      (regionIIJacobiSquaredCurvature_pos P J x).le
      (regionIIRealScale_pos P).le),
    regionIIJacobiSquaredCurvature_explicit]

theorem regionIIJacobiAmplitude_zero
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    regionIIJacobiAmplitude P J 0 = 1 := by
  have hsq := regionIIJacobiAmplitude_sq P J 0
  rw [jacobiSd_zero] at hsq
  have hpos := regionIIJacobiAmplitude_pos P J 0
  nlinarith

noncomputable def regionIIJacobiAmplitudeVelocity
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) : ℝ :=
  regionIIJacobiSquaredCurvatureVelocity P J x /
    (2 * regionIIRealScale P * regionIIJacobiAmplitude P J x)

theorem regionIIJacobiAmplitude_hasDerivAt
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) :
    HasDerivAt (regionIIJacobiAmplitude P J)
      (regionIIJacobiAmplitudeVelocity P J x) x := by
  have hratio := (regionIIJacobiSquaredCurvature_hasDerivAt P J x).div_const
    (regionIIRealScale P)
  have hsqrt := HasDerivAt.sqrt hratio
    (ne_of_gt (div_pos (regionIIJacobiSquaredCurvature_pos P J x)
      (regionIIRealScale_pos P)))
  change HasDerivAt
    (fun y => Real.sqrt
      (regionIIJacobiSquaredCurvature P J y / regionIIRealScale P))
    (regionIIJacobiAmplitudeVelocity P J x) x
  apply hsqrt.congr_deriv
  rw [regionIIJacobiAmplitudeVelocity, regionIIJacobiAmplitude]
  field_simp [ne_of_gt (regionIIRealScale_pos P),
    ne_of_gt (regionIIJacobiAmplitude_pos P J x)]

noncomputable def regionIIJacobiAmplitudeAcceleration
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) : ℝ :=
  regionIIJacobiSquaredCurvatureAcceleration P J x /
      (2 * regionIIRealScale P * regionIIJacobiAmplitude P J x) -
    regionIIJacobiSquaredCurvatureVelocity P J x ^ (2 : ℕ) /
      (4 * regionIIRealScale P ^ (2 : ℕ) * regionIIJacobiAmplitude P J x ^ (3 : ℕ))

theorem regionIIJacobiAmplitudeVelocity_hasDerivAt
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) :
    HasDerivAt (regionIIJacobiAmplitudeVelocity P J)
      (regionIIJacobiAmplitudeAcceleration P J x) x := by
  have hq := regionIIJacobiSquaredCurvatureVelocity_hasDerivAt P J x
  have hA := regionIIJacobiAmplitude_hasDerivAt P J x
  have hden := HasDerivAt.const_mul (2 * regionIIRealScale P) hA
  have hden_ne :
      2 * regionIIRealScale P * regionIIJacobiAmplitude P J x ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (ne_of_gt (regionIIRealScale_pos P)))
      (ne_of_gt (regionIIJacobiAmplitude_pos P J x))
  have hquot := hq.div hden hden_ne
  have hderiv :
      (regionIIJacobiSquaredCurvatureAcceleration P J x *
            (2 * regionIIRealScale P * regionIIJacobiAmplitude P J x) -
          regionIIJacobiSquaredCurvatureVelocity P J x *
            ((2 * regionIIRealScale P) * regionIIJacobiAmplitudeVelocity P J x)) /
          (2 * regionIIRealScale P * regionIIJacobiAmplitude P J x) ^ (2 : ℕ) =
        regionIIJacobiAmplitudeAcceleration P J x := by
    rw [regionIIJacobiAmplitudeAcceleration, regionIIJacobiAmplitudeVelocity]
    field_simp [ne_of_gt (regionIIRealScale_pos P),
      ne_of_gt (regionIIJacobiAmplitude_pos P J x)]
    ring
  apply (hquot.congr_deriv hderiv).congr_of_eventuallyEq
  filter_upwards with y
  rfl

theorem regionIIJacobiAmplitude_curvature
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) :
    regionIIJacobiSquaredCurvature P J x =
      regionIIRealScale P * regionIIJacobiAmplitude P J x ^ (2 : ℕ) := by
  rw [regionIIJacobiAmplitude, Real.sq_sqrt
    (div_nonneg (regionIIJacobiSquaredCurvature_pos P J x).le
      (regionIIRealScale_pos P).le)]
  field_simp [ne_of_gt (regionIIRealScale_pos P)]

/-- Region II amplitude oscillator; inverse cubic term is again the torsion barrier. -/
theorem regionIIJacobiAmplitude_secondOrderEquation
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) :
    regionIIJacobiAmplitudeAcceleration P J x =
      -2 * regionIIRealScale P * regionIIJacobiAmplitude P J x ^ (3 : ℕ) -
        regionIIRealScale P * gammaSq P.val * regionIIJacobiAmplitude P J x +
        regionIIRealScale P * nuSq P.val /
          regionIIJacobiAmplitude P J x ^ (3 : ℕ) := by
  rw [regionIIJacobiAmplitudeAcceleration,
    regionIIJacobiSquaredCurvature_secondOrderEquation,
    regionIIJacobiSquaredCurvature_equation,
    dimensionlessCurvatureRHSWithSquares,
    regionIIJacobiAmplitude_curvature]
  field_simp [ne_of_gt (regionIIRealScale_pos P),
    ne_of_gt (regionIIJacobiAmplitude_pos P J x)]
  ring

theorem regionIIJacobiAmplitudeVelocity_zero
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    regionIIJacobiAmplitudeVelocity P J 0 = 0 := by
  rw [regionIIJacobiAmplitudeVelocity,
    regionIIJacobiSquaredCurvatureVelocity_zero]
  ring

/-- Unlike Region I's usual crest, Region II's origin is a strict local curvature trough. -/
theorem regionIIJacobiAmplitudeAcceleration_zero_pos
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    0 < regionIIJacobiAmplitudeAcceleration P J 0 := by
  rw [regionIIJacobiAmplitudeAcceleration,
    regionIIJacobiSquaredCurvatureAcceleration_zero,
    regionIIJacobiSquaredCurvatureVelocity_zero,
    regionIIJacobiAmplitude_zero]
  have hr := (regionIIComplementModulus P).property
  have hs := regionIIRealScale_pos P
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hmain := div_pos
    (mul_pos (mul_pos htwo hr.1) (sub_pos.mpr hr.2))
    (mul_pos htwo hs)
  norm_num
  simpa only [regionIIComplementModulus_val, one_div] using hmain

theorem regionIIJacobiAmplitudeVelocity_sq
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) :
    regionIIJacobiAmplitudeVelocity P J x ^ (2 : ℕ) =
      regionIIRealScale P *
        (1 + gammaSq P.val + nuSq P.val -
          regionIIJacobiAmplitude P J x ^ (4 : ℕ) -
          gammaSq P.val * regionIIJacobiAmplitude P J x ^ (2 : ℕ) -
          nuSq P.val / regionIIJacobiAmplitude P J x ^ (2 : ℕ)) := by
  rw [regionIIJacobiAmplitudeVelocity,
    div_pow,
    regionIIJacobiSquaredCurvature_equation,
    dimensionlessCurvatureRHSWithSquares,
    regionIIJacobiAmplitude_curvature]
  field_simp [ne_of_gt (regionIIRealScale_pos P),
    ne_of_gt (regionIIJacobiAmplitude_pos P J x)]
  ring

noncomputable def regionIIJacobiAmplitudeEnergy
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) : ℝ :=
  regionIIJacobiAmplitudeVelocity P J x ^ (2 : ℕ) / 2 +
    regionIIRealScale P * regionIIJacobiAmplitude P J x ^ (4 : ℕ) / 2 +
    regionIIRealScale P * gammaSq P.val * regionIIJacobiAmplitude P J x ^ (2 : ℕ) / 2 +
    regionIIRealScale P * nuSq P.val /
      (2 * regionIIJacobiAmplitude P J x ^ (2 : ℕ))

theorem regionIIJacobiAmplitudeEnergy_eq
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) :
    regionIIJacobiAmplitudeEnergy P J x =
      regionIIRealScale P * (1 + gammaSq P.val + nuSq P.val) / 2 := by
  rw [regionIIJacobiAmplitudeEnergy, regionIIJacobiAmplitudeVelocity_sq]
  field_simp [ne_of_gt (regionIIJacobiAmplitude_pos P J x)]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
