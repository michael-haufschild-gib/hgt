import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiAmplitude
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiSecondOrder
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Correct Jacobi-amplitude dynamics

The positive square-root amplitude attached to the elastica curvature has a globally defined
first and second derivative throughout physical region I.  Eliminating the squared curvature gives
an autonomous cubic-plus-inverse-cubic oscillator.  The inverse-cubic term is the torsion barrier.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def correctedJacobiAmplitudeVelocity
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) : ℝ :=
  jacobiSquaredCurvatureVelocity P.val J v /
    (2 * (P.val.q₀ : ℝ) * correctedJacobiAmplitude P J v)

theorem correctedJacobiAmplitude_hasDerivAt
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    HasDerivAt (correctedJacobiAmplitude P J)
      (correctedJacobiAmplitudeVelocity P J v) v := by
  have hratio := (jacobiSquaredCurvature_hasDerivAt P.val J v).div_const
    (P.val.q₀ : ℝ)
  have hsqrt := HasDerivAt.sqrt hratio
    (ne_of_gt (physicalRegionI_jacobiCurvatureRatio_pos P J v))
  have hderiv :
      (jacobiSquaredCurvatureVelocity P.val J v / (P.val.q₀ : ℝ)) /
          (2 * correctedJacobiAmplitude P J v) =
        correctedJacobiAmplitudeVelocity P J v := by
    rw [correctedJacobiAmplitudeVelocity]
    field_simp [P.val.q₀.ne_zero,
      ne_of_gt (correctedJacobiAmplitude_pos P J v)]
  change HasDerivAt
    (fun y => Real.sqrt
      (jacobiSquaredCurvature P.val J y / (P.val.q₀ : ℝ)))
    (correctedJacobiAmplitudeVelocity P J v) v
  exact hsqrt.congr_deriv hderiv

noncomputable def correctedJacobiAmplitudeAcceleration
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) : ℝ :=
  jacobiSquaredCurvatureAcceleration P.val J v /
      (2 * (P.val.q₀ : ℝ) * correctedJacobiAmplitude P J v) -
    jacobiSquaredCurvatureVelocity P.val J v ^ 2 /
      (4 * (P.val.q₀ : ℝ) ^ 2 * correctedJacobiAmplitude P J v ^ 3)

theorem correctedJacobiAmplitudeVelocity_hasDerivAt
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    HasDerivAt (correctedJacobiAmplitudeVelocity P J)
      (correctedJacobiAmplitudeAcceleration P J v) v := by
  have hq := jacobiSquaredCurvatureVelocity_hasDerivAt P.val J v
  have hA := correctedJacobiAmplitude_hasDerivAt P J v
  have hden := HasDerivAt.const_mul (2 * (P.val.q₀ : ℝ)) hA
  have hden_ne :
      2 * (P.val.q₀ : ℝ) * correctedJacobiAmplitude P J v ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero P.val.q₀.ne_zero)
      (ne_of_gt (correctedJacobiAmplitude_pos P J v))
  have hquot := hq.div hden hden_ne
  have hderiv :
      (jacobiSquaredCurvatureAcceleration P.val J v *
            (2 * (P.val.q₀ : ℝ) * correctedJacobiAmplitude P J v) -
          jacobiSquaredCurvatureVelocity P.val J v *
            ((2 * (P.val.q₀ : ℝ)) * correctedJacobiAmplitudeVelocity P J v)) /
          (2 * (P.val.q₀ : ℝ) * correctedJacobiAmplitude P J v) ^ 2 =
        correctedJacobiAmplitudeAcceleration P J v := by
    rw [correctedJacobiAmplitudeAcceleration, correctedJacobiAmplitudeVelocity]
    field_simp [P.val.q₀.ne_zero,
      ne_of_gt (correctedJacobiAmplitude_pos P J v)]
    ring
  apply (hquot.congr_deriv hderiv).congr_of_eventuallyEq
  filter_upwards with y
  change jacobiSquaredCurvatureVelocity P.val J y /
      (2 * (P.val.q₀ : ℝ) * correctedJacobiAmplitude P J y) =
    jacobiSquaredCurvatureVelocity P.val J y /
      (2 * (P.val.q₀ : ℝ) * correctedJacobiAmplitude P J y)
  rfl

theorem correctedJacobiAmplitude_curvature
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    jacobiSquaredCurvature P.val J v =
      (P.val.q₀ : ℝ) * correctedJacobiAmplitude P J v ^ 2 := by
  rw [jacobiSquaredCurvature, correctedJacobiAmplitude_sq]
  field_simp [P.val.q₀.ne_zero]

/-- Autonomous oscillator for the corrected elastica amplitude. -/
theorem correctedJacobiAmplitude_secondOrderEquation
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    correctedJacobiAmplitudeAcceleration P J v =
      -2 * (P.val.q₀ : ℝ) * correctedJacobiAmplitude P J v ^ 3 -
        (P.val.q₀ : ℝ) * gammaSq P.val * correctedJacobiAmplitude P J v +
        (P.val.q₀ : ℝ) * nuSq P.val /
          correctedJacobiAmplitude P J v ^ 3 := by
  rw [correctedJacobiAmplitudeAcceleration,
    jacobiSquaredCurvature_secondOrderEquation,
    jacobiSquaredCurvature_equation,
    dimensionlessCurvatureRHSWithSquares,
    correctedJacobiAmplitude_curvature]
  field_simp [P.val.q₀.ne_zero,
    ne_of_gt (correctedJacobiAmplitude_pos P J v)]
  ring

theorem correctedJacobiAmplitudeVelocity_zero
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) :
    correctedJacobiAmplitudeVelocity P J 0 = 0 := by
  rw [correctedJacobiAmplitudeVelocity, jacobiSquaredCurvatureVelocity_zero]
  ring

theorem correctedJacobiAmplitudeAcceleration_zero
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) :
    correctedJacobiAmplitudeAcceleration P J 0 =
      -P.val.modulus / (P.val.q₀ : ℝ) := by
  rw [correctedJacobiAmplitudeAcceleration,
    jacobiSquaredCurvatureAcceleration_zero,
    jacobiSquaredCurvatureVelocity_zero,
    correctedJacobiAmplitude_zero]
  field_simp [P.val.q₀.ne_zero]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
