import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiAmplitudeDynamics
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-!
# Energy of the corrected Jacobi amplitude

The squared-curvature first integral transports to an energy law for the positive geometric
amplitude.  Its potential has quartic, quadratic, and inverse-square parts; the inverse-square
barrier is exactly the contribution of torsion.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

theorem correctedJacobiAmplitudeVelocity_sq
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
  correctedJacobiAmplitudeVelocity P J v ^ 2 =
      (P.val.q₀ : ℝ) * (1 - correctedJacobiAmplitude P J v ^ 2) *
        (correctedJacobiAmplitude P J v ^ 4 +
          (1 + gammaSq P.val) * correctedJacobiAmplitude P J v ^ 2 -
          nuSq P.val) / correctedJacobiAmplitude P J v ^ 2 := by
  rw [correctedJacobiAmplitudeVelocity]
  have hq := jacobiSquaredCurvature_equation P.val J v
  rw [dimensionlessCurvatureRHSWithSquares,
    correctedJacobiAmplitude_curvature] at hq
  field_simp [P.val.q₀.ne_zero,
    ne_of_gt (correctedJacobiAmplitude_pos P J v)]
  rw [hq]
  ring

noncomputable def correctedJacobiAmplitudeEnergy
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) : ℝ :=
  correctedJacobiAmplitudeVelocity P J v ^ 2 / 2 +
    (P.val.q₀ : ℝ) * correctedJacobiAmplitude P J v ^ 4 / 2 +
    (P.val.q₀ : ℝ) * gammaSq P.val * correctedJacobiAmplitude P J v ^ 2 / 2 +
    (P.val.q₀ : ℝ) * nuSq P.val /
      (2 * correctedJacobiAmplitude P J v ^ 2)

/-- Energy level fixed by the centered initial condition `A(0)=1`, `A'(0)=0`. -/
theorem correctedJacobiAmplitudeEnergy_eq
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    correctedJacobiAmplitudeEnergy P J v =
      (P.val.q₀ : ℝ) * (1 + gammaSq P.val + nuSq P.val) / 2 := by
  rw [correctedJacobiAmplitudeEnergy, correctedJacobiAmplitudeVelocity_sq]
  field_simp [ne_of_gt (correctedJacobiAmplitude_pos P J v)]
  ring

theorem correctedJacobiAmplitudeEnergy_zero
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) :
    correctedJacobiAmplitudeEnergy P J 0 =
      (P.val.q₀ : ℝ) * (1 + gammaSq P.val + nuSq P.val) / 2 :=
  correctedJacobiAmplitudeEnergy_eq P J 0

theorem correctedJacobiAmplitudeEnergy_hasDerivAt_zero
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    HasDerivAt (correctedJacobiAmplitudeEnergy P J) 0 v := by
  have hconst := hasDerivAt_const v
    ((P.val.q₀ : ℝ) * (1 + gammaSq P.val + nuSq P.val) / 2)
  apply hconst.congr_of_eventuallyEq
  filter_upwards with y
  exact correctedJacobiAmplitudeEnergy_eq P J y

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
