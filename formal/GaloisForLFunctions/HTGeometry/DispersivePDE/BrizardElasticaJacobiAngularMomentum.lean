import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiRadialGap
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Angular momentum of the Jacobi elastica

The positive region-I square root `Ω` turns the paper's azimuthal quadrature into a globally
regular angular velocity.  Multiplication by the squared radial amplitude exposes an exactly
constant angular momentum in the co-rotating frame.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def physicalAngularOmega (P : PhysicalRegionI) : ℝ :=
  Real.sqrt (angularOmegaSq (physicalRegionIAngularParameters P))

theorem physicalAngularOmegaSq_pos (P : PhysicalRegionI) :
    0 < angularOmegaSq (physicalRegionIAngularParameters P) := by
  rw [angularOmegaSq]
  exact div_pos
    (mul_pos (by norm_num) (physicalRegionI_nuSq_pos P))
    (angularOmegaSq_den_pos (physicalRegionIAngularParameters P))

theorem physicalAngularOmega_pos (P : PhysicalRegionI) :
    0 < physicalAngularOmega P := by
  rw [physicalAngularOmega]
  exact Real.sqrt_pos.2 (physicalAngularOmegaSq_pos P)

theorem physicalAngularOmega_sq (P : PhysicalRegionI) :
    physicalAngularOmega P ^ 2 =
      angularOmegaSq (physicalRegionIAngularParameters P) := by
  rw [physicalAngularOmega,
    Real.sq_sqrt (physicalAngularOmegaSq_pos P).le]

theorem physicalAngularOmega_lt_one (P : PhysicalRegionI) :
    physicalAngularOmega P < 1 := by
  have hs := physicalAngularOmega_sq P
  have hΩ := angularOmegaSq_lt_one (physicalRegionIAngularParameters P)
  have hp := physicalAngularOmega_pos P
  nlinarith

/-- Dimensionless version of the paper's angular equation (96). -/
noncomputable def jacobiAngularVelocity
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) : ℝ :=
  physicalAngularOmega P *
    (1 +
      (physicalAngularOmega P ^ 2 + gammaSq P.val / 2) /
        (correctedJacobiAmplitude P J v ^ 2 -
          physicalAngularOmega P ^ 2))

/-- Radial-denominator form of the same angular equation. -/
theorem jacobiAngularVelocity_eq_radial
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    jacobiAngularVelocity P J v =
      physicalAngularOmega P *
        (1 +
          (physicalAngularOmega P ^ 2 + gammaSq P.val / 2) /
            jacobiRadialAmplitude P J v ^ 2) := by
  have hgap :
      correctedJacobiAmplitude P J v ^ 2 - physicalAngularOmega P ^ 2 =
        jacobiRadialAmplitude P J v ^ 2 := by
    rw [physicalAngularOmega_sq, jacobiRadialAmplitude_sq,
      correctedJacobiAmplitude_sq]
    ring
  rw [jacobiAngularVelocity, hgap]

theorem jacobiAngularVelocity_pos
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    0 < jacobiAngularVelocity P J v := by
  rw [jacobiAngularVelocity]
  have hden :=
    physicalRegionI_correctedAmplitude_sq_sub_angularOmegaSq_pos P J v
  rw [physicalAngularOmega_sq]
  have hnum :
      0 < angularOmegaSq (physicalRegionIAngularParameters P) +
        gammaSq P.val / 2 := by
    nlinarith [physicalAngularOmegaSq_pos P, physicalRegionI_gammaSq_pos P]
  exact mul_pos (physicalAngularOmega_pos P)
    (by have := div_pos hnum hden; linarith)

noncomputable def jacobiAngularAcceleration
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) : ℝ :=
  -2 * physicalAngularOmega P *
      (physicalAngularOmega P ^ 2 + gammaSq P.val / 2) *
      correctedJacobiAmplitude P J v * correctedJacobiAmplitudeVelocity P J v /
    (correctedJacobiAmplitude P J v ^ 2 -
      physicalAngularOmega P ^ 2) ^ 2

theorem jacobiAngularVelocity_hasDerivAt
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    HasDerivAt (jacobiAngularVelocity P J)
      (jacobiAngularAcceleration P J v) v := by
  have hA := correctedJacobiAmplitude_hasDerivAt P J v
  have hsq := hA.fun_pow 2
  norm_num at hsq
  have hgap := hsq.sub_const (physicalAngularOmega P ^ 2)
  have hgap_ne :
      correctedJacobiAmplitude P J v ^ 2 - physicalAngularOmega P ^ 2 ≠ 0 := by
    rw [physicalAngularOmega_sq]
    exact ne_of_gt
      (physicalRegionI_correctedAmplitude_sq_sub_angularOmegaSq_pos P J v)
  have hconst := hasDerivAt_const v
    (physicalAngularOmega P ^ 2 + gammaSq P.val / 2)
  have hdiv := hconst.div hgap hgap_ne
  have hadd := hdiv.const_add 1
  have h := HasDerivAt.const_mul (physicalAngularOmega P) hadd
  have hderiv :
      physicalAngularOmega P *
          ((0 * (correctedJacobiAmplitude P J v ^ 2 -
                physicalAngularOmega P ^ 2) -
              (physicalAngularOmega P ^ 2 + gammaSq P.val / 2) *
                (2 * correctedJacobiAmplitude P J v *
                  correctedJacobiAmplitudeVelocity P J v)) /
            (correctedJacobiAmplitude P J v ^ 2 -
              physicalAngularOmega P ^ 2) ^ 2) =
        jacobiAngularAcceleration P J v := by
    rw [jacobiAngularAcceleration]
    ring
  change HasDerivAt
    (fun y => physicalAngularOmega P *
      (1 + (physicalAngularOmega P ^ 2 + gammaSq P.val / 2) /
        (correctedJacobiAmplitude P J y ^ 2 -
          physicalAngularOmega P ^ 2)))
    (jacobiAngularAcceleration P J v) v
  exact h.congr_deriv hderiv

theorem jacobiAngularAcceleration_zero
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) :
    jacobiAngularAcceleration P J 0 = 0 := by
  rw [jacobiAngularAcceleration, correctedJacobiAmplitudeVelocity_zero]
  ring

noncomputable def jacobiCorotatingAngularMomentum
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) : ℝ :=
  jacobiRadialAmplitude P J v ^ 2 *
    (jacobiAngularVelocity P J v - physicalAngularOmega P)

/-- The co-rotating angular momentum is independent of position. -/
theorem jacobiCorotatingAngularMomentum_eq
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    jacobiCorotatingAngularMomentum P J v =
      physicalAngularOmega P *
        (physicalAngularOmega P ^ 2 + gammaSq P.val / 2) := by
  rw [jacobiCorotatingAngularMomentum, jacobiAngularVelocity_eq_radial]
  field_simp [ne_of_gt (jacobiRadialAmplitude_pos P J v)]
  ring

theorem jacobiCorotatingAngularMomentum_pos
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    0 < jacobiCorotatingAngularMomentum P J v := by
  rw [jacobiCorotatingAngularMomentum_eq]
  exact mul_pos (physicalAngularOmega_pos P)
    (by nlinarith [physicalAngularOmegaSq_pos P,
      physicalRegionI_gammaSq_pos P, physicalAngularOmega_sq P])

theorem jacobiCorotatingAngularMomentum_hasDerivAt_zero
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    HasDerivAt (jacobiCorotatingAngularMomentum P J) 0 v := by
  have hconst := hasDerivAt_const v
    (physicalAngularOmega P *
      (physicalAngularOmega P ^ 2 + gammaSq P.val / 2))
  apply hconst.congr_of_eventuallyEq
  filter_upwards with y
  exact jacobiCorotatingAngularMomentum_eq P J y

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
