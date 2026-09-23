import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiSystem
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Second-order Jacobi curvature dynamics

Differentiating the Jacobi ansatz directly gives a globally valid second-order equation, including
at turning points where cancellation by `q'` would be invalid.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def jacobiSquaredCurvatureAcceleration
    (P : Parameters) (J : JacobiEllipticSystem P.modulus) (v : ℝ) : ℝ :=
  -2 * P.modulus *
    ((J.cn v * J.dn v) ^ (2 : ℕ) - (J.sn v * J.dn v) ^ (2 : ℕ) -
      P.modulus * (J.sn v * J.cn v) ^ (2 : ℕ))

theorem jacobiSquaredCurvatureVelocity_hasDerivAt
    (P : Parameters) (J : JacobiEllipticSystem P.modulus) (v : ℝ) :
    HasDerivAt (jacobiSquaredCurvatureVelocity P J)
      (jacobiSquaredCurvatureAcceleration P J v) v := by
  have hsncn := (J.sn_deriv v).mul (J.cn_deriv v)
  have htriple := hsncn.mul (J.dn_deriv v)
  have h := HasDerivAt.const_mul (-2 * P.modulus) htriple
  have hderiv :
      (-2 * P.modulus) *
          (((J.cn v * J.dn v) * J.cn v +
              J.sn v * (-(J.sn v * J.dn v))) * J.dn v +
            (J.sn v * J.cn v) *
              (-(P.modulus * (J.sn v * J.cn v)))) =
        jacobiSquaredCurvatureAcceleration P J v := by
    rw [jacobiSquaredCurvatureAcceleration]
    ring
  apply (h.congr_deriv hderiv).congr_of_eventuallyEq
  filter_upwards with y
  rw [jacobiSquaredCurvatureVelocity]
  simp only [Pi.mul_apply]
  ring

/-- Derivative-polynomial form obtained from equation (62), proved without dividing by `q'`. -/
theorem jacobiSquaredCurvature_secondOrderEquation
    (P : Parameters) (J : JacobiEllipticSystem P.modulus) (v : ℝ) :
    jacobiSquaredCurvatureAcceleration P J v =
      -6 * jacobiSquaredCurvature P J v ^ (2 : ℕ) -
        4 * gammaSq P * (P.q₀ : ℝ) * jacobiSquaredCurvature P J v +
        2 * (1 + nuSq P + gammaSq P) * (P.q₀ : ℝ) ^ (2 : ℕ) := by
  have hcn : J.cn v ^ (2 : ℕ) = 1 - J.sn v ^ (2 : ℕ) := by
    linarith [J.sn_sq_add_cn_sq v]
  have hdn : J.dn v ^ (2 : ℕ) = 1 - P.modulus * J.sn v ^ (2 : ℕ) := by
    linarith [J.dn_sq_add_m_sn_sq v]
  rw [jacobiSquaredCurvatureAcceleration, jacobiSquaredCurvature,
    gammaSq, nuSq]
  rw [show (J.cn v * J.dn v) ^ (2 : ℕ) = J.cn v ^ (2 : ℕ) * J.dn v ^ (2 : ℕ) by ring,
    show (J.sn v * J.dn v) ^ (2 : ℕ) = J.sn v ^ (2 : ℕ) * J.dn v ^ (2 : ℕ) by ring,
    show (J.sn v * J.cn v) ^ (2 : ℕ) = J.sn v ^ (2 : ℕ) * J.cn v ^ (2 : ℕ) by ring,
    hcn, hdn]
  field_simp [P.q₀.ne_zero]
  ring

theorem jacobiSquaredCurvatureAcceleration_zero
    (P : Parameters) (J : JacobiEllipticSystem P.modulus) :
    jacobiSquaredCurvatureAcceleration P J 0 = -2 * P.modulus := by
  rw [jacobiSquaredCurvatureAcceleration, J.sn_zero, J.cn_zero, J.dn_zero]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
