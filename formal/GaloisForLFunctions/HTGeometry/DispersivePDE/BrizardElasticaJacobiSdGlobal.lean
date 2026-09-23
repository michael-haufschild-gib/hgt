import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiAmplitude
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiQuotients
import Mathlib.Tactic

/-!
# Global `sd` dynamics in the classical modulus chamber

For `0 < m < 1`, the Jacobi quadratic identities force `dn² ≥ 1-m > 0`.  Thus the quotient
`sd=sn/dn` has no real poles.  This upgrades the local quotient-chart results to global first- and
second-order differential laws needed by the paper's real Region II continuation.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

theorem classicalJacobiDn_sq_pos
    (m : ClassicalModulus) (J : JacobiEllipticSystem (m : ℝ)) (x : ℝ) :
    0 < J.dn x ^ (2 : ℕ) := by
  have hsn := J.sn_sq_le_one x
  have hdn := J.dn_sq_add_m_sn_sq x
  have hsn0 := sq_nonneg (J.sn x)
  nlinarith [m.property.1, m.property.2]

theorem classicalJacobiDn_ne_zero
    (m : ClassicalModulus) (J : JacobiEllipticSystem (m : ℝ)) (x : ℝ) :
    J.dn x ≠ 0 := by
  intro h
  have hpos := classicalJacobiDn_sq_pos m J x
  rw [h] at hpos
  norm_num at hpos

noncomputable def classicalJacobiDnRegularPoint
    (m : ClassicalModulus) (J : JacobiEllipticSystem (m : ℝ)) (x : ℝ) :
    JacobiDnRegularPoint J where
  val := x
  denominator_ne := classicalJacobiDn_ne_zero m J x

theorem jacobiSd_hasDerivAt_global
    (m : ClassicalModulus) (J : JacobiEllipticSystem (m : ℝ)) (x : ℝ) :
    HasDerivAt (jacobiSd J) (jacobiSdVelocity J x) x := by
  exact jacobiSd_hasDerivAt J (classicalJacobiDnRegularPoint m J x)

theorem jacobiSd_firstIntegral_global
    (m : ClassicalModulus) (J : JacobiEllipticSystem (m : ℝ)) (x : ℝ) :
    jacobiSdVelocity J x ^ (2 : ℕ) =
      (1 - (1 - (m : ℝ)) * jacobiSd J x ^ (2 : ℕ)) *
        (1 + (m : ℝ) * jacobiSd J x ^ (2 : ℕ)) := by
  exact jacobiSd_firstIntegral J (classicalJacobiDnRegularPoint m J x)

noncomputable def jacobiSdAcceleration
    {m : ℝ} (J : JacobiEllipticSystem m) (x : ℝ) : ℝ :=
  (2 * m - 1) * jacobiSd J x -
    2 * m * (1 - m) * jacobiSd J x ^ (3 : ℕ)

theorem jacobiSdVelocity_hasDerivAt_global
    (m : ClassicalModulus) (J : JacobiEllipticSystem (m : ℝ)) (x : ℝ) :
    HasDerivAt (jacobiSdVelocity J) (jacobiSdAcceleration J x) x := by
  have hden := (J.dn_deriv x).fun_pow 2
  norm_num at hden
  have h := (J.cn_deriv x).div hden
    (pow_ne_zero 2 (classicalJacobiDn_ne_zero m J x))
  have hcn := J.sn_sq_add_cn_sq x
  have hdn := J.dn_sq_add_m_sn_sq x
  have hdne := classicalJacobiDn_ne_zero m J x
  change HasDerivAt (fun y : ℝ => J.cn y / J.dn y ^ (2 : ℕ))
    (jacobiSdAcceleration J x) x
  apply h.congr_deriv
  rw [jacobiSdAcceleration, jacobiSd]
  field_simp [hdne]
  linear_combination
    2 * (m : ℝ) * J.sn x * hcn - 2 * (m : ℝ) * J.sn x * hdn

theorem jacobiSdAcceleration_zero
    (m : ClassicalModulus) (J : JacobiEllipticSystem (m : ℝ)) :
    jacobiSdAcceleration J 0 = 0 := by
  rw [jacobiSdAcceleration, jacobiSd_zero]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
