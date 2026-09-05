import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiSystem
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# Jacobi quotient charts

The paper's unselected alternatives `sc = sn/cn` and `sd = sn/dn` are realized from the same
abstract Jacobi system.  Denominator regularity is carried by point data, making derivative and
quartic first-integral theorems closed.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

structure JacobiCnRegularPoint {m : ℝ} (J : JacobiEllipticSystem m) where
  val : ℝ
  denominator_ne : J.cn val ≠ 0

structure JacobiDnRegularPoint {m : ℝ} (J : JacobiEllipticSystem m) where
  val : ℝ
  denominator_ne : J.dn val ≠ 0

noncomputable def jacobiSc {m : ℝ} (J : JacobiEllipticSystem m) (x : ℝ) : ℝ :=
  J.sn x / J.cn x

noncomputable def jacobiScVelocity {m : ℝ} (J : JacobiEllipticSystem m) (x : ℝ) : ℝ :=
  J.dn x / J.cn x ^ 2

theorem jacobiSc_hasDerivAt {m : ℝ} (J : JacobiEllipticSystem m)
    (x : JacobiCnRegularPoint J) :
    HasDerivAt (jacobiSc J) (jacobiScVelocity J x.val) x.val := by
  have h := (J.sn_deriv x.val).div (J.cn_deriv x.val) x.denominator_ne
  have hderiv :
      ((J.cn x.val * J.dn x.val) * J.cn x.val -
          J.sn x.val * (-(J.sn x.val * J.dn x.val))) /
          J.cn x.val ^ 2 = jacobiScVelocity J x.val := by
    rw [jacobiScVelocity]
    have hquad := J.sn_sq_add_cn_sq x.val
    field_simp [x.denominator_ne]
    linear_combination J.dn x.val * hquad
  exact h.congr_deriv hderiv

theorem jacobiSc_firstIntegral {m : ℝ} (J : JacobiEllipticSystem m)
    (x : JacobiCnRegularPoint J) :
    jacobiScVelocity J x.val ^ 2 =
      (1 + jacobiSc J x.val ^ 2) *
        (1 + (1 - m) * jacobiSc J x.val ^ 2) := by
  rw [jacobiScVelocity, jacobiSc]
  have hcn := J.sn_sq_add_cn_sq x.val
  have hdn := J.dn_sq_add_m_sn_sq x.val
  field_simp [x.denominator_ne]
  nlinarith [sq_nonneg (J.sn x.val), sq_nonneg (J.cn x.val)]

theorem jacobiSc_zero {m : ℝ} (J : JacobiEllipticSystem m) :
    jacobiSc J 0 = 0 := by
  rw [jacobiSc, J.sn_zero]
  norm_num

theorem jacobiScVelocity_zero {m : ℝ} (J : JacobiEllipticSystem m) :
    jacobiScVelocity J 0 = 1 := by
  rw [jacobiScVelocity, J.cn_zero, J.dn_zero]
  norm_num

noncomputable def jacobiSd {m : ℝ} (J : JacobiEllipticSystem m) (x : ℝ) : ℝ :=
  J.sn x / J.dn x

noncomputable def jacobiSdVelocity {m : ℝ} (J : JacobiEllipticSystem m) (x : ℝ) : ℝ :=
  J.cn x / J.dn x ^ 2

theorem jacobiSd_hasDerivAt {m : ℝ} (J : JacobiEllipticSystem m)
    (x : JacobiDnRegularPoint J) :
    HasDerivAt (jacobiSd J) (jacobiSdVelocity J x.val) x.val := by
  have h := (J.sn_deriv x.val).div (J.dn_deriv x.val) x.denominator_ne
  have hderiv :
      ((J.cn x.val * J.dn x.val) * J.dn x.val -
          J.sn x.val * (-(m * (J.sn x.val * J.cn x.val)))) /
          J.dn x.val ^ 2 = jacobiSdVelocity J x.val := by
    rw [jacobiSdVelocity]
    have hquad := J.dn_sq_add_m_sn_sq x.val
    field_simp [x.denominator_ne]
    linear_combination J.cn x.val * hquad
  exact h.congr_deriv hderiv

theorem jacobiSd_firstIntegral {m : ℝ} (J : JacobiEllipticSystem m)
    (x : JacobiDnRegularPoint J) :
    jacobiSdVelocity J x.val ^ 2 =
      (1 - (1 - m) * jacobiSd J x.val ^ 2) *
        (1 + m * jacobiSd J x.val ^ 2) := by
  rw [jacobiSdVelocity, jacobiSd]
  have hcn := J.sn_sq_add_cn_sq x.val
  have hdn := J.dn_sq_add_m_sn_sq x.val
  field_simp [x.denominator_ne]
  nlinarith [sq_nonneg (J.sn x.val), sq_nonneg (J.dn x.val)]

theorem jacobiSd_zero {m : ℝ} (J : JacobiEllipticSystem m) :
    jacobiSd J 0 = 0 := by
  rw [jacobiSd, J.sn_zero]
  norm_num

theorem jacobiSdVelocity_zero {m : ℝ} (J : JacobiEllipticSystem m) :
    jacobiSdVelocity J 0 = 1 := by
  rw [jacobiSdVelocity, J.cn_zero, J.dn_zero]
  norm_num

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
