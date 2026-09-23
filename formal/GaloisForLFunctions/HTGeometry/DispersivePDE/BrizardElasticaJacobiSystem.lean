import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiQuartic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# General Jacobi differential system for the elastica ansatz

Mathlib currently has no general real Jacobi `sn/cn/dn` API.  This file supplies the exact closed
interface needed by arXiv:2607.21750 and proves all downstream first-integral, Lamé, and curvature
claims from that interface.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- General-modulus Jacobi triple, specified by its differential system, quadratic identities,
and standard initial values. -/
structure JacobiEllipticSystem (m : ℝ) where
  sn : ℝ → ℝ
  cn : ℝ → ℝ
  dn : ℝ → ℝ
  sn_deriv : ∀ x, HasDerivAt sn (cn x * dn x) x
  cn_deriv : ∀ x, HasDerivAt cn (-(sn x * dn x)) x
  dn_deriv : ∀ x, HasDerivAt dn (-(m * (sn x * cn x))) x
  sn_sq_add_cn_sq : ∀ x, sn x ^ (2 : ℕ) + cn x ^ (2 : ℕ) = 1
  dn_sq_add_m_sn_sq : ∀ x, dn x ^ (2 : ℕ) + m * sn x ^ (2 : ℕ) = 1
  sn_zero : sn 0 = 0
  cn_zero : cn 0 = 1
  dn_zero : dn 0 = 1

/-- General Jacobi first integral `(sn')²=(1-sn²)(1-m sn²)`. -/
theorem JacobiEllipticSystem.sn_firstIntegral
    {m : ℝ} (J : JacobiEllipticSystem m) (x : ℝ) :
    (J.cn x * J.dn x) ^ (2 : ℕ) =
      (1 - J.sn x ^ (2 : ℕ)) * (1 - m * J.sn x ^ (2 : ℕ)) := by
  have hcn : J.cn x ^ (2 : ℕ) = 1 - J.sn x ^ (2 : ℕ) := by
    linarith [J.sn_sq_add_cn_sq x]
  have hdn : J.dn x ^ (2 : ℕ) = 1 - m * J.sn x ^ (2 : ℕ) := by
    linarith [J.dn_sq_add_m_sn_sq x]
  calc
    (J.cn x * J.dn x) ^ (2 : ℕ) = J.cn x ^ (2 : ℕ) * J.dn x ^ (2 : ℕ) := by ring
    _ = _ := by rw [hcn, hdn]

/-- First derivative of `dn` in a named form convenient for second derivatives. -/
noncomputable def JacobiEllipticSystem.dnVelocity
    {m : ℝ} (J : JacobiEllipticSystem m) (x : ℝ) : ℝ :=
  -(m * (J.sn x * J.cn x))

theorem JacobiEllipticSystem.dn_hasDerivAt
    {m : ℝ} (J : JacobiEllipticSystem m) (x : ℝ) :
    HasDerivAt J.dn (J.dnVelocity x) x := by
  exact J.dn_deriv x

/-- General Lamé equation `dn''=(2m sn²-m)dn`. -/
theorem JacobiEllipticSystem.dnVelocity_hasDerivAt
    {m : ℝ} (J : JacobiEllipticSystem m) (x : ℝ) :
    HasDerivAt J.dnVelocity ((2 * m * J.sn x ^ (2 : ℕ) - m) * J.dn x) x := by
  have hprod := (J.sn_deriv x).mul (J.cn_deriv x)
  have h := hprod.const_mul (-m)
  have hderiv :
      -m * ((J.cn x * J.dn x) * J.cn x +
        J.sn x * (-(J.sn x * J.dn x))) =
        (2 * m * J.sn x ^ (2 : ℕ) - m) * J.dn x := by
    have hquad := J.sn_sq_add_cn_sq x
    linear_combination (-m * J.dn x) * hquad
  change HasDerivAt (fun y => -(m * (J.sn y * J.cn y)))
    ((2 * m * J.sn x ^ (2 : ℕ) - m) * J.dn x) x
  simpa only [Pi.mul_apply, neg_mul, hderiv] using! h

/-- Dimensionless curvature cubic with `γ²,ν²` supplied directly. -/
def dimensionlessCurvatureRHSWithSquares
    (q₀ γsq νsq q : ℝ) : ℝ :=
  4 * (q₀ - q) * (q ^ (2 : ℕ) + (1 + γsq) * q₀ * q - q₀ ^ (2 : ℕ) * νsq)

theorem dimensionlessCurvatureRHS_eq_withSquares (q₀ γ ν q : ℝ) :
    dimensionlessCurvatureRHS q₀ γ ν q =
      dimensionlessCurvatureRHSWithSquares q₀ (γ ^ (2 : ℕ)) (ν ^ (2 : ℕ)) q := by
  rfl

/-- Exact pre-cancellation residual when squared parameters are primitive data. -/
theorem curvatureSubstitution_residual_withSquares
    (a q₀ γsq νsq X Y : ℝ) :
    (-2 * a * X * Y) ^ (2 : ℕ) -
        dimensionlessCurvatureRHSWithSquares q₀ γsq νsq (q₀ - a * X ^ (2 : ℕ)) =
      4 * a * X ^ (2 : ℕ) * clearedJacobiResidual a q₀ γsq νsq X Y := by
  rw [dimensionlessCurvatureRHSWithSquares, clearedJacobiResidual]
  ring

/-- Paper's Jacobi ansatz `q(v)=q₀-m sn²(v)`. -/
noncomputable def jacobiSquaredCurvature
    (P : Parameters) (J : JacobiEllipticSystem P.modulus) (v : ℝ) : ℝ :=
  (P.q₀ : ℝ) - P.modulus * J.sn v ^ (2 : ℕ)

noncomputable def jacobiSquaredCurvatureVelocity
    (P : Parameters) (J : JacobiEllipticSystem P.modulus) (v : ℝ) : ℝ :=
  -(P.modulus * (2 * J.sn v * (J.cn v * J.dn v)))

theorem jacobiSquaredCurvature_hasDerivAt
    (P : Parameters) (J : JacobiEllipticSystem P.modulus) (v : ℝ) :
    HasDerivAt (jacobiSquaredCurvature P J)
      (jacobiSquaredCurvatureVelocity P J v) v := by
  have hsq := (J.sn_deriv v).fun_pow 2
  norm_num at hsq
  have hmul := HasDerivAt.const_mul P.modulus hsq
  have h := HasDerivAt.const_sub (P.q₀ : ℝ) hmul
  change HasDerivAt (fun x => (P.q₀ : ℝ) - P.modulus * J.sn x ^ (2 : ℕ))
    (-(P.modulus * (2 * J.sn v * (J.cn v * J.dn v)))) v
  rw [hasDerivAt_iff_hasFDerivAt] at h ⊢
  convert h using 1

theorem jacobiSquaredCurvature_zero
    (P : Parameters) (J : JacobiEllipticSystem P.modulus) :
    jacobiSquaredCurvature P J 0 = (P.q₀ : ℝ) := by
  rw [jacobiSquaredCurvature, J.sn_zero]
  ring

theorem jacobiSquaredCurvatureVelocity_zero
    (P : Parameters) (J : JacobiEllipticSystem P.modulus) :
    jacobiSquaredCurvatureVelocity P J 0 = 0 := by
  rw [jacobiSquaredCurvatureVelocity, J.sn_zero]
  ring

/-- The Jacobi ansatz solves the parameter-only dimensionless curvature equation exactly. -/
theorem jacobiSquaredCurvature_equation
    (P : Parameters) (J : JacobiEllipticSystem P.modulus) (v : ℝ) :
    jacobiSquaredCurvatureVelocity P J v ^ (2 : ℕ) =
      dimensionlessCurvatureRHSWithSquares (P.q₀ : ℝ)
        (gammaSq P) (nuSq P) (jacobiSquaredCurvature P J v) := by
  have hres := curvatureSubstitution_residual_withSquares P.modulus (P.q₀ : ℝ)
    (gammaSq P) (nuSq P) (J.sn v) (J.cn v * J.dn v)
  have hparam := parameterJacobiResidual_factor P (J.sn v) (J.cn v * J.dn v)
  have hfirst := J.sn_firstIntegral v
  rw [hfirst, sub_self, mul_zero] at hparam
  rw [hparam, mul_zero] at hres
  rw [jacobiSquaredCurvatureVelocity, jacobiSquaredCurvature]
  linarith

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
