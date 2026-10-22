import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointConformalInverseChart
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointConformalWeightJets
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Actual chart Jacobian and the exact density carried by the field conjugation. -/
namespace RHTower.D4BMJointConformal
open D4BMJointSource
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

theorem chart_fderiv_basis (p : Point3) (i : Fin 3) :
    fderiv ℝ chart p (Pi.single i 1) = chartFirst p i := by
  have h0 := ((chart_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt
    (p i) (coordinateLine_hasDerivAt p i (p i))).deriv
  have h1 := (chartCurve_derivatives p i).1
  simpa only [Function.comp_def,coordinateLine_base] using h0.symm.trans h1

/-- Determinant of the actual coordinate Jacobian is the positive Euclidean height Y. -/
theorem chart_jacobian (p : Point3) :
    Matrix.det (fun j i : Fin 3 => fderiv ℝ chart p (Pi.single i 1) j) = chart p 1 := by
  simp_rw [chart_fderiv_basis]
  rw [Matrix.det_fin_three]
  change (-p 2*warp (p 0)^(2 : ℕ))*0*0 - (-p 2*warp (p 0)^(2 : ℕ))*warp (p 0)*1 -
    0*(p 2*warp (p 0)*radialUnit (p 0))*0 + 0*warp (p 0)*0 +
    radialUnit (p 0)*(p 2*warp (p 0)*radialUnit (p 0))*1 -
    radialUnit (p 0)*0*0 = p 2*warp (p 0)
  linear_combination p 2*warp (p 0)*(warp_relation (p 0))

theorem chart_jacobian_pos (p : Point3) (hp : 0 < p 2) :
    0 < Matrix.det (fun j i : Fin 3 => fderiv ℝ chart p (Pi.single i 1) j) := by
  rw [chart_jacobian]
  exact mul_pos hp (warp_pos _)

/-- The actual field weight has the exact positive square required by the transformed mass density. -/
theorem weight_norm_sq (p : Point3) (hp : 0 < p 2) :
    ‖weight p‖^(2 : ℕ) = p 2/warp (p 0) := by
  rw [weight,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_pos (radialRoot_pos _),mul_pow]
  dsimp [radialRoot,warp]
  rw [Real.sq_sqrt hp.le,Real.sq_sqrt (Real.cosh_pos _).le]
  simp

/-- Combining the actual Jacobian and field weight converts the native scalar mass density to Y⁻². -/
theorem chart_weighted_mass_density (p : Point3) (hp : 0 < p 2) :
    ‖weight p‖^(2 : ℕ)/((p 2)^(2 : ℕ)*
      Matrix.det (fun j i : Fin 3 => fderiv ℝ chart p (Pi.single i 1) j)) =
      1/(chart p 1)^(2 : ℕ) := by
  have hy := ne_of_gt hp
  have ha := ne_of_gt (warp_pos (p 0))
  rw [weight_norm_sq p hp,chart_jacobian]
  dsimp [chart]
  field_simp

end
end RHTower.D4BMJointConformal
