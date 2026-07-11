import GaloisForLFunctions.EllipticThetaLogComparisonRigidity

/-!
# Additive elliptic-gamma logarithmic kernel and the theta-defect bridge

The normally convergent double-product kernel is pulled back to additive coordinates. Its two
nome increments become the two theta faces. After the constraint-and-divisor comparison theorem,
every mixed translated increment is exactly the analytic Jacobi-theta logarithmic-derivative
defect used by the unconditional orbit obstruction.
-/

open Complex

namespace GaloisForLFunctions

noncomputable section

/-- Adding an arbitrary additive parameter multiplies the aligned coordinate by its nome. -/
theorem ellipticThetaCoordinate_add (σ τ z : ℂ) :
    ellipticThetaCoordinate τ (z + σ) =
      ellipticNome σ * ellipticThetaCoordinate τ z := by
  rw [ellipticThetaCoordinate, ellipticThetaCoordinate, ellipticNome]
  rw [mul_add, Complex.exp_add]
  ring

/-- The two theta coordinate conventions differ by the half-difference of their parameters. -/
theorem ellipticThetaCoordinate_recenter (σ τ z : ℂ) :
    ellipticThetaCoordinate σ (z + (τ - σ) / 2) =
      ellipticThetaCoordinate τ z := by
  rw [ellipticThetaCoordinate, ellipticThetaCoordinate]
  rw [show 2 * Real.pi * I * (z + (τ - σ) / 2) =
      2 * Real.pi * I * z + Real.pi * I * (τ - σ) by ring,
    Complex.exp_add]
  have hexp : Complex.exp (Real.pi * I * σ) *
      Complex.exp (Real.pi * I * (τ - σ)) =
      Complex.exp (Real.pi * I * τ) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    -Complex.exp (Real.pi * I * σ) *
          (Complex.exp (2 * Real.pi * I * z) *
            Complex.exp (Real.pi * I * (τ - σ))) =
        -(Complex.exp (Real.pi * I * σ) *
          Complex.exp (Real.pi * I * (τ - σ))) *
            Complex.exp (2 * Real.pi * I * z) := by ring
    _ = -Complex.exp (Real.pi * I * τ) * Complex.exp (2 * Real.pi * I * z) := by
      rw [hexp]

/-- Additive pullback of the normally convergent elliptic-gamma logarithmic double kernel. -/
def ellipticGammaAdditiveLogKernel (σ τ z : ℂ) : ℂ :=
  2 * Real.pi * I * ellipticGammaLogKernel
    (ellipticNome σ) (ellipticNome τ) (ellipticThetaCoordinate τ z)

/-- The first additive elliptic-gamma hierarchy equation has the `τ`-theta boundary. -/
theorem ellipticGammaAdditiveLogKernel_add_sigma_sub
    {σ τ z : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    ellipticGammaAdditiveLogKernel σ τ (z + σ) -
        ellipticGammaAdditiveLogKernel σ τ z =
      ellipticThetaAdditiveLogKernel τ z := by
  rw [ellipticGammaAdditiveLogKernel, ellipticGammaAdditiveLogKernel,
    ellipticThetaCoordinate_add]
  rw [← mul_sub]
  rw [ellipticGammaLogKernel_mul_p_sub
    (ellipticNome_ne_zero σ) (ellipticThetaCoordinate_ne_zero τ z)
      (norm_ellipticNome_lt_one hσ) (norm_ellipticNome_lt_one hτ)]
  rfl

/-- The polarized second hierarchy equation has the recentered `σ`-theta boundary. -/
theorem ellipticGammaAdditiveLogKernel_add_tau_sub
    {σ τ z : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    ellipticGammaAdditiveLogKernel σ τ (z + τ) -
        ellipticGammaAdditiveLogKernel σ τ z =
      ellipticThetaAdditiveLogKernel σ (z + (τ - σ) / 2) := by
  rw [ellipticGammaAdditiveLogKernel, ellipticGammaAdditiveLogKernel,
    ellipticThetaCoordinate_add]
  rw [← mul_sub]
  rw [ellipticGammaLogKernel_mul_q_sub
    (ellipticNome_ne_zero τ) (ellipticThetaCoordinate_ne_zero τ z)
      (norm_ellipticNome_lt_one hσ) (norm_ellipticNome_lt_one hτ)]
  rw [ellipticThetaAdditiveLogKernel, ellipticThetaCoordinate_recenter]

/-- The mixed external-translation/`σ` face of the actual double-product kernel is exactly the
analytic theta logarithmic-derivative defect. -/
theorem ellipticGammaAdditiveLogKernel_mixed_defect_sigma
    {σ τ h z : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im)
    (hz : jacobiTheta₂ z τ ≠ 0) (hzh : jacobiTheta₂ (z + h) τ ≠ 0) :
    (ellipticGammaAdditiveLogKernel σ τ (z + h + σ) -
        ellipticGammaAdditiveLogKernel σ τ (z + h)) -
      (ellipticGammaAdditiveLogKernel σ τ (z + σ) -
        ellipticGammaAdditiveLogKernel σ τ z) =
      thetaLogDeriv (z + h) τ - thetaLogDeriv z τ := by
  rw [ellipticGammaAdditiveLogKernel_add_sigma_sub hσ hτ,
    ellipticGammaAdditiveLogKernel_add_sigma_sub hσ hτ]
  exact ellipticThetaAdditiveLogKernel_defect_eq_thetaLogDerivDefect hτ hz hzh

end

end GaloisForLFunctions
