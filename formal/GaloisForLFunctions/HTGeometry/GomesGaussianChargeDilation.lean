import GaloisForLFunctions.HTGeometry.GomesGaussianChargeLadderGeometry

/-!
# Coordinate transport of the common Gaussian charge connection

Positive coordinate dilation transports the corpus's unit Gaussian operators to every
positive effective charge. Both first-order factors scale by the square root of the
charge, their Hamiltonian scales by the charge, and the bilinear pairing has the inverse
Jacobian factor. These closed transport laws support the tensor-charge spectral experiment.
-/

noncomputable section
open MeasureTheory
open scoped SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- Positive square-root dilation on the real base. -/
def gomesGaussianChargeCoordinate (a : Set.Ioi (0 : ℝ)) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 (Real.sqrt a.val) (ne_of_gt (Real.sqrt_pos.mpr a.property)))

/-- Pullback of complex Schwartz states by the charge coordinate. -/
def gomesGaussianChargeDilation (a : Set.Ioi (0 : ℝ)) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (gomesGaussianChargeCoordinate a)

/-- The inverse coordinate pullback on the same Schwartz domain. -/
def gomesGaussianChargeUndilation (a : Set.Ioi (0 : ℝ)) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (gomesGaussianChargeCoordinate a).symm

/-- Dilation is literal composition with multiplication by the square root of the charge. -/
theorem gomesGaussianChargeDilation_apply (a : Set.Ioi (0 : ℝ)) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    gomesGaussianChargeDilation a ψ x = ψ (Real.sqrt a.val * x) := rfl

/-- Coordinate transport followed by its inverse recovers every state. -/
theorem gomesGaussianChargeDilation_left_inverse (a : Set.Ioi (0 : ℝ)) (ψ : 𝓢(ℝ, ℂ)) :
    gomesGaussianChargeUndilation a (gomesGaussianChargeDilation a ψ) = ψ := by
  ext x
  change ψ (gomesGaussianChargeCoordinate a ((gomesGaussianChargeCoordinate a).symm x)) = ψ x
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- Inverse transport followed by dilation also recovers every state. -/
theorem gomesGaussianChargeDilation_right_inverse (a : Set.Ioi (0 : ℝ)) (ψ : 𝓢(ℝ, ℂ)) :
    gomesGaussianChargeDilation a (gomesGaussianChargeUndilation a ψ) = ψ := by
  ext x
  change ψ ((gomesGaussianChargeCoordinate a).symm (gomesGaussianChargeCoordinate a x)) = ψ x
  rw [ContinuousLinearEquiv.symm_apply_apply]

/-- The derivative transforms by the exact coordinate scale. -/
theorem gomesGaussianChargeDilation_deriv (a : Set.Ioi (0 : ℝ)) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deriv (gomesGaussianChargeDilation a ψ) x =
      (Real.sqrt a.val : ℂ) * deriv ψ (Real.sqrt a.val * x) := by
  have h := (ψ.hasDerivAt (Real.sqrt a.val * x)).scomp x ((hasDerivAt_id x).const_mul (Real.sqrt a.val))
  change deriv (fun y => ψ (Real.sqrt a.val * y)) x = _
  simpa only [Function.comp_def, mul_one, Complex.real_smul] using h.deriv

/-- The charged creation operator is the dilated unit creation operator times the coordinate scale. -/
theorem gomesGaussianChargeDilation_creation (a : Set.Ioi (0 : ℝ)) (ψ : 𝓢(ℝ, ℂ)) :
    dilatonAdjointChargeCLM (gomesGaussianLogWeight a.val) (gomesGaussianChargeDilation a ψ) =
      (Real.sqrt a.val : ℂ) • gomesGaussianChargeDilation a (creationCLM ψ) := by
  ext x
  simp only [gomesGaussianAdjointCharge_apply, gomesGaussianChargeDilation_deriv,
    gomesGaussianChargeDilation_apply, smul_apply, smul_eq_mul, creationCLM_apply, Complex.ofReal_mul]
  have hs : (Real.sqrt a.val : ℂ) ^ 2 = (a.val : ℂ) := by
    exact_mod_cast Real.sq_sqrt a.property.le
  linear_combination -(2 * (Real.pi : ℂ) * x * ψ (Real.sqrt a.val * x)) * hs

/-- The same coordinate scale transports the lowering operator. -/
theorem gomesGaussianChargeDilation_annihilation (a : Set.Ioi (0 : ℝ)) (ψ : 𝓢(ℝ, ℂ)) :
    dilatonSuperchargeCLM (gomesGaussianLogWeight a.val) (gomesGaussianChargeDilation a ψ) =
      (Real.sqrt a.val : ℂ) • gomesGaussianChargeDilation a (annihilationCLM ψ) := by
  ext x
  simp only [gomesGaussianSupercharge_apply, gomesGaussianChargeDilation_deriv,
    gomesGaussianChargeDilation_apply, smul_apply, smul_eq_mul, annihilationCLM_apply, Complex.ofReal_mul]
  have hs : (Real.sqrt a.val : ℂ) ^ 2 = (a.val : ℂ) := by
    exact_mod_cast Real.sq_sqrt a.property.le
  linear_combination -(2 * (Real.pi : ℂ) * x * ψ (Real.sqrt a.val * x)) * hs

/-- The factorized Hamiltonian is the unit number operator multiplied by the charge after transport. -/
theorem gomesGaussianChargeDilation_hamiltonian (a : Set.Ioi (0 : ℝ)) (ψ : 𝓢(ℝ, ℂ)) :
    dilatonHamiltonianCLM (gomesGaussianLogWeight a.val) (gomesGaussianChargeDilation a ψ) =
      (a.val : ℂ) • gomesGaussianChargeDilation a (numberCLM ψ) := by
  rw [dilatonHamiltonianCLM, ContinuousLinearMap.comp_apply, gomesGaussianChargeDilation_annihilation,
    map_smul, gomesGaussianChargeDilation_creation, smul_smul]
  have hs : (Real.sqrt a.val : ℂ) * Real.sqrt a.val = (a.val : ℂ) := by
    exact_mod_cast (show Real.sqrt a.val * Real.sqrt a.val = a.val by
      rw [← pow_two, Real.sq_sqrt a.property.le])
  rw [hs]
  rfl

/-- Dilation carries the standard Gaussian to the charged ground state with its fixed normalization. -/
theorem gomesGaussianChargeDilation_ground (a : Set.Ioi (0 : ℝ)) :
    gomesGaussianChargeDilation a gaussianSchwartz = gomesGaussianChargeGroundState a := by
  ext x
  rw [gomesGaussianChargeDilation_apply, gaussianSchwartz_apply, gomesGaussianChargeGroundState_apply]
  unfold gaussReal
  rw [mul_pow, Real.sq_sqrt a.property.le]
  congr 2
  ring

/-- The actual Schwartz pairing transforms with the inverse coordinate Jacobian. -/
theorem gomesGaussianChargeDilation_pair (a : Set.Ioi (0 : ℝ)) (f g : 𝓢(ℝ, ℂ)) :
    schwartzPair (gomesGaussianChargeDilation a f) (gomesGaussianChargeDilation a g) =
      ((Real.sqrt a.val)⁻¹ : ℝ) • schwartzPair f g := by
  simp only [schwartzPair_eq_integral, gomesGaussianChargeDilation_apply]
  have h := Measure.integral_comp_mul_left (fun x : ℝ => f x * g x) (Real.sqrt a.val)
  rw [abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr a.property))] at h
  exact h

end GaloisForLFunctions.HTGeometry
