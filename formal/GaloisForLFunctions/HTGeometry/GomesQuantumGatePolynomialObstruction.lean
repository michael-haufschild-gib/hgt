import GaloisForLFunctions.HTGeometry.GomesComplexPolynomialGaugeRigidity
import GaloisForLFunctions.QuantumAlg.Core.Components.Gates

/-!
# Exact polynomial-parameter obstructions for the actual quantum gates

Applying the compact-target rigidity mechanism of arXiv:2607.24901v1 to the
corpus's unitary rotation and phase gates rules out exact polynomial entries
on the full real parameter axis. The positive classification is supplied by
`unitary_family_polynomial_iff_constant`. This says nothing against bounded-domain
approximation or the existing trigonometric and exponential gate formulas.
-/

noncomputable section
namespace QuantumAlg
open GaloisForLFunctions.HTGeometry

/-- The processing Z rotation admits no exact global polynomial parameterization. -/
theorem rotZOp_no_polynomial_parameter :
    ¬ ∃ P : Matrix (Fin 2) (Fin 2) (Polynomial ℂ), ∀ x : ℝ,
      (fun i j => (P i j).eval (x : ℂ)) = rotZOp x := by
  rintro ⟨P,hP⟩
  let U : ℝ → Matrix.unitaryGroup (Fin 2) ℂ := fun x => ⟨rotZOp x,rotZOp_mem_unitaryGroup x⟩
  have hc := (unitary_family_polynomial_iff_constant U).mp ⟨P,hP⟩
  have hh := congrArg (fun A : Matrix.unitaryGroup (Fin 2) ℂ => (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0) (hc Real.pi)
  have hr := congrArg Complex.re hh
  simp [U,rotZOp,Complex.exp_pi_mul_I] at hr
  linarith

/-- The standard Y rotation admits no exact global polynomial parameterization. -/
theorem rotYOp_no_polynomial_parameter :
    ¬ ∃ P : Matrix (Fin 2) (Fin 2) (Polynomial ℂ), ∀ x : ℝ,
      (fun i j => (P i j).eval (x : ℂ)) = rotYOp x := by
  rintro ⟨P,hP⟩
  let U : ℝ → Matrix.unitaryGroup (Fin 2) ℂ := fun x => ⟨rotYOp x,rotYOp_mem_unitaryGroup x⟩
  have hc := (unitary_family_polynomial_iff_constant U).mp ⟨P,hP⟩
  have hh := congrArg (fun A : Matrix.unitaryGroup (Fin 2) ℂ => (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0) (hc Real.pi)
  have hr := congrArg Complex.re hh
  simp [U,rotYOp,Real.cos_pi_div_two] at hr

/-- The one-branch phase gate admits no exact global polynomial parameterization. -/
theorem phaseGateOp_no_polynomial_parameter :
    ¬ ∃ P : Matrix (Fin 2) (Fin 2) (Polynomial ℂ), ∀ x : ℝ,
      (fun i j => (P i j).eval (x : ℂ)) = phaseGateOp x := by
  rintro ⟨P,hP⟩
  let U : ℝ → Matrix.unitaryGroup (Fin 2) ℂ := fun x => ⟨phaseGateOp x,phaseGateOp_mem_unitaryGroup x⟩
  have hc := (unitary_family_polynomial_iff_constant U).mp ⟨P,hP⟩
  have hh := congrArg (fun A : Matrix.unitaryGroup (Fin 2) ℂ => (A : Matrix (Fin 2) (Fin 2) ℂ) 1 1) (hc Real.pi)
  have hr := congrArg Complex.re hh
  simp [U,phaseGateOp,Complex.exp_pi_mul_I] at hr
  linarith

/-- The zero-branch phase gate admits no exact global polynomial parameterization. -/
theorem phaseGateOnZeroOp_no_polynomial_parameter :
    ¬ ∃ P : Matrix (Fin 2) (Fin 2) (Polynomial ℂ), ∀ x : ℝ,
      (fun i j => (P i j).eval (x : ℂ)) = phaseGateOnZeroOp x := by
  rintro ⟨P,hP⟩
  let U : ℝ → Matrix.unitaryGroup (Fin 2) ℂ := fun x => ⟨phaseGateOnZeroOp x,phaseGateOnZeroOp_mem_unitaryGroup x⟩
  have hc := (unitary_family_polynomial_iff_constant U).mp ⟨P,hP⟩
  have hh := congrArg (fun A : Matrix.unitaryGroup (Fin 2) ℂ => (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0) (hc Real.pi)
  have hr := congrArg Complex.re hh
  simp [U,phaseGateOnZeroOp,Complex.exp_pi_mul_I] at hr
  linarith

end QuantumAlg
