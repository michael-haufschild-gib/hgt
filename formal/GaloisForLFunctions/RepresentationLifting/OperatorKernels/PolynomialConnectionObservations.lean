import GaloisForLFunctions.RepresentationLifting.OperatorKernels.CompositionCokernel
import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionIndex

/-!
# Linear observations of polynomial connections

For `T_A(P) = P' - A P`, observations modulo those factoring through `T_A`
have dimension `dim W` if `A = 0`, and zero otherwise. The source polynomial
space is infinite-dimensional: finite-dimensionality of the kernel suffices.
In the differentiation case the sole obstruction is the observation of `1`.
-/

noncomputable section

open Polynomial

namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels

open GaloisForLFunctions.HTGeometry

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Kernel amplification remains exact for these infinite-dimensional source spaces. -/
theorem polynomialConnection_observation_defect [FiniteDimensional ℝ W] (A : ℝ[X]) :
    Module.finrank ℝ ((ℝ[X] →ₗ[ℝ] W) ⧸
      (precompose (W := W) (gomesPolynomialFirstOrderLinearMap A)).range) =
      if A = 0 then Module.finrank ℝ W else 0 := by
  rw [(compositionCokernelEquiv (W := W) (gomesPolynomialFirstOrderLinearMap A)).finrank_eq,
    Module.finrank_linearMap, gomesPolynomialFirstOrderLinearMap_kernel_finrank]
  split_ifs <;> simp

/-- Every algebraic observation factors except for its constant reading under differentiation. -/
theorem polynomialConnection_observation_factors_iff (A : ℝ[X]) (f : ℝ[X] →ₗ[ℝ] W) :
    (∃ g : ℝ[X] →ₗ[ℝ] W, g.comp (gomesPolynomialFirstOrderLinearMap A) = f) ↔
      A ≠ 0 ∨ f 1 = 0 := by
  change f ∈ (precompose (gomesPolynomialFirstOrderLinearMap A)).range ↔ _
  rw [range_precompose]
  by_cases ha : A = 0
  · subst A
    simp only [ne_eq, not_true_eq_false, false_or]
    constructor
    · intro h
      have h1 : (1 : ℝ[X]) ∈ (gomesPolynomialFirstOrderLinearMap 0).ker := by
        change gomesPolynomialFirstOrderOperator 0 1 = 0
        simp [gomesPolynomialFirstOrderOperator]
      exact LinearMap.congr_fun h ⟨1, h1⟩
    · intro h
      apply LinearMap.ext
      intro v
      have hd : v.val.derivative = 0 := by
        have hv := v.property
        change gomesPolynomialFirstOrderOperator 0 v.val = 0 at hv
        simpa only [gomesPolynomialFirstOrderOperator, zero_mul, sub_zero] using hv
      have hc : v.val = C (v.val.coeff 0) :=
        eq_C_of_natDegree_eq_zero (derivative_eq_zero.mp hd)
      change f v.val = 0
      rw [hc, show C (v.val.coeff 0) = v.val.coeff 0 • (1 : ℝ[X]) by
          rw [smul_eq_C_mul, mul_one],
        map_smul, h, smul_zero]
  · simp only [ha, ne_eq, not_false_eq_true, true_or, iff_true]
    apply LinearMap.ext
    intro v
    have hv : v.val = 0 :=
      ((gomesPolynomialFirstOrderOperator_injective_iff A).mpr ha)
        (v.property.trans (map_zero (gomesPolynomialFirstOrderLinearMap A)).symm)
    change f v.val = 0
    rw [hv, map_zero]

end GaloisForLFunctions.RepresentationLifting.OperatorKernels

#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.polynomialConnection_observation_defect
#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.polynomialConnection_observation_factors_iff
