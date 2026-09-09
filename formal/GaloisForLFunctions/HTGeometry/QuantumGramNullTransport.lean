import GaloisForLFunctions.HTGeometry.QuantumNullSpaceTransport
import GaloisForLFunctions.HTGeometry.KoplienkoSecondOrderGram

/-!
# Moving quantum information and second-order Gram remainder

The Gram representation of the quantum geometric tensor in
arXiv:2609.07645, Appendix D, identifies physically invisible directions
with the kernel of the observation operator. Under a changing operator,
the corpus's Koplienko remainder records exactly the squared perturbation
response. Common quantum-information kernels are therefore determined by
the old observation and its increment, with no fixed-rank assumption.
-/

open scoped InnerProductSpace
noncomputable section
namespace HTGeometry

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Exact quadratic observation charge of the existing Koplienko remainder. -/
theorem quantum_gram_remainder_expectation (P R : E →L[ℂ] F) (r : ℝ) (x : E) :
    (inner ℂ x (gramSecondOrderRemainder P R (r : ℂ) x)).re = r ^ 2 * ‖R x‖ ^ 2 := by
  rw [gramSecondOrderRemainder_eq_residualEnergy]
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right, Complex.star_def, Complex.conj_ofReal,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  have hi := inner_self_eq_norm_sq (𝕜 := ℂ) (R x)
  simp only [RCLike.re_to_complex] at hi
  rw [hi]
  ring


/-- Nonnegativity of the quadratic information increment holds for every operator and vector. -/
theorem quantum_gram_remainder_nonnegative (P R : E →L[ℂ] F) (r : ℝ) (x : E) :
    0 ≤ (inner ℂ x (gramSecondOrderRemainder P R (r : ℂ) x)).re := by
  rw [quantum_gram_remainder_expectation]
  positivity

/-- The second-order charge vanishes exactly at zero step or an invisible increment. -/
theorem quantum_gram_remainder_zero_iff (P R : E →L[ℂ] F) (r : ℝ) (x : E) :
    (inner ℂ x (gramSecondOrderRemainder P R (r : ℂ) x)).re = 0 ↔ r = 0 ∨ R x = 0 := by
  rw [quantum_gram_remainder_expectation]
  simp

/-- Common QGT null directions are old null directions annihilated by the operator increment. -/
theorem quantum_gram_common_kernel (A B : E →L[ℂ] F) :
    (ContinuousLinearMap.adjoint A ∘L A).ker ⊓
      (ContinuousLinearMap.adjoint B ∘L B).ker =
    (ContinuousLinearMap.adjoint A ∘L A).ker ⊓
      (ContinuousLinearMap.adjoint (B - A) ∘L (B - A)).ker := by
  rw [ContinuousLinearMap.ker_adjoint_comp_self,
    ContinuousLinearMap.ker_adjoint_comp_self, ContinuousLinearMap.ker_adjoint_comp_self]
  exact observation_common_kernel A.toLinearMap B.toLinearMap

omit [CompleteSpace E] [CompleteSpace F] in
/-- A uniform perturbation bound for every vector, including approximately invisible vectors. -/
theorem quantum_observation_drift_bound (A B : E →L[ℂ] F) (x : E) :
    ‖B x‖ ≤ ‖A x‖ + ‖B - A‖ * ‖x‖ := by
  calc
    ‖B x‖ = ‖A x + (B - A) x‖ := by simp
    _ ≤ ‖A x‖ + ‖(B - A) x‖ := norm_add_le _ _
    _ ≤ ‖A x‖ + ‖B - A‖ * ‖x‖ := add_le_add le_rfl ((B - A).le_opNorm x)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The observed norm changes by at most the operator increment times parameter size. -/
theorem quantum_observation_norm_change (A B : E →L[ℂ] F) (x : E) :
    |‖B x‖ - ‖A x‖| ≤ ‖B - A‖ * ‖x‖ := by
  calc
    |‖B x‖ - ‖A x‖| ≤ ‖B x - A x‖ := abs_norm_sub_norm_le _ _
    _ ≤ ‖B - A‖ * ‖x‖ := (B - A).le_opNorm x

end HTGeometry
