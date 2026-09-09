import GaloisForLFunctions.HTGeometry.ConservativeDissipativeOperator
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Spectral localization of constructed conservative–dissipative operators

Applications of the operator split in Schaffer–Exl, arXiv:2609.04530.
-/

open scoped InnerProductSpace
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [FiniteDimensional ℂ E]


/-- Proposition 3(i): the constructed conservative spectrum is imaginary. -/
theorem conservative_spectrum (A : E →L[ℂ] E) :
    spectrum ℂ (conservative A : E →ₗ[ℂ] E) ⊆ {z : ℂ | z.re = 0} := by
  intro z hz
  obtain ⟨x, hx⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz).exists_hasEigenvector
  have hp := conservative_power A x
  have he : conservative A x = z • x := hx.apply_eq_smul
  rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K] at hp
  have hp' : z.re * ‖x‖ ^ 2 = 0 := by simpa [pow_two] using hp
  exact (mul_eq_zero.mp hp').resolve_right (ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hx.2)))

/-- Proposition 3(ii): the damping spectrum is real and nonnegative. -/
theorem damping_spectrum (B : E →L[ℂ] F) :
    spectrum ℂ (damping B : E →ₗ[ℂ] E) ⊆ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} := by
  intro z hz
  obtain ⟨x, hx⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz).exists_hasEigenvector
  have he : damping B x = z • x := hx.apply_eq_smul
  have hp : ⟪x, damping B x⟫_ℂ = (‖B x‖ : ℂ) ^ 2 := by
    simp [damping, ContinuousLinearMap.adjoint_inner_right]
  rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K] at hp
  have hr : z.re * ‖x‖ ^ 2 = ‖B x‖ ^ 2 := by simpa [pow_two] using congrArg Complex.re hp
  have hi : z.im * ‖x‖ ^ 2 = 0 := by simpa [pow_two] using congrArg Complex.im hp
  have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx.2)
  refine ⟨(mul_eq_zero.mp hi).resolve_right (ne_of_gt hn), ?_⟩
  exact nonneg_of_mul_nonneg_left (hr.symm ▸ sq_nonneg ‖B x‖) hn

/-- Proposition 3(iii): every generator eigenvalue lies in the closed left half-plane. -/
theorem generator_spectrum (A : E →L[ℂ] E) (B : E →L[ℂ] F) :
    spectrum ℂ (generator A B : E →ₗ[ℂ] E) ⊆ {z : ℂ | z.re ≤ 0} := by
  intro z hz
  obtain ⟨x, hx⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz).exists_hasEigenvector
  have hp := generator_power_nonpos A B x
  have he : generator A B x = z • x := hx.apply_eq_smul
  rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K] at hp
  have hp' : z.re * ‖x‖ ^ 2 ≤ 0 := by simpa [pow_two] using hp
  exact nonpos_of_mul_nonpos_left hp' (sq_pos_of_pos (norm_pos_iff.mpr hx.2))

/-- Unit damping opens a uniform spectral gap, independent of the conservative operator. -/
theorem regularized_spectrum (A : E →L[ℂ] E) (B : E →L[ℂ] F) :
    spectrum ℂ (regularized A B : E →ₗ[ℂ] E) ⊆ {z : ℂ | z.re ≤ -1} := by
  intro z hz
  obtain ⟨x, hx⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz).exists_hasEigenvector
  have hp := regularized_power A B x
  have he : regularized A B x = z • x := hx.apply_eq_smul
  rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K] at hp
  have hp' : z.re * ‖x‖ ^ 2 = -‖B x‖ ^ 2 - ‖x‖ ^ 2 := by simpa [pow_two] using hp
  have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx.2)
  have h : (z.re + 1) * ‖x‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖B x‖]
  have := nonpos_of_mul_nonpos_left h hn
  change z.re ≤ -1
  linarith

end
end GaloisForLFunctions.HTGeometry.SchafferExl
