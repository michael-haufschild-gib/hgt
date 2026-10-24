import GaloisForLFunctions.ArithmeticDefectRigidity.CountableCofactorCovariancesHaveACommonLimit
import GaloisForLFunctions.HTGeometry.AntipodalKernelExtension
import GaloisForLFunctions.HTGeometry.RealPositiveKernelComplexification

/-!
# White noise survives the cofactor Gram and antipodal constraints

The diagonal kernel `K(j,k) = 1_{j=k}/j` has unit receiver mass, the sharp
cofactor radius, positive packet energies and exact dilation scaling. Its
antipodal positive extension exists and is unique. These properties alone
therefore do not encode the source-defined moving cofactor relation.
-/

open Finset

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The diagonal cofactor kernel with the sharp pronic dilation weight. -/
def whiteNoiseKernel (j k : ℕ+) : ℝ := if j = k then 1 / (j : ℝ) else 0

theorem whiteNoiseKernel_one_one : whiteNoiseKernel 1 1 = 1 := by
  simp [whiteNoiseKernel]

theorem whiteNoiseKernel_symm (j k : ℕ+) :
    whiteNoiseKernel j k = whiteNoiseKernel k j := by
  by_cases h : j = k
  · subst k
    rfl
  · simp [whiteNoiseKernel, h, Ne.symm h]

/-- White noise attains the radius on the diagonal and vanishes elsewhere. -/
theorem abs_whiteNoiseKernel_le (j k : ℕ+) :
    |whiteNoiseKernel j k| ≤ cofactorGramRadius j k := by
  by_cases h : j = k
  · subst k
    have hj : (0 : ℝ) < j := by exact_mod_cast j.property
    simp only [whiteNoiseKernel, if_pos rfl, abs_of_pos (one_div_pos.mpr hj),
      cofactorGramRadius]
    rw [← sq, div_pow, one_pow, Real.sq_sqrt hj.le]
  · simp only [whiteNoiseKernel, if_neg h, abs_zero, cofactorGramRadius]
    positivity

/-- Every finite white-noise energy is the weighted sum of coefficient squares. -/
theorem whiteNoiseKernel_quadratic_eq (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    (∑ j ∈ S, ∑ k ∈ S, c j * c k * whiteNoiseKernel j k) =
      ∑ j ∈ S, c j ^ 2 / (j : ℝ) := by
  apply sum_congr rfl
  intro j hj
  simp only [whiteNoiseKernel, mul_ite, mul_zero]
  rw [sum_ite_eq, if_pos hj]
  ring

theorem whiteNoiseKernel_quadratic_nonneg (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    0 ≤ ∑ j ∈ S, ∑ k ∈ S, c j * c k * whiteNoiseKernel j k := by
  rw [whiteNoiseKernel_quadratic_eq]
  exact sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (by positivity)

/-- Integer dilation has exactly the self-similarity factor allowed by the receiver. -/
theorem whiteNoiseKernel_dilation (p j k : ℕ+) :
    whiteNoiseKernel (p * j) (p * k) = (1 / (p : ℝ)) * whiteNoiseKernel j k := by
  by_cases h : j = k
  · subst k
    simp only [whiteNoiseKernel, if_pos rfl, PNat.mul_coe, Nat.cast_mul]
    simp [one_div, mul_inv_rev, mul_comm]
  · have hmul : p * j ≠ p * k := fun he => h (mul_left_cancel he)
    simp only [whiteNoiseKernel, if_neg hmul, if_neg h, mul_zero]

/-- Dilation contracts every packet with equality, including all signed mixed terms. -/
theorem whiteNoiseKernel_packet_dilation (p : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    (∑ j ∈ S, ∑ k ∈ S, c j * c k * whiteNoiseKernel (p * j) (p * k)) =
      (1 / (p : ℝ)) * (∑ j ∈ S, ∑ k ∈ S, c j * c k * whiteNoiseKernel j k) := by
  simp_rw [whiteNoiseKernel_dilation]
  simp only [mul_sum]
  exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring

/-- The complexification of white noise is a positive kernel. -/
theorem isPSDKernel_whiteNoise :
    HTGeometry.IsPSDKernel (fun j k => (whiteNoiseKernel j k : ℂ)) :=
  HTGeometry.isPSDKernel_of_real_packet_nonneg whiteNoiseKernel
    whiteNoiseKernel_symm whiteNoiseKernel_quadratic_nonneg

/-- White noise has a unique positive antipodal residual with unit mass. Hence
antipodality by itself cannot exclude the diagonal cofactor state. -/
theorem whiteNoise_has_unique_antipodal_extension :
    ∃! J : Option ℕ+ → Option ℕ+ → ℂ,
      HTGeometry.IsPSDKernel J ∧
        (∀ j k, J (some j) (some k) = (whiteNoiseKernel j k : ℂ)) ∧
        J none none = 1 ∧ J none (some 1) = -1 := by
  simpa only [whiteNoiseKernel_one_one, Complex.ofReal_one] using
    HTGeometry.existsUnique_antipodalKernelExtension isPSDKernel_whiteNoise 1

end GaloisForLFunctions.ArithmeticDefectRigidity
