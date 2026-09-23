import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAKernel

/-!
# The positive coexistence integral is exactly the entropy logarithm

Build the missing logarithmic integral identity needed for model A of
arXiv:2609.00025. An explicit primitive is differentiated on the actual
integration interval. The resulting cubic identity removes all logarithmic
quotients from the algebraic coexistence balance equation.
-/
noncomputable section
open Real Set
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbCoexistenceAKernelPrimitive (τ u : ℝ) : ℝ :=
  (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) / (2 * egbCoexistenceASymmetricRatio τ ^ (3 : ℕ)) *
    (log (1 + egbCoexistenceASymmetricRatio τ * u) - log (1 - egbCoexistenceASymmetricRatio τ * u)) -
      u / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)

theorem egbCoexistenceASymmetricRatio_log_identity (τ : ℝ) :
    log (1 + egbCoexistenceASymmetricRatio τ) - log (1 - egbCoexistenceASymmetricRatio τ) = -log (thermalRatio τ) := by
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  have hp : 0 < 1 + egbCoexistenceASymmetricRatio τ := by linarith
  have hm : 0 < 1 - egbCoexistenceASymmetricRatio τ := by linarith
  have hz := thermalRatio_pos τ
  have hr : (1 + egbCoexistenceASymmetricRatio τ) / (1 - egbCoexistenceASymmetricRatio τ) = 1 / thermalRatio τ := by
    apply (div_eq_div_iff hm.ne' hz.ne').2
    unfold egbCoexistenceASymmetricRatio
    field_simp
    ring
  rw [← log_div hp.ne' hm.ne', hr, one_div, log_inv]

/-- Fundamental theorem of calculus with the derivative proved throughout the interval. -/
theorem egbCoexistenceAKernel_primitive_integral (τ : ℝ) :
    (∫ u in (0 : ℝ)..1, egbCoexistenceAKernelIntegrand τ u) =
      egbCoexistenceAKernelPrimitive τ 1 - egbCoexistenceAKernelPrimitive τ 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (egbCoexistenceAKernelIntegrand_intervalIntegrable τ)
  intro u hu
  have huI : u ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  have hp : 0 < 1 + egbCoexistenceASymmetricRatio τ * u := by
    have hu₀ := huI.1
    have hd₀ := hd.1
    positivity
  have hm : 0 < 1 - egbCoexistenceASymmetricRatio τ * u := by
    nlinarith [mul_nonneg (le_of_lt hd.1) (sub_nonneg.mpr huI.2)]
  have hD : 1 - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * u ^ (2 : ℕ) ≠ 0 := by
    have hprod := mul_pos hm hp
    apply ne_of_gt
    nlinarith
  have hi := hasDerivAt_id u
  have hplus := ((hi.const_mul (egbCoexistenceASymmetricRatio τ)).const_add 1).log hp.ne'
  have hminus := ((hi.const_mul (egbCoexistenceASymmetricRatio τ)).const_sub 1).log hm.ne'
  have h := ((hplus.sub hminus).const_mul
    ((1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) / (2 * egbCoexistenceASymmetricRatio τ ^ (3 : ℕ)))).sub
      (hi.div_const (egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)))
  apply h.congr_deriv
  unfold egbCoexistenceAKernelIntegrand
  norm_num only [id_eq]
  have hd₀ := hd.1
  field_simp
  ring

theorem egbCoexistenceAKernel_log_integral (τ : ℝ) :
    (∫ u in (0 : ℝ)..1, egbCoexistenceAKernelIntegrand τ u) =
      (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) / (2 * egbCoexistenceASymmetricRatio τ ^ (3 : ℕ)) *
        (-log (thermalRatio τ)) - 1 / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) := by
  rw [egbCoexistenceAKernel_primitive_integral]
  unfold egbCoexistenceAKernelPrimitive
  simp only [mul_one, mul_zero, add_zero, sub_zero, log_one, zero_div, sub_self]
  rw [egbCoexistenceASymmetricRatio_log_identity]

/-- Polynomial-times-log identity used directly by the equal-Gibbs proof. -/
theorem egbCoexistenceALogKernel_cubic_identity (τ : ℝ) :
    (thermalRatio τ - 1) ^ (3 : ℕ) * egbCoexistenceALogKernel τ =
      3 * (thermalRatio τ + 1) * (thermalRatio τ ^ (2 : ℕ) + 1) * log (thermalRatio τ) -
        4 * (thermalRatio τ ^ (2 : ℕ) + thermalRatio τ + 1) * (thermalRatio τ - 1) := by
  unfold egbCoexistenceALogKernel
  rw [egbCoexistenceAKernel_log_integral]
  unfold egbCoexistenceASymmetricRatio
  have hz := thermalRatio_pos τ
  have hzu := thermalRatio_lt_one τ
  have hn : 1 - thermalRatio τ ≠ 0 := by linarith
  have hn' : thermalRatio τ - 1 ≠ 0 := by linarith
  field_simp
  ring

theorem egbCoexistenceALogKernel_logarithmic_formula (τ : ℝ) :
    egbCoexistenceALogKernel τ =
      (3 * (thermalRatio τ + 1) * (thermalRatio τ ^ (2 : ℕ) + 1) * (log (thermalRatio τ) / (thermalRatio τ - 1)) -
        4 * (thermalRatio τ ^ (2 : ℕ) + thermalRatio τ + 1)) / (thermalRatio τ - 1) ^ (2 : ℕ) := by
  have h := egbCoexistenceALogKernel_cubic_identity τ
  have hn : thermalRatio τ - 1 ≠ 0 := by linarith [thermalRatio_lt_one τ]
  field_simp
  nlinarith [h]

end GaloisForLFunctions.HTGeometry
