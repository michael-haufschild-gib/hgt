import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Finite.Comparison

/-! # Products of positive probability weights and uniform-to-law KL -/

namespace GaloisForLFunctions.HTGeometry.FourierLLogL.Law

open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- On the support-domination domain, the finite-law KL cost detects equality. -/
theorem kl_eq_zero_iff_of_dominated {P Q : Law α} (hdom : P.dominated Q) :
    P.kl Q = 0 ↔ P = Q := by
  constructor
  · intro hkl
    have htv : P.tv Q = 0 := by
      nlinarith [tv_sq_le_kl hdom, tv_nonneg P Q]
    have hsum : ∑ x, |P x - Q x| = 0 := by
      unfold tv at htv
      linarith
    apply Law.ext
    intro x
    have hx := Finset.single_le_sum (fun y _ => abs_nonneg (P y - Q y))
      (Finset.mem_univ x)
    rw [hsum] at hx
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hx (abs_nonneg _)))
  · rintro rfl
    simp [kl, entropy]

/-- The product deficit from uniform weights is exactly the exponential of
uniform-to-law relative entropy, scaled by cardinality. -/
theorem prod_eq_uniform_factor_mul_exp_kl [Nonempty α] (P : Law α)
    (hP : ∀ x, 0 < P x) :
    (∏ x, P x) = ((Fintype.card α : ℝ)⁻¹) ^ Fintype.card α *
      Real.exp (-((Fintype.card α : ℝ) * (uniform α).kl P)) := by
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos (α := α)
  have hkl : (uniform α).kl P =
      -((Fintype.card α : ℝ)⁻¹ * ∑ x, Real.log (P x)) -
        Real.log (Fintype.card α : ℝ) := by
    rw [kl, entropy_uniform, crossE, Ex]
    simp only [uniform_apply, mul_neg, Finset.sum_neg_distrib, ← Finset.mul_sum]
  have hlog : Real.log (∏ x, P x) =
      Real.log (((Fintype.card α : ℝ)⁻¹) ^ Fintype.card α) +
        -((Fintype.card α : ℝ) * (uniform α).kl P) := by
    rw [Real.log_prod (fun x _ => (hP x).ne'), Real.log_pow, Real.log_inv, hkl]
    field_simp [hN.ne']
    ring
  calc
    (∏ x, P x) = Real.exp (Real.log (∏ x, P x)) :=
      (Real.exp_log (Finset.prod_pos fun x _ => hP x)).symm
    _ = _ := by
      rw [hlog, Real.exp_add, Real.exp_log (pow_pos (inv_pos.mpr hN) _)]

end GaloisForLFunctions.HTGeometry.FourierLLogL.Law
