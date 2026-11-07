import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Nonvanishing in balanced rotated relations

An identity `T F = a F(q·) + b F(conj(q)·)` with `‖a‖ = ‖b‖` constrains a zero of
`F` only when its coefficients do not both vanish there. Every function admits such an
identity with `a = b = F`. The reverse triangle inequality gives the exact local
alternative and a quantitative lower bound for the residual of an approximate relation.

The modulus difference of a rotated linear factor is oriented by `Im q`: conjugating
the rotation reverses the inequality.
-/

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- The residual pays the difference between the two weighted moduli. -/
theorem weighted_modulus_gap_le (a b u v : ℂ) :
    |‖a‖ * ‖u‖ - ‖b‖ * ‖v‖| ≤ ‖a * u + b * v‖ := by
  simpa only [norm_mul, norm_neg, sub_neg_eq_add] using
    abs_norm_sub_norm_le (a * u) (-(b * v))

/-- Balanced coefficients retain the full modulus gap, scaled by their common norm. -/
theorem balanced_modulus_gap_le {a b : ℂ} (hab : ‖a‖ = ‖b‖) (u v : ℂ) :
    ‖a‖ * |‖u‖ - ‖v‖| ≤ ‖a * u + b * v‖ := by
  have h := weighted_modulus_gap_le a b u v
  rw [← hab, ← mul_sub, abs_mul, abs_of_nonneg (norm_nonneg a)] at h
  exact h

/-- At a vanishing balanced relation, either both coefficients vanish or the moduli agree. -/
theorem balanced_relation_zero_or_modulus_eq {a b u v : ℂ}
    (hab : ‖a‖ = ‖b‖) (hrel : a * u + b * v = 0) :
    (a = 0 ∧ b = 0) ∨ ‖u‖ = ‖v‖ := by
  by_cases ha : a = 0
  · left
    exact ⟨ha, norm_eq_zero.mp (by rw [← hab, ha, norm_zero])⟩
  · right
    have h := congrArg norm (eq_neg_of_add_eq_zero_left hrel)
    simp only [norm_mul, norm_neg] at h
    rw [← hab] at h
    exact mul_left_cancel₀ (norm_ne_zero_iff.mpr ha) h

/-- Equal moduli are precisely the pairs admitting cancellation with unit coefficients. -/
theorem exists_unit_balanced_cancellation_iff (u v : ℂ) :
    (∃ a b : ℂ, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ a * u + b * v = 0) ↔ ‖u‖ = ‖v‖ := by
  constructor
  · rintro ⟨a, b, ha, hb, hrel⟩
    have h := congrArg norm (eq_neg_of_add_eq_zero_left hrel)
    simpa only [norm_mul, norm_neg, ha, hb, one_mul] using h
  · intro huv
    by_cases hv : v = 0
    · have hu : u = 0 := norm_eq_zero.mp (by rw [huv, hv, norm_zero])
      exact ⟨1, 1, norm_one, norm_one, by simp only [hu, hv, mul_zero, add_zero]⟩
    · refine ⟨1, -(u / v), norm_one, ?_, ?_⟩
      · rw [norm_neg, norm_div, huv, div_self (norm_ne_zero_iff.mpr hv)]
      · rw [one_mul, neg_mul, div_mul_cancel₀ _ hv, add_neg_cancel]

/-- Without coefficient nonvanishing the rotated identity holds for every function. -/
theorem self_coefficient_rotated_relation (F : ℂ → ℂ) (q z : ℂ) :
    (F (q * z) + F (star q * z)) * F z =
      F z * F (q * z) + F z * F (star q * z) := by
  ring

/-- Even normalized entire coefficients admit an off-axis zero with unequal rotated moduli. -/
theorem exists_normalized_entire_vacuous_rotated_relation :
    ∃ F a b T : ℂ → ℂ,
      Differentiable ℂ F ∧ Differentiable ℂ a ∧ Differentiable ℂ b ∧
      Differentiable ℂ T ∧ F 0 = 1 ∧ a 0 = 1 ∧ b 0 = 1 ∧
      (∀ z, ‖a z‖ = ‖b z‖) ∧
      (∀ z, T z * F z = a z * F (Complex.I * z) + b z * F (-Complex.I * z)) ∧
      F (1 + Complex.I) = 0 ∧
      F (Complex.I * (1 + Complex.I)) ≠ 0 ∧
      F (-Complex.I * (1 + Complex.I)) = 0 := by
  let F : ℂ → ℂ := fun z => (z ^ 2 - 2 * z + 2) / 2
  have hF : Differentiable ℂ F := by dsimp [F]; fun_prop
  refine ⟨F, F, F, fun z => F (Complex.I * z) + F (-Complex.I * z),
    hF, hF, hF, ?_, ?_, ?_, ?_, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · fun_prop
  · norm_num [F]
  · norm_num [F]
  · norm_num [F]
  · intro z; ring
  · norm_num [F, Complex.ext_iff, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, pow_two]
  · intro h
    have him := congrArg Complex.im h
    norm_num [F, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply, pow_two] at him
  · norm_num [F, Complex.ext_iff, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, pow_two]

/-- The factor comparison changes sign when the rotation is conjugated. -/
theorem rotated_factor_norm_sq_sub (q u : ℂ) :
    ‖1 - q * u‖ ^ 2 - ‖1 - star q * u‖ ^ 2 = 4 * q.im * u.im := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

#print axioms balanced_modulus_gap_le
#print axioms balanced_relation_zero_or_modulus_eq
#print axioms exists_unit_balanced_cancellation_iff
#print axioms exists_normalized_entire_vacuous_rotated_relation
#print axioms rotated_factor_norm_sq_sub

end GaloisForLFunctions.RigidArithmeticOfCuts
