import Mathlib

/-!
# Quantitative stability of logarithmic derivatives

If an approximating value is within half the norm of a nonzero target value, then it is nonzero,
and the difference of the two logarithmic quotients is controlled explicitly by the value and
derivative errors.  This is the generic analytic transfer needed to compare a rapidly convergent
Taylor polynomial with `XiC` at mesh points that move toward a hypothetical zero.
-/

open Complex

namespace RHTower

/-- Quantitative stability of a quotient under simultaneous numerator and denominator
perturbation.  The half-norm hypothesis also proves that the approximating denominator is
nonzero. -/
theorem norm_div_sub_div_le_of_two_norm_sub_le
    {a b A B : ℂ} (hb : b ≠ 0) (hclose : 2 * ‖a - b‖ ≤ ‖b‖) :
    a ≠ 0 ∧
      ‖A / a - B / b‖ ≤
        ‖A - B‖ * (2 / ‖b‖) +
          ‖B‖ * ‖a - b‖ * (2 / ‖b‖) * (1 / ‖b‖) := by
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hdiff : ‖a - b‖ ≤ ‖b‖ / 2 := by linarith
  have hdiff_lt : ‖a - b‖ < ‖b‖ := by linarith
  have ha : a ≠ 0 := by
    intro ha0
    subst a
    simp only [zero_sub, norm_neg] at hdiff_lt
    exact (lt_irrefl ‖b‖) hdiff_lt
  have htri : ‖b‖ ≤ ‖a - b‖ + ‖a‖ := by
    calc
      ‖b‖ = ‖(b - a) + a‖ := by congr 1; ring
      _ ≤ ‖b - a‖ + ‖a‖ := norm_add_le _ _
      _ = ‖a - b‖ + ‖a‖ := by rw [norm_sub_rev]
  have haLower : ‖b‖ / 2 ≤ ‖a‖ := by linarith
  have hinv : ‖a⁻¹‖ ≤ 2 / ‖b‖ := by
    rw [norm_inv]
    calc
      ‖a‖⁻¹ = 1 / ‖a‖ := by rw [one_div]
      _ ≤ 1 / (‖b‖ / 2) := one_div_le_one_div_of_le (by positivity) haLower
      _ = 2 / ‖b‖ := by field_simp
  refine ⟨ha, ?_⟩
  have hid : A / a - B / b =
      (A - B) * a⁻¹ + B * (b - a) * a⁻¹ * b⁻¹ := by
    field_simp [ha, hb]
    ring
  rw [hid]
  calc
    ‖(A - B) * a⁻¹ + B * (b - a) * a⁻¹ * b⁻¹‖ ≤
        ‖(A - B) * a⁻¹‖ + ‖B * (b - a) * a⁻¹ * b⁻¹‖ := norm_add_le _ _
    _ = ‖A - B‖ * ‖a⁻¹‖ +
        ‖B‖ * ‖a - b‖ * ‖a⁻¹‖ * ‖b⁻¹‖ := by
      simp only [norm_mul]
      rw [norm_sub_rev b a]
    _ ≤ ‖A - B‖ * (2 / ‖b‖) +
        ‖B‖ * ‖a - b‖ * (2 / ‖b‖) * (1 / ‖b‖) := by
      have hinv' : ‖a‖⁻¹ ≤ 2 / ‖b‖ := by
        simpa only [norm_inv] using hinv
      rw [norm_inv a, norm_inv b,
        show ‖b‖⁻¹ = 1 / ‖b‖ by rw [one_div]]
      gcongr

/-- Function-level logarithmic-derivative perturbation bound. -/
theorem norm_logDeriv_sub_logDeriv_le_of_two_norm_sub_le
    {f g : ℂ → ℂ} {z : ℂ} (hf : f z ≠ 0)
    (hclose : 2 * ‖g z - f z‖ ≤ ‖f z‖) :
    g z ≠ 0 ∧
      ‖logDeriv g z - logDeriv f z‖ ≤
        ‖deriv g z - deriv f z‖ * (2 / ‖f z‖) +
          ‖deriv f z‖ * ‖g z - f z‖ * (2 / ‖f z‖) * (1 / ‖f z‖) := by
  simpa only [logDeriv_apply] using
    (norm_div_sub_div_le_of_two_norm_sub_le
      (a := g z) (b := f z) (A := deriv g z) (B := deriv f z) hf hclose)

end RHTower
