import Mathlib

/-!
# The repulsion scale is sharp up to the exponent

`DistinctRootsOfIntegerPolynomialsRepel` separates distinct roots of a monic integer polynomial of
degree `d` and height `H` by `≳ H^{−O(d²)}`. The exponent must grow with the degree: the Mignotte
polynomials

`f(x) = x^{2m} − 2(ax − 1)²`,  `a ≥ 4` an integer, `m ≥ 2`,

are monic of degree `2m` (`mignotte_monic`), have coefficients of size at most `2a²`, and have two real roots on either
side of `1/a` within `a^{−(m+1)}` of it (`mignotte_close_roots`): `f(1/a) = a^{−2m} > 0`, while
`f(1/a ± a^{−(m+1)}) = a^{−2m}((1 ± a^{−m})^{2m} − 2) < 0` because `(1 + a^{−m})^{2m} ≤ e^{2m/a^m} < 2`.

So integrality can guarantee no separation better than `H^{−d/4}` (`H ≍ a²`, `d = 2m`). At the
local complexity of `ζ` at height `T` (degree `≍ log T`, height `T^{O(1)}`) the scale that
integrality could guarantee lies between `e^{−C log³ T}` and `e^{−c log² T}`.
-/

open Polynomial

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- The Mignotte polynomial `X^{2m} − 2(aX − 1)²`. -/
def mignotte (a m : ℕ) : ℤ[X] := X ^ (2 * m) - 2 * (C (a : ℤ) * X - 1) ^ 2

theorem mignotte_eval (a m : ℕ) (x : ℝ) :
    ((mignotte a m).map (Int.castRingHom ℝ)).eval x = x ^ (2 * m) - 2 * (a * x - 1) ^ 2 := by
  simp [mignotte]

theorem mignotte_monic (a m : ℕ) (hm : 2 ≤ m) : (mignotte a m).Monic := by
  unfold mignotte
  have hdeg : (2 * (C (a : ℤ) * X - 1) ^ 2 : ℤ[X]).degree < (X ^ (2 * m) : ℤ[X]).degree := by
    rw [degree_X_pow]
    calc (2 * (C (a : ℤ) * X - 1) ^ 2 : ℤ[X]).degree ≤ 2 := by
          refine (degree_mul_le _ _).trans ?_
          have h1 : (2 : ℤ[X]).degree ≤ 0 := degree_C_le
          have h2 : ((C (a : ℤ) * X - 1) ^ 2 : ℤ[X]).degree ≤ 2 := by
            refine (degree_pow_le _ _).trans ?_
            have : (C (a : ℤ) * X - 1 : ℤ[X]).degree ≤ 1 := by
              refine (degree_sub_le _ _).trans (max_le ?_ ?_)
              · exact (degree_C_mul_X_le _)
              · rw [degree_one]; exact zero_le_one
            calc (2 : ℕ) • (C (a : ℤ) * X - 1 : ℤ[X]).degree ≤ (2 : ℕ) • (1 : WithBot ℕ) :=
                  nsmul_le_nsmul_right this 2
              _ = 2 := by norm_num
          calc (2 : ℤ[X]).degree + ((C (a : ℤ) * X - 1) ^ 2 : ℤ[X]).degree ≤ 0 + 2 :=
                add_le_add h1 h2
            _ = 2 := by simp
      _ < ((2 * m : ℕ) : WithBot ℕ) := by exact_mod_cast (by omega : 2 < 2 * m)
  exact (monic_X_pow _).sub_of_left hdeg

/-- The coefficients of the Mignotte polynomial are explicit: `x^{2m} − 2a²x² + 4ax − 2`. -/
theorem mignotte_eq (a m : ℕ) :
    mignotte a m = X ^ (2 * m) - C (2 * (a : ℤ) ^ 2) * X ^ 2 + C (4 * (a : ℤ)) * X - C 2 := by
  unfold mignotte
  simp only [map_mul, map_pow, map_ofNat]
  ring

theorem four_mul_le_four_pow : ∀ m : ℕ, 4 * m ≤ 4 ^ m
  | 0 => by norm_num
  | 1 => by norm_num
  | (k + 2) => by have := four_mul_le_four_pow (k + 1); rw [pow_succ]; omega

theorem one_add_pow_lt_two {a : ℕ} (ha : 4 ≤ a) (m : ℕ) :
    (1 + ((a : ℝ) ^ m)⁻¹) ^ (2 * m) < 2 := by
  set x : ℝ := ((a : ℝ) ^ m)⁻¹ with hx
  have hx0 : 0 ≤ x := by positivity
  have h4m : (4 : ℝ) * m ≤ (a : ℝ) ^ m := by
    have h1 : (4 : ℝ) ^ m ≤ (a : ℝ) ^ m := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast ha) m
    have h2 : (4 : ℝ) * m ≤ 4 ^ m := by exact_mod_cast four_mul_le_four_pow m
    linarith
  have hexp : (1 + x) ^ (2 * m) ≤ Real.exp (((2 * m : ℕ) : ℝ) * x) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp x]) _
  have hsmall : ((2 * m : ℕ) : ℝ) * x ≤ 1 / 2 := by
    have hapos : (0 : ℝ) < (a : ℝ) ^ m := by
      have : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
      positivity
    rw [hx, ← div_eq_mul_inv, div_le_iff₀ hapos]
    push_cast
    linarith
  have he : Real.exp (1 / 2) < 2 := by
    have := Real.exp_one_lt_d9
    have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  calc (1 + x) ^ (2 * m) ≤ Real.exp (((2 * m : ℕ) : ℝ) * x) := hexp
    _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hsmall
    _ < 2 := he

/-- **Mignotte polynomials have close roots.** For integers `a ≥ 4`, `m ≥ 1`, the polynomial
`x^{2m} − 2(ax − 1)²` has real roots `x₁ ∈ (1/a − a^{−(m+1)}, 1/a)` and
`x₂ ∈ (1/a, 1/a + a^{−(m+1)})`; in particular `0 < x₂ − x₁ < 2a^{−(m+1)}`. -/
theorem mignotte_close_roots {a m : ℕ} (ha : 4 ≤ a) (hm : 1 ≤ m) :
    ∃ x₁ x₂ : ℝ, ((mignotte a m).map (Int.castRingHom ℝ)).IsRoot x₁ ∧
      ((mignotte a m).map (Int.castRingHom ℝ)).IsRoot x₂ ∧
      x₁ < x₂ ∧ x₂ - x₁ < 2 * ((a : ℝ) ^ (m + 1))⁻¹ := by
  set f := (mignotte a m).map (Int.castRingHom ℝ) with hf
  have ha0 : (0 : ℝ) < a := by positivity
  set h : ℝ := ((a : ℝ) ^ (m + 1))⁻¹ with hh
  have hh0 : 0 < h := by positivity
  set c : ℝ := (a : ℝ)⁻¹ with hc
  have hc0 : 0 < c := by positivity
  have hah : (a : ℝ) * h = ((a : ℝ) ^ m)⁻¹ := by
    rw [hh, pow_succ, mul_inv, mul_comm, mul_assoc, inv_mul_cancel₀ ha0.ne', mul_one]
  have hlt1 : ((a : ℝ) ^ m)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by
    have : (4 : ℝ) ≤ a := by exact_mod_cast ha
    linarith) (by omega))
  -- values at `1/a` and `1/a ± h`
  have hmid : 0 < f.eval c := by
    rw [hf, mignotte_eval, hc, mul_inv_cancel₀ ha0.ne', sub_self]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero]
    positivity
  have hside : ∀ u : ℝ, |u| = h → f.eval (c + u) < 0 := by
    intro u hu
    rw [hf, mignotte_eval]
    have hsq : ((a : ℝ) * (c + u) - 1) ^ 2 = ((a : ℝ) ^ m)⁻¹ ^ 2 := by
      rw [hc, mul_add, mul_inv_cancel₀ ha0.ne', add_sub_cancel_left, mul_pow, ← sq_abs u, hu,
        ← mul_pow, hah]
    rw [hsq]
    -- `(c + u)^{2m} ≤ c^{2m}(1 + a^{−m})^{2m}` and `c^{2m} = (a^{−m})²`
    have hcu : |c + u| ≤ c * (1 + ((a : ℝ) ^ m)⁻¹) := by
      calc |c + u| ≤ |c| + |u| := abs_add_le _ _
        _ = c * (1 + ((a : ℝ) ^ m)⁻¹) := by
          rw [abs_of_pos hc0, hu, mul_add, mul_one, ← hah, hc, ← mul_assoc, inv_mul_cancel₀ ha0.ne',
            one_mul]
    have hpow : (c + u) ^ (2 * m) ≤ (c * (1 + ((a : ℝ) ^ m)⁻¹)) ^ (2 * m) := by
      rw [pow_mul, pow_mul, ← sq_abs (c + u)]
      exact pow_le_pow_left₀ (by positivity)
        (pow_le_pow_left₀ (abs_nonneg _) hcu 2) m
    have hcm : c ^ (2 * m) = ((a : ℝ) ^ m)⁻¹ ^ 2 := by
      rw [hc, inv_pow, inv_pow, ← pow_mul, mul_comm]
    rw [mul_pow, hcm] at hpow
    have hlt := one_add_pow_lt_two ha m
    have hpos : 0 < ((a : ℝ) ^ m)⁻¹ ^ 2 := by positivity
    nlinarith
  have hleft := hside (-h) (by rw [abs_neg, abs_of_pos hh0])
  have hright := hside h (abs_of_pos hh0)
  -- intermediate values
  have hcont : Continuous fun x => f.eval x := f.continuous
  obtain ⟨x₁, hx₁, hr₁⟩ : ∃ x ∈ Set.Ioo (c - h) c, f.eval x = 0 := by
    have := intermediate_value_Ioo (by linarith : c + -h ≤ c) hcont.continuousOn
    rw [← sub_eq_add_neg] at this hleft
    exact this ⟨hleft, hmid⟩
  obtain ⟨x₂, hx₂, hr₂⟩ : ∃ x ∈ Set.Ioo c (c + h), f.eval x = 0 := by
    have := intermediate_value_Ioo' (by linarith : c ≤ c + h) hcont.continuousOn
    exact this ⟨hright, hmid⟩
  exact ⟨x₁, x₂, hr₁, hr₂, by linarith [hx₁.2, hx₂.1], by linarith [hx₁.1, hx₂.2]⟩

end GaloisForLFunctions.ArithmeticDiscreteness
