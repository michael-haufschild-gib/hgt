import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ExponentialBarrierPotential

/-!
# The exact boundary of the exponential row comparison

The full barrier comparison contains a leading row of coefficient seven
and exponent `β + 1/2`, and a lower row of exponent `β`. Confinement has
coefficient `a` and exponent eight. Absorption by confinement and a
constant is possible exactly for `β < 15/2`, or at `β = 15/2` when `a > 7`.
The same classification holds for the two diagonal coercivity inequalities
used in the minimizer comparison.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations

private theorem exists_large_exp {r : ℝ} (hr : 0 < r) (C : ℝ) :
    ∃ x : ℝ, 0 ≤ x ∧ C < Real.exp (r * x) := by
  refine ⟨(|C| + 1) / r, (div_pos (by positivity) hr).le, ?_⟩
  have he : r * ((|C| + 1) / r) = |C| + 1 := by field_simp
  rw [he]
  linarith only [Real.add_one_le_exp (|C| + 1), le_abs_self C]

private theorem exp_scaled_product (r s x : ℝ) :
    Real.exp (r * x) * Real.exp (-(s * x)) = Real.exp ((r - s) * x) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- Exact absorption criterion for the complete prime and forcing rows. -/
theorem exponentialBarrier_potentialDominance_iff {a β : ℝ}
    (ha : 0 < a) (hβ : 1 / 2 < β) (V : ℝ) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, u ≤ 0 →
      6 * Real.exp (-((β + 1 / 2) * u)) + V + Real.exp (-(β * u)) +
        Real.exp (-((β + 1 / 2) * u)) ≤ a * Real.exp (-(8 * u)) + B) ↔
      β < 15 / 2 ∨ (β = 15 / 2 ∧ 7 < a) := by
  constructor
  · rintro ⟨B, _, hB⟩
    have hrow (x : ℝ) (hx : 0 ≤ x) :
        7 * Real.exp ((β + 1 / 2) * x) + Real.exp (β * x) + V ≤
          a * Real.exp (8 * x) + B := by
      have h := hB (-x) (neg_nonpos.mpr hx)
      simp only [mul_neg, neg_neg] at h
      linarith only [h]
    have hβle : β ≤ 15 / 2 := by
      by_contra h
      have hr : 0 < β + 1 / 2 - 8 := by linarith only [lt_of_not_ge h]
      obtain ⟨x, hx, hlarge⟩ := exists_large_exp hr ((a + |B - V|) / 7)
      have hbase : 7 * Real.exp ((β + 1 / 2) * x) ≤
          a * Real.exp (8 * x) + (B - V) := by
        linarith only [hrow x hx, (Real.exp_pos (β * x)).le]
      have hmul := mul_le_mul_of_nonneg_right hbase (Real.exp_pos (-(8 * x))).le
      have hmain : 7 * Real.exp ((β + 1 / 2 - 8) * x) ≤
          a + (B - V) * Real.exp (-(8 * x)) := by
        rw [add_mul, mul_assoc, exp_scaled_product, mul_assoc, exp_scaled_product,
          sub_self, zero_mul, Real.exp_zero, mul_one] at hmul
        exact hmul
      have he : Real.exp (-(8 * x)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith only [hx])
      have herr : (B - V) * Real.exp (-(8 * x)) ≤ |B - V| :=
        (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le).trans
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he (abs_nonneg (B - V)))
      linarith only [hmain, herr, hlarge]
    rcases lt_or_eq_of_le hβle with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      by_contra ha7
      have ha7 : a ≤ 7 := le_of_not_gt ha7
      obtain ⟨x, hx, hlarge⟩ := exists_large_exp (by linarith only [hβ] : 0 < β) (B - V)
      have h := hrow x hx
      rw [show β + 1 / 2 = 8 by linarith only [heq]] at h
      have hcoeff := mul_le_mul_of_nonneg_right ha7 (Real.exp_pos (8 * x)).le
      linarith only [h, hcoeff, hlarge]
  · rintro (hlt | ⟨rfl, ha7⟩)
    · exact exists_exponentialBarrier_potentialDominance ha hβ hlt V
    · obtain ⟨C, hC, hc⟩ := exists_exponential_absorption
        (a := a - 7) (c := 1) (p := 15 / 2) (q := 8)
        (by linarith only [ha7]) (by norm_num) (by norm_num) (by norm_num)
      refine ⟨C + |V|, add_nonneg hC (abs_nonneg V), fun u hu => ?_⟩
      have h := hc (-u) (neg_nonneg.mpr hu)
      simp only [one_mul, mul_neg] at h
      norm_num only at ⊢
      nlinarith only [h, le_abs_self V]

/-- The exact same boundary governs the diagonal inequalities used by the weak equation. -/
theorem exponentialBarrier_diagonalCoercivity_iff {a β : ℝ}
    (ha : 0 < a) (hβ : 1 / 2 < β) (V : ℝ) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ c : ℝ, B ≤ c → ∀ u : ℝ, u ≤ 0 →
      1 ≤ a * Real.exp (-(8 * u)) + c -
        (6 * Real.exp (-((β + 1 / 2) * u)) + V) ∧
      1 + Real.exp (-(u / 2)) ≤
        (a * Real.exp (-(8 * u)) + c -
          (6 * Real.exp (-((β + 1 / 2) * u)) + V)) * Real.exp (β * u)) ↔
      β < 15 / 2 ∨ (β = 15 / 2 ∧ 7 < a) := by
  rw [← exponentialBarrier_potentialDominance_iff ha hβ V]
  constructor
  · rintro ⟨B, hB, h⟩
    refine ⟨B, hB, fun u hu => ?_⟩
    have hc := mul_le_mul_of_nonneg_right (h B le_rfl u hu).2 (Real.exp_pos (-(β * u))).le
    have he : Real.exp (β * u) * Real.exp (-(β * u)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hh : Real.exp (-(u / 2)) * Real.exp (-(β * u)) =
        Real.exp (-((β + 1 / 2) * u)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [add_mul, one_mul, mul_assoc, he, mul_one, hh] at hc
    linarith only [hc]
  · rintro ⟨B, hB, h⟩
    refine ⟨B, hB, fun c hc u hu => ?_⟩
    have hrow : Real.exp (-(β * u)) + Real.exp (-((β + 1 / 2) * u)) ≤
        a * Real.exp (-(8 * u)) + c -
          (6 * Real.exp (-((β + 1 / 2) * u)) + V) := by
      linarith only [h u hu, hc]
    have hone : 1 ≤ Real.exp (-(β * u)) :=
      Real.one_le_exp (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
        (by linarith only [hβ] : 0 ≤ β) hu))
    refine ⟨by linarith only [hone, hrow, (Real.exp_pos (-((β + 1 / 2) * u))).le], ?_⟩
    have he : Real.exp (-(β * u)) * Real.exp (β * u) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hh : Real.exp (-((β + 1 / 2) * u)) * Real.exp (β * u) =
        Real.exp (-(u / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hm := mul_le_mul_of_nonneg_right hrow (Real.exp_pos (β * u)).le
    rwa [add_mul, he, hh] at hm

/-- No coefficient or constant can make this row comparison reach decay rate eight. -/
theorem no_exponentialBarrier_coercivity_at_eight {a : ℝ} (ha : 0 < a) (V : ℝ) :
    ¬ ∃ B : ℝ, 0 ≤ B ∧ ∀ c : ℝ, B ≤ c → ∀ u : ℝ, u ≤ 0 →
      1 ≤ a * Real.exp (-(8 * u)) + c -
        (6 * Real.exp (-((8 + 1 / 2) * u)) + V) ∧
      1 + Real.exp (-(u / 2)) ≤
        (a * Real.exp (-(8 * u)) + c -
          (6 * Real.exp (-((8 + 1 / 2) * u)) + V)) * Real.exp (8 * u) := by
  rw [exponentialBarrier_diagonalCoercivity_iff ha (by norm_num)]
  norm_num

#print axioms exponentialBarrier_potentialDominance_iff
#print axioms exponentialBarrier_diagonalCoercivity_iff
#print axioms no_exponentialBarrier_coercivity_at_eight

end GaloisForLFunctions.ExclusionOfTheCriticalState
