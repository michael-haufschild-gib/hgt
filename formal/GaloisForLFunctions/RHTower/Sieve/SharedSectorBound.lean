import GaloisForLFunctions.RHTower.Sieve.BalancedPairsNested

/-!
# The shared-prime sector, bounded by a product

Assembling the nested decomposition with the two interval counts gives the card's `(10)`:

    C_p(x,h) ≤ ((√x + 2)/p + 1) · ((h + 2)/p + 1).

The outer factor counts the multiples of `p` in `[√x, 2√x]`, the inner one the multiples of `p` in
the `n₂`-interval, whose length is at most `h` because `n₁ ≥ √x`.

The `+2`'s replace the card's `+1`'s and cost nothing: the tail estimate accepts arbitrary
nonnegative lengths, and `(√x+2)(h+2)/(h√x) → 1`.
-/

namespace RHTower.Sieve

open Finset

/-- The squarefree pair weight is at most one. -/
theorem moebius_pair_weight_le_one (a b : ℕ) :
    ((ArithmeticFunction.moebius a : ℤ) : ℝ) ^ (2 : ℕ)
      * ((ArithmeticFunction.moebius b : ℤ) : ℝ) ^ (2 : ℕ) ≤ 1 := by
  rcases moebius_trichotomy a with ha | ha | ha <;> rcases moebius_trichotomy b with hb | hb | hb <;>
    rw [ha, hb] <;> norm_num

/-- **The outer interval count.** -/
theorem outer_count_le {x : ℝ} (hx : 4 ≤ x) {p : ℕ} (hp : 0 < p) (M : ℕ) :
    (((Finset.Icc 1 M).filter
        (fun a : ℕ => (Real.sqrt x ≤ (a : ℝ) ∧ (a : ℝ) ≤ 2 * Real.sqrt x) ∧ p ∣ a)).card : ℝ)
      ≤ (Real.sqrt x + 2) / p + 1 := by
  classical
  have hx0 : (0 : ℝ) < x := by linarith
  have hs2 : (2 : ℝ) ≤ Real.sqrt x := by
    have h4 : Real.sqrt 4 ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
    have heq : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    linarith [h4, heq.le, heq.ge]
  have hs0 : (0 : ℝ) < Real.sqrt x := by linarith
  set c : ℕ := ⌊Real.sqrt x⌋₊ with hc
  set d : ℕ := ⌊2 * Real.sqrt x⌋₊ with hd
  have hc1 : 1 ≤ c := Nat.le_floor (by exact_mod_cast (by linarith : (1 : ℝ) ≤ Real.sqrt x))
  have hcd : c ≤ d := Nat.floor_le_floor (by linarith)
  have hsub : (Finset.Icc 1 M).filter
      (fun a : ℕ => (Real.sqrt x ≤ (a : ℝ) ∧ (a : ℝ) ≤ 2 * Real.sqrt x) ∧ p ∣ a)
      ⊆ (Finset.Icc c d).filter (fun a => p ∣ a) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨-, ⟨ha1, ha2⟩, hpa⟩ := ha
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, hpa⟩
    · calc c = ⌊Real.sqrt x⌋₊ := hc
        _ ≤ ⌊((a : ℕ) : ℝ)⌋₊ := Nat.floor_le_floor ha1
        _ = a := Nat.floor_natCast a
    · exact Nat.le_floor ha2
  have hcard := Finset.card_le_card hsub
  have hcardR : (((Finset.Icc 1 M).filter
      (fun a : ℕ => (Real.sqrt x ≤ (a : ℝ) ∧ (a : ℝ) ≤ 2 * Real.sqrt x) ∧ p ∣ a)).card : ℝ)
      ≤ (((Finset.Icc c d).filter (fun a => p ∣ a)).card : ℝ) := by exact_mod_cast hcard
  refine le_trans hcardR ?_
  refine le_trans (card_filter_dvd_Icc_le hp hc1 hcd) ?_
  have hdle : (d : ℝ) ≤ 2 * Real.sqrt x := Nat.floor_le (by linarith)
  have hcge : Real.sqrt x - 1 < (c : ℝ) := by
    have := Nat.lt_floor_add_one (Real.sqrt x)
    linarith
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlen : (d : ℝ) - (c : ℝ) + 1 ≤ Real.sqrt x + 2 := by linarith
  have hdiv : ((d : ℝ) - (c : ℝ) + 1) / p ≤ (Real.sqrt x + 2) / p := by gcongr
  linarith

/-- **Card equation (10).**  The shared-prime sector, bounded by a product of interval counts. -/
theorem sharedSectorCount_le_product {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {p : ℕ} (hp : 0 < p) :
    sharedSectorCount x h p
      ≤ ((Real.sqrt x + 2) / p + 1) * ((h + 2) / p + 1) := by
  classical
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hinner0 : (0 : ℝ) ≤ (h + 2) / p + 1 := by positivity
  set M : ℕ := ⌊x + h * Real.sqrt x⌋₊ with hM
  set B : ℝ := (h + 2) / (p : ℝ) + 1 with hB
  rw [sharedSectorCount,
    sum_balancedPairs_filter_nested (x := x) (h := h)
      (w := fun q => ((ArithmeticFunction.moebius q.1 : ℤ) : ℝ) ^ (2 : ℕ)
        * ((ArithmeticFunction.moebius q.2 : ℤ) : ℝ) ^ (2 : ℕ))
      (R := fun q => p ∣ q.1 ∧ p ∣ q.2)]
  have hstep : ∀ a ∈ Finset.Icc 1 M,
      (∑ b ∈ (Finset.Icc 1 M).filter
          (fun b => (x ≤ ((a * b : ℕ) : ℝ) ∧ ((a * b : ℕ) : ℝ) ≤ x + h * Real.sqrt x
              ∧ Real.sqrt x ≤ (a : ℝ) ∧ (a : ℝ) ≤ 2 * Real.sqrt x) ∧ (p ∣ a ∧ p ∣ b)),
          ((ArithmeticFunction.moebius a : ℤ) : ℝ) ^ (2 : ℕ)
            * ((ArithmeticFunction.moebius b : ℤ) : ℝ) ^ (2 : ℕ))
        ≤ (if (Real.sqrt x ≤ (a : ℝ) ∧ (a : ℝ) ≤ 2 * Real.sqrt x) ∧ p ∣ a then B else 0) := by
    intro a _
    by_cases hcond : (Real.sqrt x ≤ (a : ℝ) ∧ (a : ℝ) ≤ 2 * Real.sqrt x) ∧ p ∣ a
    · rw [if_pos hcond]
      have hcardle := inner_count_le hx hh hp hcond.1.1 hcond.1.2 M
      refine le_trans (Finset.sum_le_card_nsmul _ _ 1 ?_) ?_
      · intro b _
        exact moebius_pair_weight_le_one a b
      · rw [nsmul_eq_mul, mul_one]
        exact hcardle
    · rw [if_neg hcond]
      refine le_of_eq (Finset.sum_eq_zero ?_)
      intro b hb
      rw [Finset.mem_filter] at hb
      exact absurd ⟨⟨hb.2.1.2.2.1, hb.2.1.2.2.2⟩, hb.2.2.1⟩ hcond
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have houter := outer_count_le hx hp M
  exact mul_le_mul_of_nonneg_right houter hinner0

end RHTower.Sieve
