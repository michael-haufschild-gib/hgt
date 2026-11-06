import Mathlib

/-!
# Exponential tails beyond a product cutoff

Splitting the exponential retains the full product cutoff, while the
remaining factor is bounded by a product of geometric sequences.
-/

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms

private theorem summable_geometric_product {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (B : ℝ) :
    Summable (fun p : ℕ × ℕ => B * a ^ p.1 * a ^ p.2) := by
  have ha : ‖a‖ < 1 := by rwa [Real.norm_of_nonneg ha0]
  have hg := summable_geometric_of_norm_lt_one ha
  have hgn : Summable (fun n : ℕ => ‖a ^ n‖) := by
    simpa only [norm_pow, Real.norm_of_nonneg ha0] using hg
  simpa only [mul_assoc] using (summable_mul_of_summable_norm hgn hgn).mul_left B

private theorem tsum_geometric_product {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (B : ℝ) :
    (∑' p : ℕ × ℕ, B * a ^ p.1 * a ^ p.2) = B / (1 - a) ^ 2 := by
  have ha : ‖a‖ < 1 := by rwa [Real.norm_of_nonneg ha0]
  have hg := summable_geometric_of_norm_lt_one ha
  have hp : Summable (fun p : ℕ × ℕ => a ^ p.1 * a ^ p.2) := by
    simpa only [one_mul] using summable_geometric_product ha0 ha1 1
  simp_rw [mul_assoc]
  rw [tsum_mul_left, ← hg.tsum_mul_tsum hg hp, tsum_geometric_of_norm_lt_one ha]
  have hd : 1 - a ≠ 0 := (sub_pos.mpr ha1).ne'
  field_simp [hd]

/-- Exponential mass of positive ordered pairs beyond a product cutoff. -/
def productExponentialTail (q L : ℝ) : ℝ :=
  ∑' p : ℕ × ℕ, if L ≤ ((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1) then
    Real.exp (-q * (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1))) else 0

private theorem product_exponential_geometric_bound {q : ℝ} (hq : 0 < q)
    (L : ℝ) (p : ℕ × ℕ) :
    (if L ≤ ((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1) then
      Real.exp (-q * (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1))) else 0) ≤
      Real.exp (-q * L / 2) * Real.exp (-q / 4) ^ p.1 * Real.exp (-q / 4) ^ p.2 := by
  split_ifs with hcut
  · rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hp1 : 0 ≤ (p.1 : ℝ) := Nat.cast_nonneg _
    have hp2 : 0 ≤ (p.2 : ℝ) := Nat.cast_nonneg _
    have hprod : (p.1 : ℝ) + p.2 ≤ 2 * (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1)) := by
      nlinarith only [hp1, hp2, mul_nonneg hp1 hp2]
    have h1 := mul_nonneg hq.le (sub_nonneg.mpr hcut)
    have h2 := mul_nonneg hq.le (sub_nonneg.mpr hprod)
    nlinarith only [h1, h2]
  · positivity

/-- The product tail converges absolutely before any cancellation. -/
theorem summable_productExponentialTail {q : ℝ} (hq : 0 < q) (L : ℝ) :
    Summable (fun p : ℕ × ℕ => if L ≤ ((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1) then
      Real.exp (-q * (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1))) else 0) := by
  have ha0 := (Real.exp_pos (-q / 4)).le
  have ha1 : Real.exp (-q / 4) < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hq])
  exact Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity)
    (product_exponential_geometric_bound hq L)
    (summable_geometric_product ha0 ha1 _)

/-- Product truncation retains exponential decay at half the original product rate. -/
theorem productExponentialTail_le {q : ℝ} (hq : 0 < q) (L : ℝ) :
    productExponentialTail q L ≤ Real.exp (-q * L / 2) / (1 - Real.exp (-q / 4)) ^ 2 := by
  have ha0 := (Real.exp_pos (-q / 4)).le
  have ha1 : Real.exp (-q / 4) < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hq])
  have h := Summable.tsum_le_tsum (product_exponential_geometric_bound hq L)
    (summable_productExponentialTail hq L) (summable_geometric_product ha0 ha1 _)
  rw [tsum_geometric_product ha0 ha1] at h
  exact h

private theorem one_sub_exp_neg_quarter_lower {q : ℝ} (hq : 0 < q) (hq4 : q ≤ 4) :
    q / 8 ≤ 1 - Real.exp (-q / 4) := by
  have he : 1 + q / 4 ≤ Real.exp (q / 4) := by
    linarith only [Real.add_one_le_exp (q / 4)]
  have hi : Real.exp (-q / 4) ≤ 1 / (1 + q / 4) := by
    rw [neg_div, Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) he
  calc
    q / 8 ≤ q / (4 + q) :=
      div_le_div_of_nonneg_left hq.le (by positivity) (by linarith only [hq4])
    _ = 1 - 1 / (1 + q / 4) := by
      field_simp [show 4 + q ≠ 0 by positivity, show 1 + q / 4 ≠ 0 by positivity]
      ring
    _ ≤ _ := sub_le_sub_left hi 1

/-- On bounded positive rates, the geometric denominator costs at most a quadratic inverse rate. -/
theorem productExponentialTail_le_inverseSquare {q : ℝ}
    (hq : 0 < q) (hq4 : q ≤ 4) (L : ℝ) :
    productExponentialTail q L ≤ (64 / q ^ 2) * Real.exp (-q * L / 2) := by
  have hd := one_sub_exp_neg_quarter_lower hq hq4
  have hq8 : 0 < q / 8 := by positivity
  have hsq := pow_le_pow_left₀ hq8.le hd 2
  calc
    _ ≤ Real.exp (-q * L / 2) / (1 - Real.exp (-q / 4)) ^ 2 :=
      productExponentialTail_le hq L
    _ ≤ Real.exp (-q * L / 2) / (q / 8) ^ 2 :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (sq_pos_of_pos hq8) hsq
    _ = _ := by
      field_simp [hq.ne']
      norm_num

end GaloisForLFunctions.CompletedArithmeticForms

