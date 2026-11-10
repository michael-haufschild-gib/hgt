import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitCompositions
import Mathlib.Order.Interval.Finset.Nat

/-!
# The geometric cost of nested digit prefixes

If each deleted prefix lowers retained digit exponents by one level, a
finite arithmetic-geometric sum bounds the total prefix weight. This is
the numerical estimate used after the carry recursion creates digit gaps.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss


/-- The finite arithmetic-geometric sum measuring repeated digit-prefix costs. -/
theorem weighted_geometric_prefix_sum (q : ℤ) (n : ℕ) :
    (q - 1) ^ 2 * (∑ i ∈ range n, ((n - i : ℕ) : ℤ) * q ^ i) =
      q ^ (n + 1) - ((n + 1 : ℕ) : ℤ) * q + n := by
  induction n with
  | zero => simp only [range_zero, sum_empty, mul_zero, Nat.zero_add, pow_one,
      Nat.cast_one, one_mul, Nat.cast_zero, sub_self, add_zero]
  | succ n ih =>
    have hs : (∑ i ∈ range (n + 1), ((n + 1 - i : ℕ) : ℤ) * q ^ i) =
        q * (∑ i ∈ range n, ((n - i : ℕ) : ℤ) * q ^ i) + (n + 1 : ℕ) := by
      rw [sum_range_succ']
      simp only [Nat.add_sub_add_right, Nat.sub_zero, pow_zero, mul_one]
      rw [mul_sum]
      congr 1
      apply sum_congr rfl
      intro i _
      rw [pow_succ]
      ring
    rw [hs]
    calc
      _ = q * ((q - 1) ^ 2 * (∑ i ∈ range n, ((n - i : ℕ) : ℤ) * q ^ i)) +
          (q - 1) ^ 2 * (n + 1 : ℕ) := by ring
      _ = _ := by rw [ih, pow_succ q (n + 1)]; push_cast; ring

theorem weighted_geometric_prefix_sum_le {q : ℤ} (hq : 1 ≤ q) (n : ℕ) :
    (q - 1) ^ 2 * (∑ i ∈ range n, ((n - i : ℕ) : ℤ) * q ^ i) ≤ q ^ (n + 1) := by
  rw [weighted_geometric_prefix_sum]
  have hm := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg (n + 1) : (0 : ℤ) ≤ (n + 1 : ℕ))
  push_cast at hm ⊢
  nlinarith only [hm]

/-- If removing `n` prefixes lowers every retained exponent by at least `n`,
their total weight has the sharp double-geometric upper bound. -/
theorem prefix_weight_le_of_exponent_gap {q : ℤ} (hq : 1 ≤ q)
    (b m E : ℕ) (A : ℕ → Finset (ℕ × Fin b))
    (hgap : ∀ n ∈ Icc 1 m, ∀ x ∈ A n, x.1 + n ≤ E) :
    (q - 1) ^ 2 * (∑ n ∈ Icc 1 m, ∑ x ∈ A n, q ^ x.1) ≤
      (b : ℤ) * q ^ (E + 1) := by
  let B : Finset (ℕ × Fin b) := (range E).product univ
  have hsub (n : ℕ) (hn : n ∈ Icc 1 m) : A n ⊆ B := by
    intro x hx
    have hg := hgap n hn x hx
    have hn1 := (mem_Icc.mp hn).1
    exact mem_product.mpr ⟨mem_range.mpr (by omega), mem_univ _⟩
  have he (n : ℕ) (hn : n ∈ Icc 1 m) :
      (∑ x ∈ A n, q ^ x.1) = ∑ x ∈ B, if x ∈ A n then q ^ x.1 else 0 := by
    rw [← sum_filter]
    congr 1
    ext x
    simp only [mem_filter]
    exact ⟨fun hx => ⟨hsub n hn hx, hx⟩, fun hx => hx.2⟩
  have hcount (x : ℕ × Fin b) :
      ((Icc 1 m).filter fun n => x ∈ A n).card ≤ E - x.1 := by
    have hS : (Icc 1 m).filter (fun n => x ∈ A n) ⊆ Icc 1 (E - x.1) := by
      intro n hn
      obtain ⟨hn, hx⟩ := mem_filter.mp hn
      have hg := hgap n hn x hx
      exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1, by omega⟩
    have hc := card_le_card hS
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hc
  have hweight : (∑ n ∈ Icc 1 m, ∑ x ∈ A n, q ^ x.1) ≤
      (b : ℤ) * ∑ i ∈ range E, ((E - i : ℕ) : ℤ) * q ^ i := by
    calc
      _ = ∑ n ∈ Icc 1 m, ∑ x ∈ B, if x ∈ A n then q ^ x.1 else 0 :=
        sum_congr rfl he
      _ = ∑ x ∈ B, ∑ n ∈ Icc 1 m, if x ∈ A n then q ^ x.1 else 0 := sum_comm
      _ ≤ ∑ x ∈ B, ((E - x.1 : ℕ) : ℤ) * q ^ x.1 := by
        apply sum_le_sum
        intro x _
        rw [← sum_filter, sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount x)
          (pow_nonneg (by omega : 0 ≤ q) _)
      _ = _ := by
        simp only [B, product_eq_sprod, sum_product, sum_const, card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_sum]
  have hscaled := mul_le_mul_of_nonneg_left hweight (sq_nonneg (q - 1))
  have hgeom := mul_le_mul_of_nonneg_left (weighted_geometric_prefix_sum_le hq E)
    (Nat.cast_nonneg b : (0 : ℤ) ≤ b)
  nlinarith only [hscaled, hgeom]

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.prefix_weight_le_of_exponent_gap
