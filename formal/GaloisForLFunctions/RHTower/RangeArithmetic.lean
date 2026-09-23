/-
Range arithmetic for the RHTower spur estimates.

These lemmas are deliberately independent of the multiplier construction.  They
are the reusable bookkeeping layer that converts the paper range `j^(3 : ℕ) <= d^(2 : ℕ)`
into the half-range and absorbs high-tail powers of `j/d`.
-/
import Mathlib

namespace RHTower

noncomputable section

/-- Cube-square range implies the half-range needed by the elementary log estimate.

This is the integer form of `j <= d^(2/3) => 2*j <= d` once `d >= 8`. -/
theorem two_mul_le_of_cube_le_square {j d : ℕ} (hjd : j ^ (3 : ℕ) ≤ d ^ (2 : ℕ)) (hd : 8 ≤ d) :
    2 * j ≤ d := by
  by_contra h
  have hltNat : d < 2 * j := Nat.lt_of_not_ge h
  have hlt : (d : ℝ) < 2 * (j : ℝ) := by exact_mod_cast hltNat
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 8) hd)
  have hjdR : (j : ℝ) ^ (3 : ℕ) ≤ (d : ℝ) ^ (2 : ℕ) := by exact_mod_cast hjd
  have hcube_lt : (d : ℝ) ^ (3 : ℕ) < (2 * (j : ℝ)) ^ (3 : ℕ) :=
    pow_lt_pow_left₀ hlt (le_of_lt hdpos) (by norm_num)
  have hbound : (d : ℝ) ^ (3 : ℕ) < 8 * (d : ℝ) ^ (2 : ℕ) := by
    nlinarith [hcube_lt, hjdR]
  have hd8R : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2pos : 0 < (d : ℝ) ^ (2 : ℕ) := pow_pos hdpos 2
  nlinarith

/-- Arithmetic weight conversion for one high-tail monomial.

Once `j <= d`, the `r` discarded powers contribute `(j/d)^r <= 1`, so a term
with base exponent `P + q` and `q <= P` is bounded by `j^(2P)`. -/
theorem tail_monomial_weight_le_of_le (P q r : ℕ) {j d : ℕ}
    (hj : 1 ≤ j) (hjd : j ≤ d) (hq : q ≤ P) :
    (j : ℝ) ^ (P + r + q) * |((d : ℝ)⁻¹)| ^ r ≤ (j : ℝ) ^ (2 * P) := by
  have hjposNat : 0 < j := lt_of_lt_of_le Nat.zero_lt_one hj
  have hdposNat : 0 < d := lt_of_lt_of_le hjposNat hjd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdposNat
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hratio_le : (j : ℝ) * |((d : ℝ)⁻¹)| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (le_of_lt hdR))]
    rw [mul_inv_le_iff₀ hdR]
    have hjdR : (j : ℝ) ≤ d := by exact_mod_cast hjd
    nlinarith
  have hratio_nonneg : 0 ≤ (j : ℝ) * |((d : ℝ)⁻¹)| := by positivity
  have hratio_pow : ((j : ℝ) * |((d : ℝ)⁻¹)|) ^ r ≤ 1 :=
    pow_le_one₀ hratio_nonneg hratio_le
  have hratio_pow_nonneg : 0 ≤ ((j : ℝ) * |((d : ℝ)⁻¹)|) ^ r :=
    pow_nonneg hratio_nonneg r
  have hlead : (j : ℝ) ^ (P + q) ≤ (j : ℝ) ^ (2 * P) := by
    exact pow_le_pow_right₀ hjR (by omega)
  have htarget_nonneg : 0 ≤ (j : ℝ) ^ (2 * P) := by positivity
  calc
    (j : ℝ) ^ (P + r + q) * |((d : ℝ)⁻¹)| ^ r
        = (j : ℝ) ^ (P + q) * (((j : ℝ) * |((d : ℝ)⁻¹)|) ^ r) := by
          have hsum : P + r + q = P + q + r := by omega
          rw [hsum, pow_add, mul_pow]
          ring
    _ ≤ (j : ℝ) ^ (2 * P) * (((j : ℝ) * |((d : ℝ)⁻¹)|) ^ r) := by
          exact mul_le_mul_of_nonneg_right hlead hratio_pow_nonneg
    _ ≤ (j : ℝ) ^ (2 * P) * 1 := by
          exact mul_le_mul_of_nonneg_left hratio_pow htarget_nonneg
    _ = (j : ℝ) ^ (2 * P) := by ring

/-- Paper-range form of `tail_monomial_weight_le_of_le`. -/
theorem tail_monomial_weight_le_cube_square_order (P q r : ℕ) {j d : ℕ}
    (hd : 8 ≤ d) (hj : 1 ≤ j) (hjd : j ^ (3 : ℕ) ≤ d ^ (2 : ℕ)) (hq : q ≤ P) :
    (j : ℝ) ^ (P + r + q) * |((d : ℝ)⁻¹)| ^ r ≤ (j : ℝ) ^ (2 * P) := by
  have hhalf : 2 * j ≤ d := two_mul_le_of_cube_le_square hjd hd
  have hjle : j ≤ d := by omega
  exact tail_monomial_weight_le_of_le P q r hj hjle hq

end

end RHTower
