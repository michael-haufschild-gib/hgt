import GaloisForLFunctions.RHTower.ThueMorseMellinFlatness

/-!
# Two-endpoint Prouhet packets for the finite theta-tail seam

The finite Thue--Morse polynomial has an arbitrarily high-order zero at the translation
character `X = 1`.  Multiplying it by one affine factor leaves that zero intact while allowing
two independent value normalizations.  For the theta-tail Haar seam the distinguished values are
`q = 2⁻¹ᐟ²` and `q⁻¹ = 2¹ᐟ²`:

* the first value normalizes a signed combination of Haar prefixes to have total weight one;
* the second value controls the elementary half-exponential square;
* the zero at one annihilates every finite translation polynomial below the chosen Prouhet depth.

This module proves the exact polynomial algebra.  No Xi value, divisor datum, limiting measure, or
sign condition occurs.
-/

open Polynomial

namespace RHTower

noncomputable section

/-- The finite Thue--Morse product with real coefficients. -/
def thueMorseRealPolynomial (m : ℕ) : ℝ[X] :=
  (thueMorsePolynomial m).map (Int.castRingHom ℝ)

/-- Real evaluation is the literal finite binary product. -/
theorem eval_thueMorseRealPolynomial (m : ℕ) (q : ℝ) :
    (thueMorseRealPolynomial m).eval q =
      ∏ k ∈ Finset.range m, (1 - q ^ (2 ^ k)) := by
  rw [thueMorseRealPolynomial, eval_map]
  rw [thueMorsePolynomial, eval₂_finsetProd]
  apply Finset.prod_congr rfl
  intro k _hk
  simp

/-- The binary product is positive between its endpoint characters `0` and `1`. -/
theorem eval_thueMorseRealPolynomial_pos
    (m : ℕ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < (thueMorseRealPolynomial m).eval q := by
  rw [eval_thueMorseRealPolynomial]
  apply Finset.prod_pos
  intro k _hk
  have hpow : q ^ (2 ^ k) < 1 := by
    exact pow_lt_one₀ hq0.le hq1 (by positivity)
  linarith

/-- The binary product is nonzero beyond the endpoint character `1`. -/
theorem eval_thueMorseRealPolynomial_ne_zero_of_one_lt
    (m : ℕ) {q : ℝ} (hq : 1 < q) :
    (thueMorseRealPolynomial m).eval q ≠ 0 := by
  rw [eval_thueMorseRealPolynomial]
  apply Finset.prod_ne_zero_iff.mpr
  intro k _hk
  have hpow : 1 < q ^ (2 ^ k) := one_lt_pow₀ hq (by positivity)
  linarith

theorem thueMorseRealPolynomial_succ (m : ℕ) :
    thueMorseRealPolynomial (m + 1) =
      thueMorseRealPolynomial m * (1 - X ^ (2 ^ m)) := by
  rw [thueMorseRealPolynomial, thueMorsePolynomial_succ]
  simp [thueMorseRealPolynomial]

private theorem X_sub_one_dvd_one_sub_X_pow (n : ℕ) :
    (X - 1 : ℝ[X]) ∣ 1 - X ^ n := by
  refine ⟨-(∑ i ∈ Finset.range n, X ^ i), ?_⟩
  rw [mul_neg, mul_geom_sum]
  ring

/-- The depth-`m` binary product has a zero of order at least `m` at `X = 1`. -/
theorem X_sub_one_pow_dvd_thueMorseRealPolynomial (m : ℕ) :
    (X - 1 : ℝ[X]) ^ m ∣ thueMorseRealPolynomial m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show m + 1 = Nat.succ m by rfl, thueMorseRealPolynomial_succ]
      rw [pow_succ]
      exact mul_dvd_mul ih (X_sub_one_dvd_one_sub_X_pow (2 ^ m))

/-- The affine interpolation of a depth-`m` Prouhet symbol at two prescribed characters.
The first value is normalized to one and the second to `τ`. -/
def twoEndpointProuhetPolynomial (m : ℕ) (q r τ : ℝ) : ℝ[X] :=
  let B := thueMorseRealPolynomial m
  let u := (B.eval q)⁻¹
  let v := τ * (B.eval r)⁻¹
  let β := (v - u) / (r - q)
  let α := u - β * q
  B * (C α + C β * X)

/-- The left endpoint normalization is exact. -/
theorem twoEndpointProuhetPolynomial_eval_left
    (m : ℕ) {q r τ : ℝ}
    (hBq : (thueMorseRealPolynomial m).eval q ≠ 0) :
    (twoEndpointProuhetPolynomial m q r τ).eval q = 1 := by
  let B := thueMorseRealPolynomial m
  let u := (B.eval q)⁻¹
  let v := τ * (B.eval r)⁻¹
  let β := (v - u) / (r - q)
  let α := u - β * q
  have hlin : α + β * q = u := by simp only [α]; ring
  have hunit : B.eval q * u = 1 := by
    simpa only [B, u] using mul_inv_cancel₀ hBq
  change (B * (C α + C β * X)).eval q = 1
  rw [eval_mul, eval_add, eval_C, eval_mul, eval_C, eval_X, hlin, hunit]

/-- The right endpoint normalization is exact. -/
theorem twoEndpointProuhetPolynomial_eval_right
    (m : ℕ) {q r τ : ℝ}
    (hBr : (thueMorseRealPolynomial m).eval r ≠ 0)
    (hsep : r - q ≠ 0) :
    (twoEndpointProuhetPolynomial m q r τ).eval r = τ := by
  let B := thueMorseRealPolynomial m
  let u := (B.eval q)⁻¹
  let v := τ * (B.eval r)⁻¹
  let β := (v - u) / (r - q)
  let α := u - β * q
  have hlin : α + β * r = v := by
    simp only [α, β]
    field_simp [hsep]
    ring
  have htarget : B.eval r * v = τ := by
    simp only [v, inv_eq_one_div]
    calc
      B.eval r * (τ * (1 / B.eval r)) = τ * (B.eval r / B.eval r) := by ring
      _ = τ := by rw [div_self (by simpa only [B] using hBr), mul_one]
  change (B * (C α + C β * X)).eval r = τ
  rw [eval_mul, eval_add, eval_C, eval_mul, eval_C, eval_X, hlin, htarget]

/-- The affine endpoint interpolation preserves the entire Prouhet zero at one. -/
theorem X_sub_one_pow_dvd_twoEndpointProuhetPolynomial
    (m : ℕ) (q r τ : ℝ) :
    (X - 1 : ℝ[X]) ^ m ∣ twoEndpointProuhetPolynomial m q r τ := by
  exact dvd_mul_of_dvd_left (X_sub_one_pow_dvd_thueMorseRealPolynomial m) _

end

end RHTower
