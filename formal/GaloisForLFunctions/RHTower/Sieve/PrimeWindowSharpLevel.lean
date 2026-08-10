import GaloisForLFunctions.RHTower.Sieve.PrimeWindowBrunTitchmarsh

/-!
# The prime window count at the fourth-root level

With the sieve level free, it can be taken as a power of the window length, and Brun–Titchmarsh's
error `6z(1 + log z)³` then sits below its own main term.  At the level `z = q^{1/4}` the count of
primes in the unit multiplicative window `(q/e, qe]` is

```text
#{primes p : |log p − log q| < 1} ≤ 700·q/log q + 1 ,
```

against the `q(e − e^{-1}) + 1` integers the window contains.  The saving of the full logarithm is
what the Selberg-sieve route could not produce, because its fibre error `Y²(log z)⁴` caps the level
at `log Y = O(1)`.

Consequence for the almost-diagonal mean value theorem: on a prime support the near-diagonal weight
is `q/log q`, not `q`.  For the von Mangoldt weight `a_q = f(q)(log q)q^{-σ}` the near-diagonal mass
drops from `∑_q (log q)² q^{1-2σ} ≍ (log z)²` to `∑_q (log q) q^{1-2σ} ≍ log z`, a factor `log z`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- `log √√x = (log x)/4`. -/
theorem log_sqrt_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.log (Real.sqrt (Real.sqrt x)) = Real.log x / 4 := by
  rw [Real.log_sqrt (Real.sqrt_nonneg x), Real.log_sqrt hx]
  ring

/-- The fourth root as an exponential. -/
theorem sqrt_sqrt_eq_exp {x : ℝ} (hx : 0 < x) :
    Real.sqrt (Real.sqrt x) = Real.exp (Real.log x / 4) := by
  have h0 : (0 : ℝ) < Real.sqrt (Real.sqrt x) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hx)
  rw [← log_sqrt_sqrt hx.le, Real.exp_log h0]

/-- **The Brun–Titchmarsh error is below its main term at the fourth-root level.**  The inequality
`6(1 + u/4)³u ≤ 610·e^{3u/4}` for `u ≥ 4`, which is what makes `z = q^{1/4}` admissible. -/
theorem poly_le_exp_three_quarters {u : ℝ} (hu : 4 ≤ u) :
    6 * (1 + u / 4) ^ 3 * u ≤ 610 * Real.exp (3 * u / 4) := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have h0 : (0 : ℝ) ≤ 1 + u / 4 := by linarith
  have h1 : (1 : ℝ) + u / 4 ≤ u / 2 := by linarith
  have hcube : (1 + u / 4) ^ 3 ≤ (u / 2) ^ 3 := pow_le_pow_left₀ h0 h1 3
  have hx : (0 : ℝ) ≤ 3 * u / 16 := by linarith
  have hexp : 3 * u / 16 ≤ Real.exp (3 * u / 16) := by
    linarith [Real.add_one_le_exp (3 * u / 16)]
  have hpow : (3 * u / 16) ^ (4 : ℕ) ≤ (Real.exp (3 * u / 16)) ^ (4 : ℕ) :=
    pow_le_pow_left₀ hx hexp 4
  have hsplit : (Real.exp (3 * u / 16)) ^ (4 : ℕ) = Real.exp (3 * u / 4) := by
    rw [← Real.exp_nat_mul]
    norm_num
    ring_nf
  rw [hsplit] at hpow
  have hval : (3 * u / 16) ^ (4 : ℕ) = 81 * u ^ 4 / 65536 := by ring
  rw [hval] at hpow
  have hleft : 6 * (1 + u / 4) ^ 3 * u ≤ 6 * (u / 2) ^ 3 * u := by
    nlinarith [hcube, hu0]
  nlinarith [hleft, hpow]

/-- `e − e⁻¹ < 2.72`. -/
theorem exp_sub_exp_neg_one_lt : Real.exp 1 - Real.exp (-1) < 2.72 := by
  have h1 := Real.exp_one_lt_d9
  have h2 : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
  linarith

/-- **The sharp prime window count.**  The unit multiplicative window around a prime `q` carries at
most `700·q/log q + 1` primes — a full logarithm below the number of integers it contains. -/
theorem logNeighbourCount_le_sharp (s : Finset ℕ) (hs : ∀ m ∈ s, m.Prime) {q : ℕ} (hq : 2 ≤ q) :
    (logNeighbourCount s 1 q : ℝ) ≤ 700 * ((q : ℝ) / Real.log q) + 1 := by
  have hq1 : 1 ≤ q := by omega
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hlogq : (0 : ℝ) < Real.log q := Real.log_pos (by linarith)
  have hs0 : (0 : ℕ) ∉ s := fun h => Nat.not_prime_zero (hs 0 h)
  have hee := exp_sub_exp_neg_one_lt
  rcases le_or_gt 4 (Real.log q) with hbig | hsmall
  · -- Brun–Titchmarsh at the fourth-root level
    have hlogz : Real.log (Real.sqrt (Real.sqrt (q : ℝ))) = Real.log q / 4 :=
      log_sqrt_sqrt hq0.le
    have hzval : Real.sqrt (Real.sqrt (q : ℝ)) = Real.exp (Real.log q / 4) :=
      sqrt_sqrt_eq_exp hq0
    have hz1 : 1 < Real.sqrt (Real.sqrt (q : ℝ)) := by
      rw [hzval]
      linarith [Real.add_one_le_exp (Real.log q / 4)]
    have hbt := logNeighbourCount_le_bt s hs (δ := 1) (by norm_num) hq1 hz1
    rw [hlogz, hzval] at hbt
    -- the error term
    have hpoly := poly_le_exp_three_quarters hbig
    have hexpq : Real.exp (Real.log q) = (q : ℝ) := Real.exp_log hq0
    have hmerge : Real.exp (3 * Real.log q / 4) * Real.exp (Real.log q / 4) = (q : ℝ) := by
      rw [← Real.exp_add, show 3 * Real.log q / 4 + Real.log q / 4 = Real.log q by ring, hexpq]
    have hq4 : (0 : ℝ) < Real.exp (Real.log q / 4) := Real.exp_pos _
    have herr : 6 * Real.exp (Real.log q / 4) * (1 + Real.log q / 4) ^ 3
        ≤ 610 * ((q : ℝ) / Real.log q) := by
      have hrw : (610 : ℝ) * ((q : ℝ) / Real.log q) = (610 * (q : ℝ)) / Real.log q := by ring
      rw [hrw, le_div_iff₀ hlogq]
      have hstep := mul_le_mul_of_nonneg_right hpoly hq4.le
      have hL : 610 * Real.exp (3 * Real.log q / 4) * Real.exp (Real.log q / 4)
          = 610 * (q : ℝ) := by
        rw [mul_assoc, hmerge]
      nlinarith [hstep, hL.le, hL.ge]
    -- the main term
    have hmain : 2 * ((q : ℝ) * (Real.exp 1 - Real.exp (-1)) + 1) / (Real.log q / 4)
        ≤ 26 * ((q : ℝ) / Real.log q) := by
      have hrw1 : 2 * ((q : ℝ) * (Real.exp 1 - Real.exp (-1)) + 1) / (Real.log q / 4)
          = (8 * ((q : ℝ) * (Real.exp 1 - Real.exp (-1)) + 1)) / Real.log q := by
        field_simp
        ring
      have hrw2 : (26 : ℝ) * ((q : ℝ) / Real.log q) = (26 * (q : ℝ)) / Real.log q := by ring
      rw [hrw1, hrw2, div_le_div_iff₀ hlogq hlogq]
      have hstep : 8 * ((q : ℝ) * (Real.exp 1 - Real.exp (-1)) + 1) ≤ 26 * (q : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hee.le hq0.le, hqR]
      nlinarith [mul_le_mul_of_nonneg_right hstep hlogq.le]
    have hqu : (0 : ℝ) ≤ (q : ℝ) / Real.log q := div_nonneg hq0.le hlogq.le
    linarith [hbt, herr, hmain, hqu]
  · -- below the threshold the window bound already suffices
    have hwin := logNeighbourCount_le_window s hs0 (δ := 1) (by norm_num) hq1
    have hbound : (q : ℝ) * (Real.exp 1 - Real.exp (-1)) + 1 ≤ 700 * ((q : ℝ) / Real.log q) + 1 := by
      have hcmp : (175 : ℝ) * (q : ℝ) ≤ 700 * ((q : ℝ) / Real.log q) := by
        have hrw : (700 : ℝ) * ((q : ℝ) / Real.log q) = (700 * (q : ℝ)) / Real.log q := by ring
        rw [hrw, le_div_iff₀ hlogq]
        nlinarith [mul_le_mul_of_nonneg_left hsmall.le
          (show (0 : ℝ) ≤ 175 * (q : ℝ) by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hee.le hq0.le, hcmp, hq0]
    linarith [hwin, hbound]

/-- **The prime-supported mean value theorem, sharp.**  The near-diagonal weight is `q/log q`. -/
theorem integral_Icc_normSq_logPoly_le_prime_sharp (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ m ∈ s, m.Prime) {W : ℝ} (hW : 2 * Real.pi * 1 * W ≤ 1) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ 2)
      ≤ (5 / 4) * ∑ q ∈ s, (700 * ((q : ℝ) / Real.log q) + 1) * ‖a q‖ ^ 2 := by
  refine le_trans (integral_Icc_normSq_logPoly_le_count a s (δ := 1) one_pos hW) ?_
  rw [show (5 : ℝ) / (4 * 1) = 5 / 4 by norm_num]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q hq => ?_) (by norm_num)
  exact mul_le_mul_of_nonneg_right (logNeighbourCount_le_sharp s hs (hs q hq).two_le)
    (by positivity)

end RHTower.Sieve

end
