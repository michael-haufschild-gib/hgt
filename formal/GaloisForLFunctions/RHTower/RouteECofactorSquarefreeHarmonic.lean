import GaloisForLFunctions.RHTower.Sieve.SquarefreeWindowCount
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDensityBound
import GaloisForLFunctions.RHTower.Sieve.CoprimeSignDensity
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# The unsigned squarefree harmonic estimates

The cofactor card quotes two classical estimates: `∑_{n ≤ T} μ²(n) n^{-1/2} ≍ √T` for its `(7)` and
`∑_{n ≤ T} μ²(n)/n ≍ log T` for its `(9)`.  Both follow from the corpus's own squarefree window
count with no further input — the first by a single comparison of the weight against its value at
the top of the range, the second by summing that count over dyadic blocks.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- The reciprocal square roots telescope. -/
theorem sum_sqrtInv_le (T : ℕ) :
    ∑ n ∈ Finset.Icc 1 T, (Real.sqrt n)⁻¹ ≤ 2 * Real.sqrt T := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ T + 1)]
      have hT0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg _
      have hs : Real.sqrt T ≤ Real.sqrt ((T : ℝ) + 1) :=
        Real.sqrt_le_sqrt (by linarith)
      have hs1 : (0 : ℝ) < Real.sqrt ((T : ℝ) + 1) := Real.sqrt_pos.2 (by linarith)
      have hsq : Real.sqrt ((T : ℝ) + 1) * Real.sqrt ((T : ℝ) + 1) = (T : ℝ) + 1 :=
        Real.mul_self_sqrt (by linarith)
      have hsq0 : Real.sqrt (T : ℝ) * Real.sqrt (T : ℝ) = (T : ℝ) :=
        Real.mul_self_sqrt hT0
      have hstep : (Real.sqrt ((T : ℕ) + 1 : ℕ))⁻¹
          ≤ 2 * Real.sqrt ((T + 1 : ℕ) : ℝ) - 2 * Real.sqrt T := by
        have hcast : (((T + 1 : ℕ)) : ℝ) = (T : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        rw [inv_le_iff_one_le_mul₀ hs1]
        nlinarith [hsq, hsq0, hs, hs1, Real.sqrt_nonneg (T : ℝ)]
      have hcast : (((T + 1 : ℕ)) : ℝ) = (T : ℝ) + 1 := by push_cast; ring
      linarith [ih, hstep]

/-- **The square-root-weighted squarefree sum, from above.** -/
theorem sum_sqrtInv_squarefree_le (T : ℕ) :
    ∑ n ∈ Finset.Icc 1 T, ((moebius n : ℤ) : ℝ) ^ 2 * (Real.sqrt n)⁻¹
      ≤ 2 * Real.sqrt T := by
  refine le_trans (Finset.sum_le_sum fun n _ => ?_) (sum_sqrtInv_le T)
  have hmu : ((moebius n : ℤ) : ℝ) ^ 2 ≤ 1 := by
    have h := moebius_apply_of_squarefree (n := n)
    rcases eq_or_ne (moebius n) 0 with h0 | h0
    · rw [h0]
      norm_num
    · have hone : moebius n = 1 ∨ moebius n = -1 := by
        have := ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp h0
        exact this
      rcases hone with h1 | h1 <;> rw [h1] <;> norm_num
  have hinv : (0 : ℝ) ≤ (Real.sqrt n)⁻¹ := by positivity
  nlinarith [hmu, hinv]

/-- **The square-root-weighted squarefree sum, from below.**  This is the card's `(7)` main term. -/
theorem sum_sqrtInv_squarefree_ge {T R : ℕ} (hT : 1 ≤ T) (hR : 1 ≤ R) (hRT : T ≤ R ^ 2) :
    squarefreeDensity * Real.sqrt T - ((R : ℝ) + (T : ℝ) / (R : ℝ)) / Real.sqrt T
      ≤ ∑ n ∈ Finset.Icc 1 T, ((moebius n : ℤ) : ℝ) ^ 2 * (Real.sqrt n)⁻¹ := by
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hsT : (0 : ℝ) < Real.sqrt T := Real.sqrt_pos.2 hT0
  have hsqT : Real.sqrt T * Real.sqrt T = (T : ℝ) := Real.mul_self_sqrt hT0.le
  -- the count of squarefree integers below `T`
  have hcount := abs_window_squarefree_sub_le (t := 0) (L := T) hR
    (by rw [Nat.zero_add]; exact hRT)
  have hIoc : Finset.Ioc 0 (0 + T) = Finset.Icc 1 T := by
    rw [Nat.zero_add]
    ext n
    rw [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hIoc] at hcount
  have hlow : (T : ℝ) * squarefreeDensity - ((R : ℝ) + (T : ℝ) / (R : ℝ))
      ≤ ∑ n ∈ Finset.Icc 1 T, ((moebius n : ℤ) : ℝ) ^ 2 := by
    have := (abs_le.mp hcount).1
    linarith
  -- each weight is at least its value at the top of the range
  have hterm : ∀ n ∈ Finset.Icc 1 T,
      ((moebius n : ℤ) : ℝ) ^ 2 * (Real.sqrt T)⁻¹
        ≤ ((moebius n : ℤ) : ℝ) ^ 2 * (Real.sqrt n)⁻¹ := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have hnT : (n : ℝ) ≤ (T : ℝ) := by exact_mod_cast hn.2
    have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hn0
    have hle : Real.sqrt n ≤ Real.sqrt T := Real.sqrt_le_sqrt hnT
    have hinv : (Real.sqrt T)⁻¹ ≤ (Real.sqrt n)⁻¹ := inv_anti₀ hsn hle
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  have hsum : (∑ n ∈ Finset.Icc 1 T, ((moebius n : ℤ) : ℝ) ^ 2) * (Real.sqrt T)⁻¹
      ≤ ∑ n ∈ Finset.Icc 1 T, ((moebius n : ℤ) : ℝ) ^ 2 * (Real.sqrt n)⁻¹ := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hterm
  have hmul : ((T : ℝ) * squarefreeDensity - ((R : ℝ) + (T : ℝ) / (R : ℝ))) * (Real.sqrt T)⁻¹
      ≤ (∑ n ∈ Finset.Icc 1 T, ((moebius n : ℤ) : ℝ) ^ 2) * (Real.sqrt T)⁻¹ :=
    mul_le_mul_of_nonneg_right hlow (by positivity)
  have hval : ((T : ℝ) * squarefreeDensity - ((R : ℝ) + (T : ℝ) / (R : ℝ))) * (Real.sqrt T)⁻¹
      = squarefreeDensity * Real.sqrt T - ((R : ℝ) + (T : ℝ) / (R : ℝ)) / Real.sqrt T := by
    have h1 : (T : ℝ) * squarefreeDensity * (Real.sqrt T)⁻¹
        = squarefreeDensity * Real.sqrt T := by
      rw [inv_eq_one_div, mul_one_div, eq_comm, eq_div_iff (ne_of_gt hsT)]
      linear_combination squarefreeDensity * hsqT
    have h2 : ((R : ℝ) + (T : ℝ) / (R : ℝ)) * (Real.sqrt T)⁻¹
        = ((R : ℝ) + (T : ℝ) / (R : ℝ)) / Real.sqrt T :=
      (div_eq_mul_inv _ _).symm
    rw [sub_mul, h1, h2]
  linarith [hmul, hval, hsum]

/-! ## The logarithmic weight of `(9)` -/

/-- **One dyadic block of the squarefree harmonic sum.** -/
theorem sum_inv_squarefree_block_ge {j R : ℕ} (hR : 1 ≤ R) (hRj : 2 ^ j + 2 ^ j ≤ R ^ 2) :
    (((2 : ℝ) ^ j * squarefreeDensity - ((R : ℝ) + ((2 : ℝ) ^ j) / (R : ℝ)))) / (2 : ℝ) ^ (j + 1)
      ≤ ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ) := by
  classical
  have hcount := abs_window_squarefree_sub_le (t := 2 ^ j) (L := 2 ^ j) hR hRj
  have hcast : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
  have hidx : (2 : ℕ) ^ j + 2 ^ j = 2 ^ (j + 1) := by ring
  rw [hidx, hcast] at hcount
  have hlow : (2 : ℝ) ^ j * squarefreeDensity - ((R : ℝ) + ((2 : ℝ) ^ j) / (R : ℝ))
      ≤ ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), ((moebius n : ℤ) : ℝ) ^ 2 := by
    have := (abs_le.mp hcount).1
    linarith
  have hp0 : (0 : ℝ) < (2 : ℝ) ^ (j + 1) := by positivity
  have hterm : ∀ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)),
      ((moebius n : ℤ) : ℝ) ^ 2 / (2 : ℝ) ^ (j + 1) ≤ ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by
        have : 0 < 2 ^ j := Nat.two_pow_pos j
        omega
      exact_mod_cast this
    have hnle : (n : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
      have hc : ((2 ^ (j + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (j + 1) := by push_cast; ring
      have := hn.2
      have : ((n : ℕ) : ℝ) ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast this
      rwa [hc] at this
    exact div_le_div_of_nonneg_left (by positivity) hn0 hnle
  have hsum : (∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), ((moebius n : ℤ) : ℝ) ^ 2)
        / (2 : ℝ) ^ (j + 1)
      ≤ ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum hterm
  exact le_trans (div_le_div_of_nonneg_right hlow hp0.le) hsum

/-- **Every dyadic block above `2^8` carries a quarter of the squarefree density.** -/
theorem sum_inv_squarefree_block_ge_const {j : ℕ} (hj : 8 ≤ j) :
    squarefreeDensity / 4
      ≤ ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ) := by
  set R : ℕ := 2 ^ (j / 2 + 1) with hRdef
  have hR1 : 1 ≤ R := Nat.one_le_two_pow
  have hRj : 2 ^ j + 2 ^ j ≤ R ^ 2 := by
    rw [hRdef, ← pow_mul, show (2 : ℕ) ^ j + 2 ^ j = 2 ^ (j + 1) by ring]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbase := sum_inv_squarefree_block_ge hR1 hRj
  refine le_trans ?_ hbase
  -- the block's error term is at most `3·2^{j/2}`
  have hRR : (R : ℝ) = (2 : ℝ) ^ (j / 2 + 1) := by
    rw [hRdef]
    push_cast
    ring
  have hhalf : (2 : ℝ) ^ (j / 2) ≤ (2 : ℝ) ^ j := by
    refine pow_le_pow_right₀ (by norm_num) (by omega)
  have hR0 : (0 : ℝ) < (R : ℝ) := by
    rw [hRR]; positivity
  have hquot : ((2 : ℝ) ^ j) / (R : ℝ) ≤ (2 : ℝ) ^ (j / 2) := by
    rw [hRR, div_le_iff₀ (by positivity), ← pow_add]
    refine pow_le_pow_right₀ (by norm_num) (by omega)
  have herr : (R : ℝ) + ((2 : ℝ) ^ j) / (R : ℝ) ≤ 3 * (2 : ℝ) ^ (j / 2) := by
    have hRle : (R : ℝ) ≤ 2 * (2 : ℝ) ^ (j / 2) := by
      rw [hRR, pow_succ]
      ring_nf
      exact le_refl _
    linarith [hquot, hRle]
  -- the main term dominates
  have hD : (0 : ℝ) < squarefreeDensity := squarefreeDensity_pos
  have hDge : (3 : ℝ) / 8 ≤ squarefreeDensity := squarefreeDensity_ge
  have hbig : (16 : ℝ) ≤ (2 : ℝ) ^ (j / 2) := by
    have : (2 : ℝ) ^ (4 : ℕ) ≤ (2 : ℝ) ^ (j / 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this
    linarith
  have hsq : (2 : ℝ) ^ (j / 2) * (2 : ℝ) ^ (j / 2) ≤ (2 : ℝ) ^ j := by
    rw [← pow_add]
    refine pow_le_pow_right₀ (by norm_num) (by omega)
  have hmain : squarefreeDensity / 4 * (2 : ℝ) ^ (j + 1)
      ≤ (2 : ℝ) ^ j * squarefreeDensity - 3 * (2 : ℝ) ^ (j / 2) := by
    have hpow : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by rw [pow_succ]; ring
    rw [hpow]
    have hhalfterm : 3 * (2 : ℝ) ^ (j / 2) ≤ squarefreeDensity / 2 * (2 : ℝ) ^ j := by
      nlinarith [hbig, hsq, hDge, hD, pow_pos (by norm_num : (0:ℝ) < 2) (j / 2)]
    linarith
  have hp0 : (0 : ℝ) < (2 : ℝ) ^ (j + 1) := by positivity
  rw [le_div_iff₀ hp0]
  linarith [hmain, herr]

/-- **The squarefree harmonic sum grows logarithmically.**  This is the card's `(9)` main term. -/
theorem sum_inv_squarefree_ge (J : ℕ) :
    squarefreeDensity / 4 * ((J : ℝ) - 8)
      ≤ ∑ n ∈ Finset.Ioc 0 (2 ^ J), ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ) := by
  classical
  have hD : (0 : ℝ) < squarefreeDensity := squarefreeDensity_pos
  induction J with
  | zero =>
      have hnn : (0 : ℝ) ≤ ∑ n ∈ Finset.Ioc 0 (2 ^ 0), ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ) :=
        Finset.sum_nonneg fun n _ => by positivity
      have : squarefreeDensity / 4 * ((0 : ℝ) - 8) ≤ 0 := by
        nlinarith [hD]
      simpa using le_trans this hnn
  | succ J ih =>
      by_cases hJ : 8 ≤ J
      · have hsplit : (∑ n ∈ Finset.Ioc 0 (2 ^ J), ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ))
            + ∑ n ∈ Finset.Ioc (2 ^ J) (2 ^ (J + 1)), ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ)
            = ∑ n ∈ Finset.Ioc 0 (2 ^ (J + 1)), ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ) :=
          Finset.sum_Ioc_consecutive _ (Nat.zero_le _)
            (Nat.pow_le_pow_right (by norm_num) (by omega))
        have hblock := sum_inv_squarefree_block_ge_const hJ
        push_cast
        linarith [ih, hblock, hsplit]
      · have hnn : (0 : ℝ)
            ≤ ∑ n ∈ Finset.Ioc 0 (2 ^ (J + 1)), ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ) :=
          Finset.sum_nonneg fun n _ => by positivity
        have hJ8 : (J : ℝ) + 1 - 8 ≤ 0 := by
          have : (J : ℝ) ≤ 7 := by
            have : J ≤ 7 := by omega
            exact_mod_cast this
          linarith
        have : squarefreeDensity / 4 * (((J : ℝ) + 1) - 8) ≤ 0 := by nlinarith [hD, hJ8]
        push_cast
        linarith [this, hnn]

/-- **The squarefree harmonic sum, from above.** -/
theorem sum_inv_squarefree_le (T : ℕ) :
    ∑ n ∈ Finset.Icc 1 T, ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ) ≤ 1 + Real.log T := by
  refine le_trans (Finset.sum_le_sum fun n hn => ?_) (sum_Icc_one_div_le_one_add_log T)
  rw [Finset.mem_Icc] at hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
  have hmu : ((moebius n : ℤ) : ℝ) ^ 2 ≤ 1 := by
    rcases eq_or_ne (moebius n) 0 with h0 | h0
    · rw [h0]; norm_num
    · rcases ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp h0 with h1 | h1 <;>
        rw [h1] <;> norm_num
  rw [div_le_div_iff₀ hn0 hn0]
  nlinarith [hmu, hn0]

/-! ## Squarefree integers avoiding a finite set of primes -/

/-- The multiples of `p` below `Y` number at most `Y/p`. -/
theorem card_multiples_le (Y : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    ((((Finset.Icc 1 Y).filter (fun n => p ∣ n)).card : ℕ) : ℝ) ≤ (Y : ℝ) / (p : ℝ) := by
  classical
  have hIoc : Finset.Icc 1 Y = Finset.Ioc 0 Y := by
    ext n
    rw [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIoc, Nat.Ioc_filter_dvd_card_eq_div]
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [le_div_iff₀ hp0]
  have := Nat.div_mul_le_self Y p
  have hcast : (((Y / p : ℕ) * p : ℕ) : ℝ) ≤ ((Y : ℕ) : ℝ) := by exact_mod_cast this
  push_cast at hcast
  linarith

/-- **Squarefree integers below `Y` avoiding a finite set of primes.**  The classical union bound:
the squarefree count minus the multiples of each excluded prime. -/
theorem card_squarefree_avoid_ge {Y : ℕ} (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 1 ≤ p) {R : ℕ}
    (hR : 1 ≤ R) (hRY : Y ≤ R ^ 2) :
    (Y : ℝ) * squarefreeDensity - ((R : ℝ) + (Y : ℝ) / (R : ℝ)) - ∑ p ∈ Q, (Y : ℝ) / (p : ℝ)
      ≤ ((((Finset.Icc 1 Y).filter
          (fun n => Squarefree n ∧ ∀ p ∈ Q, ¬ p ∣ n)).card : ℕ) : ℝ) := by
  classical
  -- the squarefree count
  have hcount := abs_window_squarefree_sub_le (t := 0) (L := Y) hR (by rw [Nat.zero_add]; exact hRY)
  have hIoc : Finset.Ioc 0 (0 + Y) = Finset.Icc 1 Y := by
    rw [Nat.zero_add]
    ext n
    rw [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hIoc] at hcount
  have hsf : ∑ n ∈ Finset.Icc 1 Y, ((moebius n : ℤ) : ℝ) ^ 2
      = (((Finset.Icc 1 Y).filter (fun n => Squarefree n)).card : ℝ) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun n hn => ?_
    by_cases hs : Squarefree n
    · rw [if_pos hs, ArithmeticFunction.moebius_apply_of_squarefree hs]
      rcases Nat.even_or_odd (ArithmeticFunction.cardFactors n) with h | h
      · rw [Even.neg_one_pow h]; norm_num
      · rw [Odd.neg_one_pow h]; norm_num
    · rw [if_neg hs, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
      norm_num
  rw [hsf] at hcount
  have hlow : (Y : ℝ) * squarefreeDensity - ((R : ℝ) + (Y : ℝ) / (R : ℝ))
      ≤ (((Finset.Icc 1 Y).filter (fun n => Squarefree n)).card : ℝ) := by
    have := (abs_le.mp hcount).1
    linarith
  -- the excluded multiples
  have hsplit : (((Finset.Icc 1 Y).filter (fun n => Squarefree n)).card : ℝ)
      ≤ ((((Finset.Icc 1 Y).filter (fun n => Squarefree n ∧ ∀ p ∈ Q, ¬ p ∣ n)).card : ℕ) : ℝ)
        + ∑ p ∈ Q, ((((Finset.Icc 1 Y).filter (fun n => p ∣ n)).card : ℕ) : ℝ) := by
    have hsub : (Finset.Icc 1 Y).filter (fun n => Squarefree n)
        ⊆ ((Finset.Icc 1 Y).filter (fun n => Squarefree n ∧ ∀ p ∈ Q, ¬ p ∣ n))
          ∪ Q.biUnion (fun p => (Finset.Icc 1 Y).filter (fun n => p ∣ n)) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      by_cases hall : ∀ p ∈ Q, ¬ p ∣ n
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hn.1, hn.2, hall⟩)
      · push Not at hall
        obtain ⟨p, hpQ, hpn⟩ := hall
        refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨p, hpQ, ?_⟩)
        exact Finset.mem_filter.2 ⟨hn.1, hpn⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le
      ((Finset.Icc 1 Y).filter (fun n => Squarefree n ∧ ∀ p ∈ Q, ¬ p ∣ n))
      (Q.biUnion (fun p => (Finset.Icc 1 Y).filter (fun n => p ∣ n)))
    have h3 := Finset.card_biUnion_le (s := Q)
      (t := fun p => (Finset.Icc 1 Y).filter (fun n => p ∣ n))
    have hnat : ((Finset.Icc 1 Y).filter (fun n => Squarefree n)).card
        ≤ ((Finset.Icc 1 Y).filter (fun n => Squarefree n ∧ ∀ p ∈ Q, ¬ p ∣ n)).card
          + ∑ p ∈ Q, ((Finset.Icc 1 Y).filter (fun n => p ∣ n)).card := by omega
    have := (Nat.cast_le (α := ℝ)).2 hnat
    push_cast at this
    exact this
  have hmult : ∑ p ∈ Q, ((((Finset.Icc 1 Y).filter (fun n => p ∣ n)).card : ℕ) : ℝ)
      ≤ ∑ p ∈ Q, (Y : ℝ) / (p : ℝ) :=
    Finset.sum_le_sum fun p hp => card_multiples_le Y (hQ p hp)
  linarith [hlow, hsplit, hmult]

/-- **The union bound, against any set containing the surviving integers.**  Stated without a
`Finset.filter` in the conclusion, so that a caller may substitute its own description of the
surviving set. -/
theorem card_squarefree_avoid_ge_of_subset {Y : ℕ} (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 1 ≤ p) {R : ℕ}
    (hR : 1 ≤ R) (hRY : Y ≤ R ^ 2) (S : Finset ℕ)
    (hS : ∀ n ∈ Finset.Icc 1 Y, Squarefree n → (∀ p ∈ Q, ¬ p ∣ n) → n ∈ S) :
    (Y : ℝ) * squarefreeDensity - ((R : ℝ) + (Y : ℝ) / (R : ℝ)) - ∑ p ∈ Q, (Y : ℝ) / (p : ℝ)
      ≤ ((S.card : ℕ) : ℝ) := by
  classical
  refine le_trans (card_squarefree_avoid_ge Q hQ hR hRY) ?_
  refine Nat.cast_le.2 (Finset.card_le_card ?_)
  intro n hn
  rw [Finset.mem_filter] at hn
  exact hS n hn.1 hn.2.1 hn.2.2

end RHTower.Sieve
