import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCountEstimate
import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.NormCollisionAmplification
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Ternary carries in a positive-generator model

The odd-prime system with extra labels of norms three and four satisfies
2*(N(n)+N(floor(n/2))) + s₃(n) = 3*n. Its count error is therefore governed
by ternary digit sums along dyadic dilations. Ternary repdigits force signed
logarithmic deficits at arbitrarily large thresholds.
-/

noncomputable section

open scoped BigOperators
namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount

/-- The odd-integer count depends only on the integer part of its endpoint. -/
private theorem odd_count_floor {X : ℝ} (hX : 0 ≤ X) :
    (oddIntegers X).card = (⌊X⌋₊ + 1) / 2 := by
  rw [card_oddIntegers, show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl,
    Nat.floor_div_natCast, Nat.floor_add_one hX]

/-- Two adjacent dyadic scales count all integers except the multiples of four. -/
private theorem odd_pair_telescope_step {X : ℝ} (hX : 0 ≤ X) :
    (oddIntegers X).card + (oddIntegers (X / 2)).card + ⌊X / 4⌋₊ = ⌊X⌋₊ := by
  rw [odd_count_floor hX, odd_count_floor (by positivity)]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl, Nat.floor_div_natCast,
    show (4 : ℝ) = ((4 : ℕ) : ℝ) from rfl, Nat.floor_div_natCast]
  omega

/-- Summing the odd-pair identity over powers of four leaves one terminal floor. -/
private theorem odd_power_telescope {X : ℝ} (hX : 0 ≤ X) (B : ℕ) :
    (∑ b ∈ Finset.range (B + 1), (oddIntegers (X / (4 : ℝ) ^ b)).card) +
      (∑ b ∈ Finset.range (B + 1), (oddIntegers ((X / 2) / (4 : ℝ) ^ b)).card) +
      ⌊X / (4 : ℝ) ^ (B + 1)⌋₊ = ⌊X⌋₊ := by
  induction B with
  | zero => simpa using odd_pair_telescope_step hX
  | succ B ih =>
    rw [Finset.sum_range_succ _ (B + 1), Finset.sum_range_succ _ (B + 1)]
    have hp := odd_pair_telescope_step (X := X / (4 : ℝ) ^ (B + 1)) (by positivity)
    have he : (X / (4 : ℝ) ^ (B + 1)) / 2 = (X / 2) / (4 : ℝ) ^ (B + 1) := by ring
    have ht : (X / (4 : ℝ) ^ (B + 1)) / 4 = X / (4 : ℝ) ^ (B + 1 + 1) := by
      simp only [pow_succ, div_mul_eq_div_div]
    rw [he, ht] at hp
    omega

/-- Adding the count at X and X/2 telescopes the norm-four exponent. -/
theorem count_add_half_eq_floor_sum {X : ℝ} (hX : 0 ≤ X) (A B : ℕ)
    (hA : X < (3 : ℝ) ^ (A + 1)) (hB : X < (4 : ℝ) ^ (B + 1)) :
    system.countBall X + system.countBall (X / 2) =
      ∑ a ∈ Finset.range (A + 1), ⌊X / (3 : ℝ) ^ a⌋₊ := by
  have hx2 : X / 2 ≤ X := by linarith only [hX]
  rw [countBall_eq_rectangle_sum hX A B hA hB,
    countBall_eq_rectangle_sum (by positivity : 0 ≤ X / 2) A B
      (hx2.trans_lt hA) (hx2.trans_lt hB), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  -- The outer norm-three exponent remains after the norm-four telescope.
  have hp := odd_power_telescope (X := X / (3 : ℝ) ^ a) (by positivity) B
  have hcut : X / (3 : ℝ) ^ a < (4 : ℝ) ^ (B + 1) := by
    have hpow : (1 : ℝ) ≤ (3 : ℝ) ^ a := one_le_pow₀ (by norm_num)
    have hdiv : X / (3 : ℝ) ^ a ≤ X := by
      apply (div_le_iff₀ (by positivity : 0 < (3 : ℝ) ^ a)).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hX
    exact hdiv.trans_lt hB
  have hzero : ⌊X / (3 : ℝ) ^ a / (4 : ℝ) ^ (B + 1)⌋₊ = 0 := by
    apply Nat.floor_eq_zero.mpr
    exact (div_lt_one (by positivity : 0 < (4 : ℝ) ^ (B + 1))).mpr hcut
  rw [hzero, add_zero] at hp
  simp only [div_mul_eq_div_div]
  have he : (X / 2) / (3 : ℝ) ^ a = (X / (3 : ℝ) ^ a) / 2 := by ring
  rw [he]
  exact hp

/-- An integer-norm system has a constant count between consecutive integer thresholds. -/
private theorem countBall_eq_floor (B : RHTower.BeurlingSystem)
    (h : GaloisForLFunctions.RigidArithmeticOfCuts.HasIntegerNorms B)
    {X : ℝ} (hX : 0 ≤ X) : B.countBall X = B.countBall ⌊X⌋₊ := by
  unfold RHTower.BeurlingSystem.countBall
  congr 1
  ext g
  obtain ⟨n, _, hn⟩ :=
    GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.exists_nat_intNorm B h g
  simp only [Set.mem_setOf_eq, hn]
  constructor
  · intro hle
    exact_mod_cast Nat.le_floor hle
  · intro hle
    exact hle.trans (Nat.floor_le hX)

/-- The dyadic count sum is determined exactly by the ternary digit sum. -/
theorem count_add_half_digit_sum (n : ℕ) :
    2 * (system.countBall n + system.countBall ((n / 2 : ℕ) : ℝ)) +
      (Nat.digits 3 n).sum = 3 * n := by
  let A := Nat.log 3 n + 1
  let B := Nat.log 4 n
  have hA : (n : ℝ) < (3 : ℝ) ^ (A + 1) := by
    have hn := Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) n
    have he : 3 ^ (Nat.log 3 n + 1) ≤ 3 ^ (A + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by dsimp only [A]; omega)
    exact_mod_cast hn.trans_le he
  have hB : (n : ℝ) < (4 : ℝ) ^ (B + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) n
  have hc := count_add_half_eq_floor_sum (X := (n : ℝ)) (by positivity) A B hA hB
  have hh : system.countBall ((n : ℝ) / 2) = system.countBall ((n / 2 : ℕ) : ℝ) := by
    rw [countBall_eq_floor system hasIntegerNorms (by positivity),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl, Nat.floor_div_eq_div]
  rw [hh] at hc
  have hfloor (a : ℕ) : ⌊(n : ℝ) / (3 : ℝ) ^ a⌋₊ = n / 3 ^ a := by
    rw [show (3 : ℝ) ^ a = ((3 ^ a : ℕ) : ℝ) by
      simp only [Nat.cast_pow, Nat.cast_ofNat], Nat.floor_div_eq_div]
  simp_rw [hfloor] at hc
  rw [Finset.sum_range_succ'] at hc
  simp only [pow_zero, Nat.div_one] at hc
  have hd := Nat.sub_one_mul_sum_log_div_pow_eq_sub_sum_digits (p := 3) n
  have hle := Nat.digit_sum_le 3 n
  change system.countBall n + system.countBall ((n / 2 : ℕ) : ℝ) =
    (∑ k ∈ Finset.range (Nat.log 3 n + 1), n / 3 ^ (k + 1)) + n at hc
  change 2 * (∑ k ∈ Finset.range (Nat.log 3 n + 1), n / 3 ^ (k + 1)) =
    n - (Nat.digits 3 n).sum at hd
  omega

/-- The base-three expansion of 3^k minus one consists of k digits equal to two. -/
private theorem ternary_repdigit_sum (k : ℕ) : (Nat.digits 3 (3 ^ k - 1)).sum = 2 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0 < (3 : ℕ) ^ k := pow_pos (by omega) k
    have he : 3 ^ (k + 1) - 1 = 3 * (3 ^ k - 1) + 2 := by
      rw [pow_succ]
      omega
    rw [he, Nat.digits_def' (by norm_num) (by omega)]
    have hmod : (3 * (3 ^ k - 1) + 2) % 3 = 2 := by omega
    have hdiv : (3 * (3 ^ k - 1) + 2) / 3 = 3 ^ k - 1 := by omega
    rw [hmod, hdiv, List.sum_cons, ih]
    omega

/-- The slope-one discrepancy at a natural threshold. -/
def discrepancy (n : ℕ) : ℝ := (system.countBall n : ℝ) - n

/-- At ternary repdigits, the two dyadic discrepancies sum to minus the digit length. -/
theorem repdigit_discrepancy_sum (k : ℕ) :
    discrepancy (3 ^ k - 1) + discrepancy ((3 ^ k - 1) / 2) = -(k : ℝ) := by
  have hc := count_add_half_digit_sum (3 ^ k - 1)
  rw [ternary_repdigit_sum] at hc
  have hp : (3 : ℕ) ^ k % 2 = 1 := by simp [Nat.pow_mod]
  have he : 2 * ((3 ^ k - 1) / 2) = 3 ^ k - 1 := by omega
  have hcR : (2 : ℝ) * (system.countBall (3 ^ k - 1 : ℕ) +
      (system.countBall (((3 ^ k - 1) / 2 : ℕ) : ℝ) : ℝ)) + 2 * k =
      3 * ((3 ^ k - 1 : ℕ) : ℝ) := by exact_mod_cast hc
  have heR : (2 : ℝ) * (((3 ^ k - 1) / 2 : ℕ) : ℝ) = (3 ^ k - 1 : ℕ) := by
    exact_mod_cast he
  dsimp only [discrepancy]
  linarith only [hcR, heR]

/-- One of the two repdigit thresholds has a deficit of at least half the digit length. -/
theorem repdigit_deficit (k : ℕ) :
    discrepancy (3 ^ k - 1) ≤ -(k : ℝ) / 2 ∨
      discrepancy ((3 ^ k - 1) / 2) ≤ -(k : ℝ) / 2 := by
  have h := repdigit_discrepancy_sum k
  by_cases hh : discrepancy (3 ^ k - 1) ≤ -(k : ℝ) / 2
  · exact Or.inl hh
  · exact Or.inr (by linarith only [h, hh])

/-- Arbitrarily large thresholds have a deficit at least log n divided by twice log three. -/
theorem negative_log_excursions :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      Real.log n / (2 * Real.log 3) ≤ (n : ℝ) - system.countBall n := by
  intro N
  let k := 2 * N + 2
  have hg (j : ℕ) : j + 1 ≤ (3 : ℕ) ^ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ]
      omega
  have hk : 2 * N + 3 ≤ 3 ^ k := hg k
  have hsmall : N + 1 ≤ (3 ^ k - 1) / 2 := by omega
  have hbig : N + 1 ≤ 3 ^ k - 1 := by omega
  have hl : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have finish (n : ℕ) (hn : N + 1 ≤ n) (hupper : n ≤ 3 ^ k)
      (hdef : discrepancy n ≤ -(k : ℝ) / 2) :
      N ≤ n ∧ Real.log n / (2 * Real.log 3) ≤ (n : ℝ) - system.countBall n := by
    refine ⟨by omega, ?_⟩
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog : Real.log n ≤ (k : ℝ) * Real.log 3 := by
      have h := Real.log_le_log hnpos (show (n : ℝ) ≤ ((3 ^ k : ℕ) : ℝ) by
        exact_mod_cast hupper)
      simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h
    have hscale : ((k : ℝ) * Real.log 3) / (2 * Real.log 3) = (k : ℝ) / 2 := by
      field_simp [hl.ne']
    have hratio := div_le_div_of_nonneg_right hlog (by positivity : 0 ≤ 2 * Real.log 3)
    rw [hscale] at hratio
    dsimp only [discrepancy] at hdef
    linarith only [hratio, hdef]
  rcases repdigit_deficit k with h | h
  · exact ⟨3 ^ k - 1, finish _ hbig (Nat.sub_le _ _) h⟩
  · exact ⟨(3 ^ k - 1) / 2, finish _ hsmall
      ((Nat.div_le_self _ _).trans (Nat.sub_le _ _)) h⟩

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount
