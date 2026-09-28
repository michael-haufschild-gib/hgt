import GaloisForLFunctions.RHTower.Sieve.MoebiusMultiRangeLowCost
import GaloisForLFunctions.RHTower.Sieve.RamareLadderErrorSharp
import GaloisForLFunctions.RHTower.Sieve.TwoRangeScheduleFacts
import GaloisForLFunctions.RHTower.Sieve.TwoRangeAggregates
import GaloisForLFunctions.RHTower.Sieve.RamareRoughSetSplit

/-!
# The ladder of prime ranges

A single parameter `ν` fixes the whole ladder.  Range `j` has scale exponent `ν_j = ν^{2^j}`
(so `ν_{j+1} = ν_j²` and `log ν_j = 2^j log ν`), base `R_j = ⌈exp(ν_j⁴)⌉`, step ratio
`η_j = e^{-ν}/2^j`, and `L_j = ⌈2ν_j⁵/η_j⌉` steps, so that its top `Q_j` satisfies
`ν_j⁴ + ν_j⁵ ≤ log Q_j ≤ 3ν_j⁵`.  The threshold exponents are `α_j = 1/4 − 1/(8·2^j)`.

The consequences used later: the harmonic mass of range `j` is at least `½·log ν_j`, the number of
steps is at most `3ν_j⁵·2^j·e^ν`, and consecutive ranges satisfy
`log Q_{j+1}/log R_j ≤ 3ν_j⁶`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The scale exponent `ν_j = ν^{2^j}` of range `j`. -/
def rangeLadderNu (ν : ℝ) (j : ℕ) : ℝ := ν ^ (2 ^ j)

/-- The base `⌈exp(ν_j⁴)⌉` of range `j`. -/
def rangeLadderBase (ν : ℝ) (j : ℕ) : ℕ := ⌈Real.exp (rangeLadderNu ν j ^ 4)⌉₊

/-- The base of range `j` as a real number. -/
def rangeLadderR (ν : ℝ) (j : ℕ) : ℝ := (rangeLadderBase ν j : ℝ)

/-- The step ratio `e^{-ν}/2^j` of range `j`. -/
def rangeLadderEta (ν : ℝ) (j : ℕ) : ℝ := Real.exp (-ν) / 2 ^ j

/-- The number of steps `⌈2ν_j⁵/η_j⌉` of range `j`. -/
def rangeLadderSteps (ν : ℝ) (j : ℕ) : ℕ := ⌈2 * rangeLadderNu ν j ^ 5 / rangeLadderEta ν j⌉₊

/-- The top `R_j(1+η_j)^{L_j}` of range `j`. -/
def rangeLadderTopReal (ν : ℝ) (j : ℕ) : ℝ := rangeLadderR ν j * (1 + rangeLadderEta ν j) ^ rangeLadderSteps ν j

/-- The integer top of range `j`. -/
def rangeLadderTop (ν : ℝ) (j : ℕ) : ℕ := ⌊rangeLadderTopReal ν j⌋₊

/-- The designated primes of range `j`. -/
def rangeLadderP (ν : ℝ) (j : ℕ) : Finset ℕ := primesRange (rangeLadderBase ν j) (rangeLadderTop ν j)

/-- The threshold exponent `1/4 − 1/(8·2^j)` of range `j`. -/
def rangeLadderAlpha (j : ℕ) : ℝ := 1 / 4 - 1 / (8 * 2 ^ j)

theorem rangeLadderNu_succ (ν : ℝ) (j : ℕ) : rangeLadderNu ν (j + 1) = rangeLadderNu ν j ^ 2 := by
  rw [rangeLadderNu, rangeLadderNu, pow_succ, pow_mul]

theorem rangeLadderNu_pos {ν : ℝ} (hν : 0 < ν) (j : ℕ) : 0 < rangeLadderNu ν j := pow_pos hν _

theorem log_rangeLadderNu (ν : ℝ) (j : ℕ) :
    Real.log (rangeLadderNu ν j) = 2 ^ j * Real.log ν := by
  rw [rangeLadderNu, Real.log_pow]; push_cast; ring

theorem le_rangeLadderNu {ν : ℝ} (hν : 1 ≤ ν) (j : ℕ) : ν ≤ rangeLadderNu ν j := by
  rw [rangeLadderNu]
  calc ν = ν ^ 1 := (pow_one ν).symm
    _ ≤ ν ^ (2 ^ j) := pow_le_pow_right₀ hν (Nat.one_le_two_pow)

theorem two_pow_le_log_rangeLadderNu {ν : ℝ} (hν : Real.exp 1 ≤ ν) (j : ℕ) :
    (2 : ℝ) ^ j ≤ Real.log (rangeLadderNu ν j) := by
  have hν0 : 0 < ν := lt_of_lt_of_le (Real.exp_pos 1) hν
  have hl : 1 ≤ Real.log ν := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hν
  rw [log_rangeLadderNu]
  have : (0 : ℝ) ≤ 2 ^ j := by positivity
  nlinarith

theorem exp_le_rangeLadderR (ν : ℝ) (j : ℕ) : Real.exp (rangeLadderNu ν j ^ 4) ≤ rangeLadderR ν j :=
  Nat.le_ceil _

theorem rangeLadderR_le (ν : ℝ) (j : ℕ) : rangeLadderR ν j ≤ Real.exp (rangeLadderNu ν j ^ 4) + 1 :=
  (Nat.ceil_lt_add_one (Real.exp_pos _).le).le

theorem one_lt_rangeLadderR {ν : ℝ} (hν : 0 < ν) (j : ℕ) : 1 < rangeLadderR ν j := by
  have h1 : 1 < Real.exp (rangeLadderNu ν j ^ 4) :=
    Real.one_lt_exp_iff.mpr (pow_pos (rangeLadderNu_pos hν j) 4)
  exact h1.trans_le (exp_le_rangeLadderR ν j)

theorem rangeLadderR_pos {ν : ℝ} (hν : 0 < ν) (j : ℕ) : 0 < rangeLadderR ν j :=
  lt_trans one_pos (one_lt_rangeLadderR hν j)

theorem log_rangeLadderR_ge (ν : ℝ) (j : ℕ) : rangeLadderNu ν j ^ 4 ≤ Real.log (rangeLadderR ν j) := by
  have := Real.log_le_log (Real.exp_pos _) (exp_le_rangeLadderR ν j)
  rwa [Real.log_exp] at this

theorem log_rangeLadderR_le {ν : ℝ} (hν : 0 < ν) (j : ℕ) :
    Real.log (rangeLadderR ν j) ≤ rangeLadderNu ν j ^ 4 + 1 := by
  have hpos := rangeLadderR_pos hν j
  have h1 : rangeLadderR ν j ≤ Real.exp (rangeLadderNu ν j ^ 4 + 1) := by
    rw [Real.exp_add]
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have hx : (1 : ℝ) ≤ Real.exp (rangeLadderNu ν j ^ 4) := Real.one_le_exp (by positivity)
    nlinarith [rangeLadderR_le ν j]
  have := Real.log_le_log hpos h1
  rwa [Real.log_exp] at this

theorem rangeLadderEta_pos (ν : ℝ) (j : ℕ) : 0 < rangeLadderEta ν j := by
  rw [rangeLadderEta]; positivity

theorem rangeLadderEta_le_one {ν : ℝ} (hν : 0 ≤ ν) (j : ℕ) : rangeLadderEta ν j ≤ 1 := by
  rw [rangeLadderEta, div_le_one (by positivity)]
  have h1 : Real.exp (-ν) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  linarith

theorem rangeLadderSteps_ge (ν : ℝ) (j : ℕ) :
    2 * rangeLadderNu ν j ^ 5 / rangeLadderEta ν j ≤ rangeLadderSteps ν j := Nat.le_ceil _

theorem rangeLadderSteps_le {ν : ℝ} (hν : 0 < ν) (j : ℕ) :
    (rangeLadderSteps ν j : ℝ) ≤ 2 * rangeLadderNu ν j ^ 5 / rangeLadderEta ν j + 1 := by
  have h0 : 0 ≤ 2 * rangeLadderNu ν j ^ 5 / rangeLadderEta ν j := by
    have := rangeLadderEta_pos ν j
    have := rangeLadderNu_pos hν j
    positivity
  exact (Nat.ceil_lt_add_one h0).le

theorem one_le_rangeLadderSteps {ν : ℝ} (hν : 0 < ν) (j : ℕ) : 1 ≤ rangeLadderSteps ν j := by
  rw [rangeLadderSteps, Nat.one_le_ceil_iff]
  have := rangeLadderEta_pos ν j
  have := rangeLadderNu_pos hν j
  positivity

/-- The number of steps is at most `3ν_j⁵·2^j·e^ν`. -/
theorem rangeLadderSteps_le_exp {ν : ℝ} (hν : 1 ≤ ν) (j : ℕ) :
    (rangeLadderSteps ν j : ℝ) ≤ 3 * rangeLadderNu ν j ^ 5 * 2 ^ j * Real.exp ν := by
  have hν0 : 0 < ν := by linarith
  have h := rangeLadderSteps_le hν0 j
  have hid : 2 * rangeLadderNu ν j ^ 5 / rangeLadderEta ν j = 2 * rangeLadderNu ν j ^ 5 * 2 ^ j * Real.exp ν := by
    rw [rangeLadderEta, Real.exp_neg]
    field_simp
  have h1 : (1 : ℝ) ≤ rangeLadderNu ν j ^ 5 * 2 ^ j * Real.exp ν := by
    have a1 : 1 ≤ rangeLadderNu ν j ^ 5 := one_le_pow₀ (hν.trans (le_rangeLadderNu hν j))
    have a2 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have a3 : 1 ≤ Real.exp ν := Real.one_le_exp hν0.le
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ rangeLadderNu ν j ^ 5 * 2 ^ j * Real.exp ν := by gcongr
  rw [hid] at h
  linarith

theorem rangeLadderTopReal_pos {ν : ℝ} (hν : 0 < ν) (j : ℕ) : 0 < rangeLadderTopReal ν j := by
  rw [rangeLadderTopReal]
  have := rangeLadderR_pos hν j
  have := rangeLadderEta_pos ν j
  positivity

/-- The top of a range, from below: `ν_j⁴ + ν_j⁵ ≤ log Q_j`. -/
theorem log_rangeLadderTopReal_ge {ν : ℝ} (hν : 0 ≤ ν) (hν0 : 0 < ν) (j : ℕ) :
    rangeLadderNu ν j ^ 4 + rangeLadderNu ν j ^ 5 ≤ Real.log (rangeLadderTopReal ν j) := by
  have hη := rangeLadderEta_pos ν j
  have hη1 := rangeLadderEta_le_one hν j
  rw [rangeLadderTopReal, Real.log_mul (rangeLadderR_pos hν0 j).ne' (by positivity), Real.log_pow]
  have hlog := log_one_add_ge_half_self hη hη1
  have hL := rangeLadderSteps_ge ν j
  have hstep : rangeLadderNu ν j ^ 5 ≤ (rangeLadderSteps ν j : ℝ) * Real.log (1 + rangeLadderEta ν j) := by
    have hL' : 2 * rangeLadderNu ν j ^ 5 ≤ (rangeLadderSteps ν j : ℝ) * rangeLadderEta ν j := by
      rwa [div_le_iff₀ hη] at hL
    have hL0 : (0 : ℝ) ≤ rangeLadderSteps ν j := Nat.cast_nonneg _
    nlinarith
  linarith [log_rangeLadderR_ge ν j]

/-- The top of a range, from above: `log Q_j ≤ 3ν_j⁵` once `ν ≥ 2`. -/
theorem log_rangeLadderTopReal_le {ν : ℝ} (hν : 2 ≤ ν) (j : ℕ) :
    Real.log (rangeLadderTopReal ν j) ≤ 3 * rangeLadderNu ν j ^ 5 := by
  have hν0 : 0 < ν := by linarith
  have hη := rangeLadderEta_pos ν j
  have hη1 := rangeLadderEta_le_one hν0.le j
  have ht : 2 ≤ rangeLadderNu ν j := hν.trans (le_rangeLadderNu (by linarith) j)
  rw [rangeLadderTopReal, Real.log_mul (rangeLadderR_pos hν0 j).ne' (by positivity), Real.log_pow]
  have hlog : Real.log (1 + rangeLadderEta ν j) ≤ rangeLadderEta ν j := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + rangeLadderEta ν j by linarith)
    linarith
  have hL := rangeLadderSteps_le hν0 j
  have hstep : (rangeLadderSteps ν j : ℝ) * Real.log (1 + rangeLadderEta ν j)
      ≤ 2 * rangeLadderNu ν j ^ 5 + 1 := by
    have hL0 : (0 : ℝ) ≤ rangeLadderSteps ν j := Nat.cast_nonneg _
    have hlog0 : 0 ≤ Real.log (1 + rangeLadderEta ν j) := Real.log_nonneg (by linarith)
    calc (rangeLadderSteps ν j : ℝ) * Real.log (1 + rangeLadderEta ν j)
        ≤ (2 * rangeLadderNu ν j ^ 5 / rangeLadderEta ν j + 1) * rangeLadderEta ν j := by gcongr
      _ = 2 * rangeLadderNu ν j ^ 5 + rangeLadderEta ν j := by field_simp
      _ ≤ 2 * rangeLadderNu ν j ^ 5 + 1 := by linarith
  have hR := log_rangeLadderR_le hν0 j
  have h45 : rangeLadderNu ν j ^ 4 + 2 ≤ rangeLadderNu ν j ^ 5 := by
    have h4 : (16 : ℝ) ≤ rangeLadderNu ν j ^ 4 := by
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ rangeLadderNu ν j ^ 4 := by gcongr
    nlinarith
  linarith

/-- The designated primes of range `j` lie in its ladder. -/
theorem rangeLadderP_bounds (ν : ℝ) (j : ℕ) :
    ∀ p ∈ rangeLadderP ν j, rangeLadderR ν j < (p : ℝ)
      ∧ (p : ℝ) ≤ rangeLadderR ν j * (1 + rangeLadderEta ν j) ^ rangeLadderSteps ν j :=
  primesRange_ladder_bounds_self rfl (rangeLadderEta_pos ν j).le (Nat.cast_nonneg _) rfl

theorem rangeLadderP_prime (ν : ℝ) (j : ℕ) : ∀ q ∈ rangeLadderP ν j, q.Prime :=
  fun _ hq => (mem_primesRange.1 hq).1

/-- The threshold exponents increase by `1/(16·2^j)` from one range to the next. -/
theorem rangeLadderAlpha_sub (j : ℕ) :
    2 * rangeLadderAlpha j - 2 * rangeLadderAlpha (j + 1) = -(1 / (8 * 2 ^ j)) := by
  rw [rangeLadderAlpha, rangeLadderAlpha, pow_succ]
  field_simp
  ring

theorem rangeLadderAlpha_le (j : ℕ) : rangeLadderAlpha j ≤ 1 / 2 := by
  rw [rangeLadderAlpha]
  have : (0 : ℝ) ≤ 1 / (8 * 2 ^ j) := by positivity
  linarith

theorem rangeLadderAlpha_zero : rangeLadderAlpha 0 = 1 / 8 := by
  rw [rangeLadderAlpha]; norm_num

end

end RHTower.Sieve
