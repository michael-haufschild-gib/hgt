import GaloisForLFunctions.RHTower.Sieve.TwoRangeScheduleFacts

/-!
# The remaining aggregates of the two-range schedule

The ladder groups are expressions in the length `M` of the Dirichlet polynomial, the number of
steps, the harmonic mass of the designated range and its cardinality.  This file supplies the
comparisons that the two ladders need and that the schedule does not yet record: the length against
the square root of the outer scale, the number of steps of the *high* ladder, the cardinality of a
prime range, and — the one arithmetic input — a **lower** bound for the harmonic mass, which the
rough group needs because that mass sits in a denominator.
-/

namespace RHTower.Sieve

open Filter Topology Finset

noncomputable section

/-- **The harmonic mass of a wide prime range, from below.**  The companion of
`Sieve/PrimeRangeLogLogMass.sum_inv_primesRange_le_logLog_diff`; both come from the same two-sided
Mertens estimate with a decaying error. -/
theorem sum_inv_primesRange_ge_logLog_diff {z₀ z : ℕ} (h₀ : 2 ≤ z₀) (hz : z₀ ≤ z) :
    Real.log (Real.log z) - Real.log (Real.log z₀)
        - 2 * ((2 * mertensFirstConst + 1 / 2) / Real.log z₀)
      ≤ ∑ p ∈ primesRange z₀ z, 1 / (p : ℝ) := by
  have hz2 : 2 ≤ z := le_trans h₀ hz
  have hlog₀ : (0 : ℝ) < Real.log z₀ := by
    have h2 : (2 : ℝ) ≤ (z₀ : ℝ) := by exact_mod_cast h₀
    exact Real.log_pos (by linarith)
  have hlogz : (0 : ℝ) < Real.log z := by
    have h2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
    exact Real.log_pos (by linarith)
  have hz₀0 : (0 : ℝ) < ((z₀ : ℕ) : ℝ) := by
    have : 0 < z₀ := by omega
    exact_mod_cast this
  have hmono : Real.log z₀ ≤ Real.log z := by
    have hle : ((z₀ : ℕ) : ℝ) ≤ ((z : ℕ) : ℝ) := by exact_mod_cast hz
    exact Real.log_le_log hz₀0 hle
  have hA := abs_mertensS_sub_logLog_sub_const_le hz2
  have hB := abs_mertensS_sub_logLog_sub_const_le h₀
  have hA' : -((2 * mertensFirstConst + 1 / 2) / Real.log z)
      ≤ mertensS z - logLog z - meisselMertensConst := (abs_le.1 hA).1
  have hB' : mertensS z₀ - logLog z₀ - meisselMertensConst
      ≤ (2 * mertensFirstConst + 1 / 2) / Real.log z₀ := (abs_le.1 hB).2
  have herr : (2 * mertensFirstConst + 1 / 2) / Real.log z
      ≤ (2 * mertensFirstConst + 1 / 2) / Real.log z₀ := by
    have hc0 : (0 : ℝ) ≤ 2 * mertensFirstConst + 1 / 2 := by
      have := mertensFirstConst_nonneg
      linarith
    exact div_le_div_of_nonneg_left hc0 hlog₀ hmono
  rw [sum_inv_primesRange hz]
  simp only [logLog] at hA' hB'
  linarith

/-- **The length of the Dirichlet polynomial is at least the square root of the outer scale.** -/
theorem sqrt_le_twoRangeLength {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt x ≤ ((twoRangeLength β x : ℕ) : ℝ) := by
  filter_upwards [(tendsto_cardLength hβ).eventually_ge_atTop (1 : ℝ)] with x hh1
  have hfl := Nat.lt_floor_add_one (Real.sqrt x + cardLength β x)
  rw [twoRangeLength]
  linarith

/-- **The length of the Dirichlet polynomial is at most twice the square root.** -/
theorem twoRangeLength_le_two_sqrt {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, ((twoRangeLength β x : ℕ) : ℝ) ≤ 2 * Real.sqrt x := by
  filter_upwards [cardLength_le_sqrt hβ0 hβ1, Filter.eventually_ge_atTop (0 : ℝ)] with x hhs hx0
  have hfl : ((twoRangeLength β x : ℕ) : ℝ) ≤ Real.sqrt x + cardLength β x := by
    rw [twoRangeLength]
    refine Nat.floor_le ?_
    have h1 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
    have h2 : (0 : ℝ) < cardLength β x := cardLength_pos β x
    linarith
  linarith

/-- The length of the Dirichlet polynomial is positive. -/
theorem one_le_twoRangeLength {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ x : ℝ in atTop, (1 : ℝ) ≤ ((twoRangeLength β x : ℕ) : ℝ) := by
  filter_upwards [sqrt_le_twoRangeLength hβ, Filter.eventually_ge_atTop (1 : ℝ)] with x hM hx1
  have : (1 : ℝ) ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hx1
  linarith

/-- **The high ladder has polylogarithmically many steps.** -/
theorem highSteps_le {a b c' : ℝ} (_ha : 0 < a) (hab : a ≤ b) (hc' : 0 < c') :
    ∀ᶠ x : ℝ in atTop,
      ((highSteps a b c' x : ℕ) : ℝ) ≤ 2 * (Real.log x) ^ (b + c') := by
  have hzero := tendsto_highEta (c' := c') hc'
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hzero] with x hx1 hlog1 hη1
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hη : 0 < highEta c' x := highEta_pos hx1
  have hlogr : (0 : ℝ) < Real.log (1 + highEta c' x) := Real.log_pos (by linarith)
  have hhalf := log_one_add_ge_half_self hη hη1
  have hmono : (Real.log x) ^ a ≤ (Real.log x) ^ b :=
    Real.rpow_le_rpow_of_exponent_le hlog1 hab
  have hgap0 : (0 : ℝ) ≤ (Real.log x) ^ b - (Real.log x) ^ a := by linarith
  have hnum : (Real.log x) ^ b - (Real.log x) ^ a ≤ (Real.log x) ^ b := by
    have : (0 : ℝ) ≤ (Real.log x) ^ a := Real.rpow_nonneg hlogx.le a
    linarith
  have hkey : 2 * (Real.log x) ^ b / highEta c' x = 2 * (Real.log x) ^ (b + c') := by
    rw [highEta, div_eq_mul_inv, ← Real.rpow_neg hlogx.le, neg_neg, mul_assoc,
      ← Real.rpow_add hlogx]
  have hfl : ((highSteps a b c' x : ℕ) : ℝ)
      ≤ ((Real.log x) ^ b - (Real.log x) ^ a) / Real.log (1 + highEta c' x) := by
    rw [highSteps]
    exact Nat.floor_le (div_nonneg hgap0 hlogr.le)
  refine hfl.trans ?_
  rw [← hkey]
  refine (div_le_div₀ (by positivity) hnum (by linarith) hhalf).trans (le_of_eq ?_)
  field_simp

end

end RHTower.Sieve
