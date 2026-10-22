import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarParabolicCompletedEndpointLaw

/-!
# All-head no-go for the literal canonical completed parabolic current

At canonical integer clocks, the terminal-completed matched--quantile source is not a bounded
sequence.  This is not an analytic conjecture: every multiple of six is outside von Mangoldt
support, so the literal matched aggregate is stationary there, while its physical endpoint quartic
has a linearly growing one-step increment.

The result rules out only an all-integer-head envelope.  It leaves open, and makes mandatory, a
genuinely cofinal source-relative selection that absorbs these forced zero-atom drifts.  No source
term is replaced, averaged, or estimated away.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- The original terminal-completed matched--quantile source current at the canonical integer
clock. -/
def ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent (K : ℕ) : ℝ :=
  ccmParabolicPairing
    (ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K
      (Real.log ((K : ℝ) + 3)))
    (ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K
      (Real.log ((K : ℝ) + 3)))

/-- The deterministic physical endpoint contribution at the same canonical clock. -/
def ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic (K : ℕ) : ℝ :=
  (2 * Real.sqrt ((K + 3 : ℕ) : ℝ) - 2) ^ (4 : ℕ) / 12

theorem criticalMellinAtomWeight_eq_zero_of_not_isPrimePow
    {n : ℕ} (hn : ¬ IsPrimePow n) : criticalMellinAtomWeight n = 0 := by
  rw [criticalMellinAtomWeight_eq_div_sqrt,
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, zero_div]

/-- A zero von-Mangoldt atom contributes no matched parabolic cell at all. -/
theorem ccmActualHeadMatchedParabolicMoment_eq_zero_of_not_isPrimePow
    {n : ℕ} (hn : ¬ IsPrimePow n) :
    ccmActualHeadMatchedParabolicMoment n = 0 := by
  have hw : criticalMellinAtomWeight n = 0 :=
    criticalMellinAtomWeight_eq_zero_of_not_isPrimePow hn
  have hwidth : ccmActualHeadMatchedPolarUpperCoordinate n -
      ccmActualHeadMatchedPolarLowerCoordinate n = 0 := by
    rw [ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight, hw]
  unfold ccmActualHeadMatchedParabolicMoment
  rw [sub_eq_zero.mp hwidth, ccmParabolicMoment_self]

theorem ccmActualHeadMatchedParabolicAggregate_succ
    (K : ℕ) :
    ccmActualHeadMatchedParabolicAggregate (K + 1) =
      ccmActualHeadMatchedParabolicAggregate K +
        ccmActualHeadMatchedParabolicMoment (K + 3) := by
  simp [ccmActualHeadMatchedParabolicAggregate, Finset.sum_range_succ]

/-- The actual matched aggregate is exactly stationary when the newly admitted integer is not a
prime power. -/
theorem ccmActualHeadMatchedParabolicAggregate_succ_eq_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    ccmActualHeadMatchedParabolicAggregate (K + 1) =
      ccmActualHeadMatchedParabolicAggregate K := by
  rw [ccmActualHeadMatchedParabolicAggregate_succ,
    ccmActualHeadMatchedParabolicMoment_eq_zero_of_not_isPrimePow hK]
  simp

theorem ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent_eq_matchedForm_sub_endpointQuartic
    (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent K =
      ccmParabolicForm (ccmActualHeadMatchedParabolicAggregate K) -
        ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic K := by
  unfold ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent
    ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic
  exact ccmActualHeadMatchedCompletedQuantileParabolic_pairing_sourceBoundary_log_eq_matchedForm_sub_canonicalEndpointQuartic K

/-- At a zero atom, the complete literal current moves by exactly the negative deterministic
endpoint-quartic increment. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent_succ_sub_eq_endpointQuartic_sub_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent (K + 1) -
      ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent K =
      ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic K -
        ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic (K + 1) := by
  rw [ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent_eq_matchedForm_sub_endpointQuartic,
    ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent_eq_matchedForm_sub_endpointQuartic,
    ccmActualHeadMatchedParabolicAggregate_succ_eq_of_not_isPrimePow K hK]
  ring

/-- The deterministic endpoint quartic has a linear lower bound on each integer increment after
its initial range. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicEndpointQuartic_succ_sub_lower
    (N : ℕ) (hN : 4 ≤ N) :
    (2 / 9 : ℝ) * N ≤
      ((2 * Real.sqrt ((N + 1 : ℕ) : ℝ) - 2) ^ (4 : ℕ) / 12 -
        (2 * Real.sqrt (N : ℝ) - 2) ^ (4 : ℕ) / 12) := by
  let a : ℝ := Real.sqrt (N : ℝ)
  let b : ℝ := Real.sqrt ((N + 1 : ℕ) : ℝ)
  let x : ℝ := 2 * a - 2
  let y : ℝ := 2 * b - 2
  have hNR : 0 ≤ (N : ℝ) := by positivity
  have hN1R : 0 ≤ ((N + 1 : ℕ) : ℝ) := by positivity
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hasq : a ^ (2 : ℕ) = (N : ℝ) := by
    dsimp [a]
    exact Real.sq_sqrt hNR
  have hbsq : b ^ (2 : ℕ) = ((N + 1 : ℕ) : ℝ) := by
    dsimp [b]
    exact Real.sq_sqrt hN1R
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have ha2 : 2 ≤ a := by nlinarith
  have hab : a ≤ b := by
    by_contra h
    have : b < a := lt_of_not_ge h
    have hprod : 0 < (a - b) * (a + b) :=
      mul_pos (sub_pos.mpr this) (by linarith)
    have hfactor : (a - b) * (a + b) = a ^ (2 : ℕ) - b ^ (2 : ℕ) := by ring
    rw [hfactor] at hprod
    have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by norm_num
    rw [hcast] at hbsq
    nlinarith
  have hble : b ≤ a + 1 := by
    by_contra h
    have : a + 1 < b := lt_of_not_ge h
    have hprod : 0 < (b - (a + 1)) * (b + (a + 1)) :=
      mul_pos (sub_pos.mpr this) (by linarith)
    have hfactor : (b - (a + 1)) * (b + (a + 1)) = b ^ (2 : ℕ) - (a + 1) ^ (2 : ℕ) := by ring
    rw [hfactor] at hprod
    have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by norm_num
    rw [hcast] at hbsq
    nlinarith
  have hba0 : 0 ≤ b - a := sub_nonneg.mpr hab
  have hsum : b + a ≤ 3 * a := by linarith
  have hgap : (b - a) * (b + a) = 1 := by
    have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by norm_num
    rw [hcast] at hbsq
    nlinarith
  have hden : 1 ≤ 3 * a * (b - a) := by
    calc
      1 = (b - a) * (b + a) := hgap.symm
      _ ≤ (b - a) * (3 * a) := mul_le_mul_of_nonneg_left hsum hba0
      _ = 3 * a * (b - a) := by ring
  have hxa : a ≤ x := by
    dsimp [x]
    linarith
  have hx0 : 0 ≤ x := le_trans ha0 hxa
  have hyx : 0 ≤ y - x := by
    dsimp [x, y]
    linarith
  have hcube : 0 ≤ x ^ (3 : ℕ) - a ^ (3 : ℕ) := by
    calc
      x ^ (3 : ℕ) - a ^ (3 : ℕ) = (x - a) * (x ^ (2 : ℕ) + x * a + a ^ (2 : ℕ)) := by ring
      _ ≥ 0 := mul_nonneg (sub_nonneg.mpr hxa) (by positivity)
  have hfirst : 4 * a ^ (3 : ℕ) * (y - x) ≤ y ^ (4 : ℕ) - x ^ (4 : ℕ) := by
    have hmono : 4 * a ^ (3 : ℕ) * (y - x) ≤ 4 * x ^ (3 : ℕ) * (y - x) := by
      have hcube' : a ^ (3 : ℕ) ≤ x ^ (3 : ℕ) := by linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcube' (by norm_num)) hyx
    have hrest : 0 ≤ y ^ (4 : ℕ) - x ^ (4 : ℕ) - 4 * x ^ (3 : ℕ) * (y - x) := by
      calc
        y ^ (4 : ℕ) - x ^ (4 : ℕ) - 4 * x ^ (3 : ℕ) * (y - x) =
            (y - x) ^ (2 : ℕ) * (6 * x ^ (2 : ℕ) + 4 * x * (y - x) + (y - x) ^ (2 : ℕ)) := by ring
        _ ≥ 0 := mul_nonneg (sq_nonneg _) (by positivity)
    linarith
  have hmain : (8 / 3 : ℝ) * a ^ (2 : ℕ) ≤ 4 * a ^ (3 : ℕ) * (y - x) := by
    calc
      (8 / 3 : ℝ) * a ^ (2 : ℕ) = (8 / 3 : ℝ) * a ^ (2 : ℕ) * 1 := by ring
      _ ≤ (8 / 3 : ℝ) * a ^ (2 : ℕ) * (3 * a * (b - a)) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
      _ = 4 * a ^ (3 : ℕ) * (y - x) := by
        dsimp [x, y]
        ring
  dsimp [a, b, x, y] at hasq hfirst hmain ⊢
  nlinarith

theorem ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic_succ_sub_lower_at_head
    (K : ℕ) (hK : 1 ≤ K) :
    (2 / 9 : ℝ) * (K + 3) ≤
      ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic (K + 1) -
        ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic K := by
  unfold ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic
  have h := ccmActualHeadMatchedCompletedQuantileParabolicEndpointQuartic_succ_sub_lower
    (K + 3) (by omega)
  convert h using 1
  all_goals norm_num

theorem ccmActualHeadMatchedCompletedQuantileParabolic_not_isPrimePow_six_mul_succ (m : ℕ) :
    ¬ IsPrimePow (6 * (m + 1)) := by
  have hn2 : 2 ≤ 6 * (m + 1) := by omega
  rw [Nat.not_isPrimePow_iff_nontrivial_of_two_le hn2]
  refine ⟨2, Nat.mem_primeFactors.mpr ⟨Nat.prime_two, ?_, by omega⟩,
    3, Nat.mem_primeFactors.mpr ⟨Nat.prime_three, ?_, by omega⟩, by norm_num⟩
  · exact dvd_mul_of_dvd_left (by norm_num : 2 ∣ 6) _
  · exact dvd_mul_of_dvd_left (by norm_num : 3 ∣ 6) _

/-- **Explicit zero-atom drift.** The source-faithful canonical current has linearly growing
consecutive jumps at the explicit multiple-of-six lattice. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent_six_mul_succ_increment_abs_ge
    (m : ℕ) :
    (4 / 3 : ℝ) * (m + 1) ≤
      |ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent ((6 * m + 3) + 1) -
        ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent (6 * m + 3)| := by
  let K := 6 * m + 3
  have hnot : ¬ IsPrimePow (K + 3) := by
    have hindex : K + 3 = 6 * (m + 1) := by
      dsimp only [K]
      norm_num [Nat.mul_add, Nat.add_assoc]
    rw [hindex]
    exact ccmActualHeadMatchedCompletedQuantileParabolic_not_isPrimePow_six_mul_succ m
  have hcurrent :=
    ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent_succ_sub_eq_endpointQuartic_sub_of_not_isPrimePow K hnot
  have hendpoint :=
    ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic_succ_sub_lower_at_head K (by
      dsimp only [K]
      omega)
  have hendpoint0 : 0 ≤ ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic (K + 1) -
      ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic K := by
    exact le_trans (show 0 ≤ (2 / 9 : ℝ) * (K + 3) by positivity) hendpoint
  have habs :
      |ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent (K + 1) -
        ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent K| =
        ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic (K + 1) -
          ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic K := by
    rw [hcurrent]
    rw [show ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic K -
        ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic (K + 1) =
        -(ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic (K + 1) -
          ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic K) by ring,
      abs_neg, abs_of_nonneg hendpoint0]
  rw [show (6 * m + 3) + 1 = K + 1 by dsimp only [K],
    show 6 * m + 3 = K by rfl, habs]
  calc
    (4 / 3 : ℝ) * (m + 1) = (2 / 9 : ℝ) * (K + 3) := by
      dsimp only [K]
      push_cast
      ring
    _ ≤ ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic (K + 1) -
        ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic K := hendpoint

/-- **All-head no-go.** No uniform bound can hold for the literal terminal-completed current at
every canonical integer head.  This does not rule out a carefully selected cofinal family. -/
theorem not_exists_uniform_ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent_bound :
    ¬ ∃ C : ℝ, ∀ K : ℕ,
      |ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent K| ≤ C := by
  rintro ⟨C, hC⟩
  have hC0 : 0 ≤ C := le_trans
    (abs_nonneg (ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent 0)) (hC 0)
  obtain ⟨m, hm⟩ := exists_nat_gt ((3 / 2 : ℝ) * C)
  have hlarge :=
    ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent_six_mul_succ_increment_abs_ge m
  have hupper :
      |ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent ((6 * m + 3) + 1) -
        ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent (6 * m + 3)| ≤ 2 * C := by
    calc
      |ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent ((6 * m + 3) + 1) -
          ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent (6 * m + 3)| ≤
          |ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent ((6 * m + 3) + 1)| +
            |ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent (6 * m + 3)| := by
              simpa using abs_sub_le
                (ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent ((6 * m + 3) + 1))
                (0 : ℝ)
                (ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent (6 * m + 3))
      _ ≤ C + C := add_le_add (hC _) (hC _)
      _ = 2 * C := by ring
  have hmle : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
  have hstrict : 2 * C < (4 / 3 : ℝ) * (m + 1) := by
    push_cast at hmle ⊢
    nlinarith
  exact (not_lt_of_ge hupper) (lt_of_lt_of_le hstrict hlarge)

end RHTower
