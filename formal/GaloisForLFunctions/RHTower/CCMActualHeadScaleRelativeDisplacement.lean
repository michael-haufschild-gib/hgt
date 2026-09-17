import GaloisForLFunctions.RHTower.CCMActualHeadDyadicRelativeDisplacement

/-!
# All-scale completed-error holonomy of matched prime cells

The exact dyadic matched--quantile displacement law is one element of an integral-scale cocycle.
For every integral coarsening `n ↦ floor (n / m)`, this module records the literal completed
prime--polar error difference as an oriented cell displacement, two exact upper-cell marks, and
the nonnegative floor reserve.  It supplies no positivity or energy estimate: critical control of
the positive variation remains RH-bearing.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Exact polar-coordinate reserve from replacing the real quotient `n / m` by its integer
coarsening. -/
def scaleRoundingReserve (m n : ℕ) : ℝ :=
  2 * (Real.exp ((Real.log n - Real.log m) / 2) -
    Real.exp (Real.log ((n / m : ℕ) : ℝ) / 2))

/-- At every positive integral logarithmic scale, the prime-mass floor is exactly the coarsened
integer. -/
theorem criticalMellinPrimeMass_log_sub_logScale_eq_divScale
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    criticalMellinPrimeMass (Real.log n - Real.log m) =
      criticalMellinPrimeMass (Real.log ((n / m : ℕ) : ℝ)) := by
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.zero_lt_one.trans_le hm) hmn
  have hmpos : 0 < m := Nat.zero_lt_of_lt hm
  have hqpos : 0 < n / m := Nat.div_pos hmn hmpos
  have hnposR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hmposR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hqposR : (0 : ℝ) < ((n / m : ℕ) : ℝ) := by exact_mod_cast hqpos
  have hleftReal : Real.exp (Real.log n - Real.log m) = (n : ℝ) / m := by
    rw [Real.exp_sub, Real.exp_log hnposR, Real.exp_log hmposR]
  have hleft : ⌊Real.exp (Real.log n - Real.log m)⌋₊ = n / m := by
    rw [hleftReal]
    simpa using (Nat.floor_div_eq_div (K := ℝ) n m)
  have hright : ⌊Real.exp (Real.log ((n / m : ℕ) : ℝ))⌋₊ = n / m := by
    rw [Real.exp_log hqposR, Nat.floor_natCast]
  unfold criticalMellinPrimeMass
  rw [hleft, hright]

/-- The completed-error increment at every integral scale is the node-error increment plus the
literal floor reserve. -/
theorem completedError_scale_eq_nodeError_sub_add_rounding
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    criticalMellinCompletedError (Real.log n - Real.log m) -
        criticalMellinCompletedError (Real.log n) +
        2 * (Real.sqrt m - 1) / Real.sqrt n =
      ccmActualHeadOutgoingNodeError (n / m) -
        ccmActualHeadOutgoingNodeError n + scaleRoundingReserve m n := by
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.zero_lt_one.trans_le hm) hmn
  have hmpos : 0 < m := Nat.zero_lt_of_lt hm
  have hqpos : 0 < n / m := Nat.div_pos hmn hmpos
  have hprime := criticalMellinPrimeMass_log_sub_logScale_eq_divScale hm hmn
  simp only [ccmActualHeadOutgoingNodeError,
    criticalMellinCompletedError_eq_polar_sub_primeMass]
  rw [hprime]
  have hlogm : Real.exp (Real.log m / 2) = Real.sqrt m := by
    rw [← Real.log_sqrt (by exact_mod_cast (Nat.le_of_lt hmpos)),
      Real.exp_log (Real.sqrt_pos.mpr (by exact_mod_cast hmpos))]
  have hlogn : Real.exp (Real.log n / 2) = Real.sqrt n := by
    rw [← Real.log_sqrt (by exact_mod_cast (Nat.le_of_lt hnpos)),
      Real.exp_log (Real.sqrt_pos.mpr (by exact_mod_cast hnpos))]
  have hlogq : Real.exp (Real.log ((n / m : ℕ) : ℝ) / 2) =
      Real.sqrt ((n / m : ℕ) : ℝ) := by
    rw [← Real.log_sqrt (by exact_mod_cast (Nat.le_of_lt hqpos)),
      Real.exp_log (Real.sqrt_pos.mpr (by exact_mod_cast hqpos))]
  have hneglogn : Real.exp (-(Real.log n / 2)) = (Real.sqrt n)⁻¹ := by
    rw [Real.exp_neg, hlogn]
  have hneglogq : Real.exp (-(Real.log ((n / m : ℕ) : ℝ) / 2)) =
      (Real.sqrt ((n / m : ℕ) : ℝ))⁻¹ := by
    rw [Real.exp_neg, hlogq]
  have hshift : Real.exp (-((Real.log n - Real.log m) / 2)) =
      Real.sqrt m * (Real.sqrt n)⁻¹ := by
    rw [show -((Real.log n - Real.log m) / 2) =
        Real.log m / 2 + -(Real.log n / 2) by ring,
      Real.exp_add, hlogm, hneglogn]
  simp_rw [Real.sinh_eq]
  rw [hshift, hneglogn, hneglogq]
  dsimp only [scaleRoundingReserve]
  change _ = _ + 2 *
    (Real.exp ((Real.log n - Real.log m) / 2) -
      Real.exp (Real.log ((n / m : ℕ) : ℝ) / 2))
  ring

/-- Oriented matched--quantile holonomy under one arbitrary integer coarsening. -/
def scaleRelativeDisplacement (m n : ℕ) : ℝ :=
  ccmActualHeadMatchedQuantilePolarDisplacement n -
    ccmActualHeadMatchedQuantilePolarDisplacement (n / m)

/-- **All-scale transport identity.** The literal completed source at every integral logarithmic
coarsening is exactly the matched--quantile holonomy, its two geometric endpoint marks, and the
floor reserve. -/
theorem completedError_scale_eq_relativeDisplacement_add_upperExcess_sub_add_rounding
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    criticalMellinCompletedError (Real.log n - Real.log m) -
        criticalMellinCompletedError (Real.log n) +
        2 * (Real.sqrt m - 1) / Real.sqrt n =
      scaleRelativeDisplacement m n + matchedUpperExcess n -
        matchedUpperExcess (n / m) + scaleRoundingReserve m n := by
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.zero_lt_one.trans_le hm) hmn
  have hmpos : 0 < m := Nat.zero_lt_of_lt hm
  have hqpos : 0 < n / m := Nat.div_pos hmn hmpos
  have hnode := completedError_scale_eq_nodeError_sub_add_rounding hm hmn
  have hdispN :=
    ccmActualHeadMatchedQuantilePolarDisplacement_eq_neg_error_sub_upperExcess n hnpos
  have hdispQ :=
    ccmActualHeadMatchedQuantilePolarDisplacement_eq_neg_error_sub_upperExcess (n / m) hqpos
  unfold scaleRelativeDisplacement matchedUpperExcess
  linarith

/-- The literal loss from integer coarsening is nonnegative. -/
theorem scaleRoundingReserve_nonneg
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    0 ≤ scaleRoundingReserve m n := by
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.zero_lt_one.trans_le hm) hmn
  have hmpos : 0 < m := Nat.zero_lt_of_lt hm
  have hqpos : 0 < n / m := Nat.div_pos hmn hmpos
  have hdiv : ((n / m : ℕ) : ℝ) ≤ (n : ℝ) / m := Nat.cast_div_le
  have hlog : Real.log ((n / m : ℕ) : ℝ) ≤ Real.log ((n : ℝ) / m) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by exact_mod_cast hqpos))
      (Set.mem_Ioi.mpr (by positivity)) hdiv
  have hexp : Real.exp (Real.log ((n / m : ℕ) : ℝ) / 2) ≤
      Real.exp ((Real.log n - Real.log m) / 2) := by
    apply Real.exp_le_exp.mpr
    rw [← Real.log_div (by exact_mod_cast hnpos.ne')
      (by exact_mod_cast hmpos.ne')]
    linarith
  unfold scaleRoundingReserve
  linarith

end RHTower
