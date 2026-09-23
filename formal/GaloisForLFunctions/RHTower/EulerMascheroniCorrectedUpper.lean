import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# A corrected upper sequence for the Euler--Mascheroni constant

Subtracting `1 / (2 * (n + 1))` from the standard upper sequence
`H_n - log n` preserves strict decrease to Euler's constant while removing
its first-order error.  The proof uses the rational Padé lower bound
`2x / (x + 2) < log (1 + x)`.

At the factorable index `1250 = 2 * 5^(4 : ℕ)`, this gives the exact certified
bound `gamma < 0.577216` without a large harmonic evaluation.
-/

open Real Filter Topology

namespace RHTower

noncomputable section

/-- First-order-corrected upper approximation to Euler's constant. -/
def eulerMascheroniCorrectedUpper (n : ℕ) : ℝ :=
  if n = 0 then 2 else
    Real.eulerMascheroniSeq' n - 1 / (2 * ((n : ℝ) + 1))

/-- The corrected upper approximants are strictly decreasing. -/
theorem strictAnti_eulerMascheroniCorrectedUpper :
    StrictAnti eulerMascheroniCorrectedUpper := by
  refine strictAnti_nat_of_succ_lt fun n => ?_
  rcases n with _ | n
  · norm_num [eulerMascheroniCorrectedUpper, Real.eulerMascheroniSeq']
  · let m : ℕ := n + 1
    have hm0 : 0 < (m : ℝ) := by
      dsimp only [m]
      positivity
    have hm1 : 0 < (m : ℝ) + 1 := by positivity
    have hm2 : 0 < (m : ℝ) + 2 := by positivity
    have hlogPadé := Real.lt_log_one_add_of_pos (x := 1 / (m : ℝ)) (by positivity)
    have hlogEq :
        Real.log (1 + 1 / (m : ℝ)) =
          Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) := by
      rw [show 1 + 1 / (m : ℝ) = ((m : ℝ) + 1) / (m : ℝ) by
        field_simp]
      rw [Real.log_div hm1.ne' hm0.ne']
    have hrat :
        (2 * (m : ℝ) + 5) / (2 * ((m : ℝ) + 1) * ((m : ℝ) + 2)) <
          2 / (2 * (m : ℝ) + 1) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hlog :
        (2 * (m : ℝ) + 5) / (2 * ((m : ℝ) + 1) * ((m : ℝ) + 2)) <
          Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) := by
      rw [← hlogEq]
      apply hrat.trans
      calc
        2 / (2 * (m : ℝ) + 1) =
            2 * (1 / (m : ℝ)) / (1 / (m : ℝ) + 2) := by
              field_simp [hm0.ne']; ring_nf
        _ < Real.log (1 + 1 / (m : ℝ)) := hlogPadé
    simp only [eulerMascheroniCorrectedUpper, Nat.succ_ne_zero, if_false]
    rw [Real.eulerMascheroniSeq', Real.eulerMascheroniSeq']
    simp only [Nat.succ_ne_zero, if_false]
    have htarget :
        ((harmonic (m + 1) : ℚ) : ℝ) - Real.log (m + 1) -
            1 / (2 * (((m + 1 : ℕ) : ℝ) + 1)) <
          ((harmonic m : ℚ) : ℝ) - Real.log m -
            1 / (2 * ((m : ℝ) + 1)) := by
      rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
      push_cast
      field_simp at hlog ⊢
      nlinarith
    simpa only [m, Nat.cast_add, Nat.cast_one] using htarget

/-- The corrected sequence has the same limit as the standard upper sequence. -/
theorem tendsto_eulerMascheroniCorrectedUpper :
    Tendsto eulerMascheroniCorrectedUpper atTop
      (nhds Real.eulerMascheroniConstant) := by
  have hden : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop
      (by norm_num)
  have hcorr :
      Tendsto (fun n : ℕ => 1 / (2 * ((n : ℝ) + 1))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have hmain := Real.tendsto_eulerMascheroniSeq'.sub hcorr
  have hmain' :
      Tendsto (fun n : ℕ => Real.eulerMascheroniSeq' n -
        1 / (2 * ((n : ℝ) + 1))) atTop
        (nhds Real.eulerMascheroniConstant) := by
    simpa only [sub_zero] using hmain
  apply hmain'.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp [eulerMascheroniCorrectedUpper, hn]

/-- Every corrected approximant is a strict upper bound for Euler's constant. -/
theorem eulerMascheroniConstant_lt_correctedUpper (n : ℕ) :
    Real.eulerMascheroniConstant < eulerMascheroniCorrectedUpper n := by
  refine lt_of_le_of_lt ?_
    (strictAnti_eulerMascheroniCorrectedUpper (Nat.lt_succ_self n))
  exact strictAnti_eulerMascheroniCorrectedUpper.antitone.le_of_tendsto
    tendsto_eulerMascheroniCorrectedUpper (n + 1)

set_option maxRecDepth 1000000 in
/-- Exact six-decimal upper bound obtained at `1250 = 2 * 5^(4 : ℕ)`. -/
theorem eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion :
    Real.eulerMascheroniConstant < 577216 / 1000000 := by
  refine (eulerMascheroniConstant_lt_correctedUpper 1250).trans ?_
  rw [eulerMascheroniCorrectedUpper, if_neg (by norm_num),
    Real.eulerMascheroniSeq']
  norm_num only [if_false, Nat.reduceEqDiff, Nat.cast_ofNat]
  rw [show (1250 : ℝ) = 2 * 5 ^ (4 : ℕ) by norm_num,
    Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have htwo := Real.log_two_gt_d9
  have hfive := Real.log_five_gt_d9
  norm_num [harmonic] at *
  linarith

end

end RHTower
