import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarDLVPRate

/-!
# Relative decay of literal matched--quantile displacement

The literal matched-to-quantile polar displacement is not small compared with one local
critical-Mellin atom; controlling that stronger scale is precisely the unsolved signed coverage
problem.  It is, however, negligible on its natural polar-mass scale.  The unconditional
de la Vallée Poussin bound for the completed critical-Mellin error gives

`exp(-log n / 2) * delta_n -> 0`.

This theorem is source-faithful: it uses the exact identity
`delta_n = - outgoingNodeError_n - matchedUpperExcess_n`, including the local upper excess.
It does not estimate a signed collective codiagonal and therefore does not assert RH or the
missing cofinal coverage-seam bound.
-/

open Filter Topology Set MeasureTheory

noncomputable section

namespace RHTower

private theorem log_le_two_mul_sqrt {t : ℝ} (ht : 0 < t) :
    Real.log t ≤ 2 * Real.sqrt t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hlog : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 :=
    Real.log_le_sub_one_of_pos hs
  have hhalf : Real.log (Real.sqrt t) = Real.log t / 2 :=
    Real.log_sqrt ht.le
  rw [hhalf] at hlog
  linarith

/-- Every positive critical Mellin atom is at most `2`.  This coarse bound is used only to show
that the bounded local upper excess vanishes after polar-mass normalization. -/
theorem criticalMellinAtomWeight_le_two_of_pos {n : ℕ} (hn : 0 < n) :
    criticalMellinAtomWeight n ≤ 2 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  rw [criticalMellinAtomWeight_eq_div_sqrt]
  have hvm := ArithmeticFunction.vonMangoldt_le_log (n := n)
  have hlog := log_le_two_mul_sqrt hnR
  calc
    ArithmeticFunction.vonMangoldt n / Real.sqrt n ≤ Real.log n / Real.sqrt n :=
      div_le_div_of_nonneg_right hvm hsqrt.le
    _ ≤ (2 * Real.sqrt n) / Real.sqrt n :=
      div_le_div_of_nonneg_right hlog hsqrt.le
    _ = 2 := by field_simp

/-- The outgoing completed node error vanishes relative to polar mass.  This is the DLV/PNT
input expressed at literal integer nodes, with the finite incoming Gamma correction retained. -/
theorem tendsto_scaled_ccmActualHeadOutgoingNodeError_atTop_zero :
    Tendsto (fun n : ℕ => Real.exp (-Real.log (n : ℝ) / 2) *
      ccmActualHeadOutgoingNodeError n) atTop (𝓝 0) := by
  have hscale : Tendsto (fun n : ℕ => Real.exp (-Real.log (n : ℝ) / 2))
      atTop (𝓝 0) := by
    have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have harg : Tendsto (fun n : ℕ => -Real.log (n : ℝ) / 2) atTop atBot := by
      have hmul := hlog.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
      have hneg := tendsto_neg_atBot_iff.2 hmul
      convert hneg using 1
      ext n
      ring
    exact Real.tendsto_exp_atBot.comp harg
  have hcompleted : Tendsto (fun n : ℕ =>
      Real.exp (-Real.log (n : ℝ) / 2) *
        criticalMellinCompletedError (Real.log (n : ℝ))) atTop (𝓝 0) := by
    have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact tendsto_exp_neg_half_mul_criticalMellinCompletedError_atTop_zero.comp hlog
  have hsmall : Tendsto (fun n : ℕ =>
      Real.exp (-Real.log (n : ℝ) / 2) *
        (2 * (1 - Real.exp (-Real.log (n : ℝ) / 2)))) atTop (𝓝 0) := by
    have hsquare := hscale.mul hscale
    have hmodel := hscale.sub hsquare
    convert hmodel.const_mul 2 using 1 <;> ext n <;> ring
  have hsum : Tendsto (fun n : ℕ =>
      Real.exp (-Real.log (n : ℝ) / 2) *
        criticalMellinCompletedError (Real.log (n : ℝ)) -
      Real.exp (-Real.log (n : ℝ) / 2) *
        (2 * (1 - Real.exp (-Real.log (n : ℝ) / 2)))) atTop (𝓝 0) := by
    simpa using hcompleted.sub hsmall
  apply hsum.congr'
  filter_upwards with n
  simp only [ccmActualHeadOutgoingNodeError]
  ring

/-- The local upper excess of an exact matched cell also vanishes relative to polar mass. -/
theorem tendsto_scaled_ccmActualHeadMatchedUpperExcess_atTop_zero :
    Tendsto (fun n : ℕ => Real.exp (-Real.log (n : ℝ) / 2) *
      (ccmActualHeadMatchedPolarUpperCoordinate n -
        2 * Real.exp (Real.log n / 2))) atTop (𝓝 0) := by
  have hscale : Tendsto (fun n : ℕ => Real.exp (-Real.log (n : ℝ) / 2))
      atTop (𝓝 0) := by
    have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have harg : Tendsto (fun n : ℕ => -Real.log (n : ℝ) / 2) atTop atBot := by
      have hmul := hlog.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
      have hneg := tendsto_neg_atBot_iff.2 hmul
      convert hneg using 1
      ext n
      ring
    exact Real.tendsto_exp_atBot.comp harg
  have hmajor : Tendsto (fun n : ℕ => 2 * Real.exp (-Real.log (n : ℝ) / 2))
      atTop (𝓝 0) := by
    simpa using hscale.const_mul 2
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  let e := ccmActualHeadMatchedPolarUpperCoordinate n -
    2 * Real.exp (Real.log n / 2)
  have he := ccmActualHeadMatchedPolarUpperExcess_mem_atomWeight n
  have hw : criticalMellinAtomWeight n ≤ 2 :=
    criticalMellinAtomWeight_le_two_of_pos (Nat.zero_lt_of_lt hn)
  have hscale0 : 0 ≤ Real.exp (-Real.log (n : ℝ) / 2) := (Real.exp_pos _).le
  change ‖Real.exp (-Real.log (n : ℝ) / 2) * e‖ ≤
    2 * Real.exp (-Real.log (n : ℝ) / 2)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hscale0 he.1)]
  nlinarith

/-- **Relative literal transport law.**  Matched-to-quantile displacement is asymptotically
negligible relative to the polar mass coordinate `2 * sqrt n`.  The theorem deliberately makes
no claim relative to the much smaller atom width `criticalMellinAtomWeight n`. -/
theorem tendsto_scaled_ccmActualHeadMatchedQuantilePolarDisplacement_atTop_zero :
    Tendsto (fun n : ℕ => Real.exp (-Real.log (n : ℝ) / 2) *
      ccmActualHeadMatchedQuantilePolarDisplacement n) atTop (𝓝 0) := by
  have hnode := tendsto_scaled_ccmActualHeadOutgoingNodeError_atTop_zero
  have hexcess := tendsto_scaled_ccmActualHeadMatchedUpperExcess_atTop_zero
  have hsum : Tendsto (fun n : ℕ =>
      -(Real.exp (-Real.log (n : ℝ) / 2) * ccmActualHeadOutgoingNodeError n) -
      Real.exp (-Real.log (n : ℝ) / 2) *
        (ccmActualHeadMatchedPolarUpperCoordinate n -
          2 * Real.exp (Real.log n / 2))) atTop (𝓝 0) := by
    simpa using hnode.neg.sub hexcess
  apply hsum.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  rw [ccmActualHeadMatchedQuantilePolarDisplacement_eq_neg_error_sub_upperExcess n
    (Nat.zero_lt_of_lt hn)]
  ring

end RHTower
