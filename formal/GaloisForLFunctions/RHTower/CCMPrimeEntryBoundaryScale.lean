import GaloisForLFunctions.RHTower.CCMPrimeEntryPairBoundary

/-!
# The omitted boundary has exact exponential scale

PNT gives the two normalized boundary charges the limits two and one.
The squared boundary correction is consequently asymptotic to 5 exp(T).
Replacing the finite pair overlap by its infinite limit therefore creates
exponential growth even though the actual centered energy is o(exp(T)).
This is an unconditional failure of that proposed simplification.
-/

noncomputable section
open MeasureTheory Filter Set

namespace RHTower

private theorem tendsto_psi_exp_scaled :
    Tendsto (fun t : ℝ => Real.exp (-t) * Chebyshev.psi (Real.exp t)) atTop (nhds 1) := by
  have hident (x : ℝ) : chebyshevPsiReal x = Chebyshev.psi x := by
    rw [chebyshevPsiReal_eq_sum_range, Chebyshev.psi_eq_sum_Icc]
    congr 1
    ext n
    simp
  have h := tendsto_chebyshevPsiReal_div.comp Real.tendsto_exp_atTop
  simpa only [Function.comp_def, hident, Real.exp_neg, div_eq_mul_inv, mul_comm] using h

theorem tendsto_ccmPrimeEntryPrefix_scaled :
    Tendsto (fun T : ℝ => Real.exp (-T) * ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ T)
      atTop (nhds 1) := by
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub Real.tendsto_exp_neg_atTop_nhds_zero).sub
    tendsto_ccmLogChebyshevDeficitPrimitive_scaled_zero
  simp only [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with T hT
  rw [ccmLogChebyshevDeficitPrimitive_eq_entry_prefix hT le_rfl]
  have hc : Real.exp (-T) * Real.exp T = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith only [hc]

theorem tendsto_ccmPrimeDeficitCriticalEnergy_integral_scaled_zero :
    Tendsto (fun T : ℝ => Real.exp (-T) *
      ∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) atTop (nhds 0) := by
  apply tendsto_exp_neg_mul_primitive_zero ccmPrimeDeficitCriticalEnergy
    continuous_ccmPrimeDeficitCriticalEnergy.intervalIntegrable
  have h := tendsto_ccmLogChebyshevDeficitPrimitive_scaled_zero.pow 2
  norm_num only [zero_pow (by norm_num : 2 ≠ 0)] at h
  refine h.congr fun t => ?_
  unfold ccmPrimeDeficitCriticalEnergy
  ring

/-- The boundary has exact leading constant five, from the two actual
arithmetic charges. It is not a lower-order approximation error. -/
theorem tendsto_ccmPrimeEntryPairBoundary_scaled :
    Tendsto (fun T : ℝ => Real.exp (-T) * ccmPrimeEntryPairBoundary T)
      atTop (nhds 5) := by
  have h := ((tendsto_ccmPrimeEntryPrefix_scaled.add tendsto_psi_exp_scaled).pow 2).add
    (tendsto_psi_exp_scaled.pow 2)
  norm_num at h
  refine h.congr fun T => ?_
  unfold ccmPrimeEntryPairBoundary
  ring

/-- The candidate obtained by using infinite overlap while keeping the
original finite background and mixed term. -/
def ccmPrimeEntryUncorrectedEnergy (T : ℝ) : ℝ :=
  Real.exp T - Real.exp (-T) - 2 * T -
    2 * ccmPrimeEntryBackgroundPrefix T ⌊Real.exp T⌋₊ +
      ccmPrimeEntryPairLimit ⌊Real.exp T⌋₊

theorem ccmPrimeEntryUncorrectedEnergy_eq {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeEntryUncorrectedEnergy T =
      (∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) + ccmPrimeEntryPairBoundary T := by
  rw [ccmPrimeDeficitCriticalEnergy_integral_eq_pair_limit hT]
  unfold ccmPrimeEntryUncorrectedEnergy
  ring

/-- Dropping the two-charge correction produces an artificial 5 exp(T)
term in the exact arithmetic source, independently of RH. -/
theorem tendsto_ccmPrimeEntryUncorrectedEnergy_scaled :
    Tendsto (fun T : ℝ => Real.exp (-T) * ccmPrimeEntryUncorrectedEnergy T)
      atTop (nhds 5) := by
  have h := tendsto_ccmPrimeDeficitCriticalEnergy_integral_scaled_zero.add
    tendsto_ccmPrimeEntryPairBoundary_scaled
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with T hT
  rw [ccmPrimeEntryUncorrectedEnergy_eq hT, mul_add]

theorem eventually_exp_le_ccmPrimeEntryUncorrectedEnergy :
    ∀ᶠ T : ℝ in atTop, Real.exp T ≤ ccmPrimeEntryUncorrectedEnergy T := by
  have h := tendsto_ccmPrimeEntryUncorrectedEnergy_scaled.eventually
    (eventually_gt_nhds (by norm_num : (1 : ℝ) < 5))
  filter_upwards [h] with T hT
  have hm := mul_lt_mul_of_pos_left hT (Real.exp_pos T)
  have hc : Real.exp T * Real.exp (-T) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  simpa only [mul_one, ← mul_assoc, hc, one_mul] using hm.le

end RHTower
