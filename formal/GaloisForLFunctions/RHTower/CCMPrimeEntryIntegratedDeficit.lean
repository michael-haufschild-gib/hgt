import GaloisForLFunctions.RHTower.CCMPrimeDeficitWeilFlux

/-!
# The unweighted primitive of the actual deficit

The finite prime background overlap and its weighted complement give the
unweighted prefix integral without an interchange of infinite sums.
-/

noncomputable section
open MeasureTheory Set

namespace RHTower

theorem integral_ccmPrimeEntryPrefix_eq_background (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ t) =
      ccmPrimeEntryBackgroundPrefix T ⌊Real.exp T⌋₊ + mertensSum ⌊Real.exp T⌋₊ -
        Real.exp (-T) *
          (ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ T + Chebyshev.psi (Real.exp T)) := by
  have hm : IntervalIntegrable
      (fun t => (1 - Real.exp (-t)) * ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ t) volume 0 T :=
    ((continuous_const.sub (Real.continuous_exp.comp continuous_neg)).mul
      (continuous_ccmPrimeEntryPrefix _)).intervalIntegrable 0 T
  have hw : IntervalIntegrable
      (fun t => Real.exp (-t) * ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ t) volume 0 T :=
    ((Real.continuous_exp.comp continuous_neg).mul
      (continuous_ccmPrimeEntryPrefix _)).intervalIntegrable 0 T
  calc
    _ = ∫ t in (0 : ℝ)..T,
        (1 - Real.exp (-t)) * ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ t +
          Real.exp (-t) * ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ t := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add hm hw,
        integral_ccmPrimeEntryPrefix_background, integral_exp_neg_mul_ccmPrimeEntryPrefix]
      ring

/-- The exact unweighted integral, retaining the terminal prime prefix and
Chebyshev sum in its boundary term. -/
theorem integral_ccmLogChebyshevDeficitPrimitive_eq_background {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ccmLogChebyshevDeficitPrimitive t) =
      Real.exp T - 1 - T - ccmPrimeEntryBackgroundPrefix T ⌊Real.exp T⌋₊ -
        mertensSum ⌊Real.exp T⌋₊ + Real.exp (-T) *
          (ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ T + Chebyshev.psi (Real.exp T)) := by
  have hp (t : ℝ) (ht : t ∈ uIcc 0 T) :
      ccmLogChebyshevDeficitPrimitive t =
        (Real.exp t - 1) - ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ t := by
    have ht' := uIcc_of_le hT ▸ ht
    exact ccmLogChebyshevDeficitPrimitive_eq_entry_prefix ht'.1
      (Nat.floor_mono (Real.exp_le_exp.mpr ht'.2))
  have hb : IntervalIntegrable (fun t : ℝ => Real.exp t - 1) volume 0 T :=
    (Real.continuous_exp.sub continuous_const).intervalIntegrable 0 T
  rw [intervalIntegral.integral_congr hp,
    intervalIntegral.integral_sub hb
      ((continuous_ccmPrimeEntryPrefix _).intervalIntegrable 0 T),
    integral_ccmPrimeEntryPrefix_eq_background,
    intervalIntegral.integral_sub (Real.continuous_exp.intervalIntegrable 0 T)
      intervalIntegrable_const, integral_exp, intervalIntegral.integral_const]
  simp only [Real.exp_zero, sub_zero, smul_eq_mul, mul_one]
  ring

end RHTower
