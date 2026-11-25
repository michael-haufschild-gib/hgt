import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Coefficients

/-! # Exponential separation of the odds for equal counts at different energies -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization

open Filter Topology Set MeasureTheory

private theorem exp_gap {x y : ℝ} (hxy : x < y) :
    Tendsto (fun h : Ioi (0:ℝ) => Real.exp ((x-y)/h.val)) criticalApproach (𝓝 0) := by
  have hv : Tendsto (Subtype.val : Ioi (0:ℝ) → ℝ) criticalApproach (𝓝[>] 0) := tendsto_comap
  have H := (tendsto_inv_nhdsGT_zero.comp hv).const_mul_atTop (sub_pos.mpr hxy)
  have T := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp H)
  simpa only [Function.comp_def,← neg_mul,neg_sub,div_eq_mul_inv] using T

/-- A gap in the rescaled energies dominates any finite ratio of critical coefficients. -/
private theorem odds_zero {N D A B : Ioi (0:ℝ) → ℝ} {x y u v : ℝ} (hxy : x < y) (hv : 0 < v)
    (hA : Tendsto A criticalApproach (𝓝 u)) (hB : Tendsto B criticalApproach (𝓝 v))
    (hN : ∀ h, 0 ≤ N h) (hU : ∀ h, N h ≤ Real.exp (x/h.val)*A h)
    (hL : ∀ h, Real.exp (y/h.val)*B h ≤ D h) :
    Tendsto (fun h => N h/D h) criticalApproach (𝓝 0) := by
  have H := (exp_gap hxy).mul (hA.div hB hv.ne')
  rw [zero_mul] at H
  apply squeeze_zero' _ _ H
  · filter_upwards [hB.eventually_const_lt hv] with h hb
    exact div_nonneg (hN h) ((mul_pos (Real.exp_pos _) hb).le.trans (hL h))
  · filter_upwards [hB.eventually_const_lt hv] with h hb
    have hpos := mul_pos (Real.exp_pos (y/h.val)) hb
    calc N h/D h ≤ (Real.exp (x/h.val)*A h)/D h :=
           div_le_div_of_nonneg_right (hU h) (hpos.le.trans (hL h))
         _ ≤ (Real.exp (x/h.val)*A h)/(Real.exp (y/h.val)*B h) :=
           div_le_div_of_nonneg_left ((hN h).trans (hU h)) hpos (hL h)
         _ = _ := by
           rw [sub_div,Real.exp_sub]
           exact (div_mul_div_comm _ _ (A h) (B h)).symm

private theorem coefficient_nonneg (c d : ℝ) (h : Ioi (0:ℝ)) (s : ℝ) (k : ℕ) :
    0 ≤ coefficient (added c d h) s k := by
  rw [coefficient,← slice_mass (added c d h) s h k]
  exact mul_nonneg (_root_.RHTower.finiteSquarefreePartition_pos _ _).le (slice (added c d h) s h k).mass.property

private theorem limit_pos {c d : ℝ} (hc : 0 < c) (hcd : c < d) (k : ℕ) :
    0 < Real.log (d/c)^k/k.factorial :=
  div_pos (pow_pos (Real.log_pos ((one_lt_div hc).mpr hcd)) k) (Nat.cast_pos.mpr (Nat.factorial_pos k))

/-- Every fixed count slice has positive weight eventually, at any real inverse temperature. -/
theorem coefficient_eventually_pos {c d : ℝ} (hc : 0 < c) (hcd : c < d) (s : ℝ) (k : ℕ) :
    ∀ᶠ h in criticalApproach, 0 < coefficient (added c d h) s k := by
  filter_upwards [(coefficient_limit hc hcd k).eventually_const_lt (limit_pos hc hcd k)] with h hh
  rcases le_total 0 (1-s) with ht | ht
  · have H := (coefficient_tilt_pos c d h ht k).1
    rw [sub_sub_cancel] at H
    exact (mul_pos (Real.exp_pos _) hh).trans_le H
  · have H := (coefficient_tilt_neg c d h ht k).1
    rw [sub_sub_cancel] at H
    exact (mul_pos (Real.exp_pos _) hh).trans_le H

/-- Above unit inverse temperature, high-to-low odds vanish for every fixed positive count. -/
theorem high_odds_above {c d b e s : ℝ} (hc : 0 < c) (hcd : c < d) (hdb : d < b) (hbe : b < e)
    (hs : 1 < s) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun h => coefficient (added b e h) s k / coefficient (added c d h) s k)
      criticalApproach (𝓝 0) := by
  let t := 1-s
  have ht : t < 0 := sub_neg.mpr hs
  apply odds_zero (x := t*(k*b)) (y := t*(k*d))
    (mul_lt_mul_of_neg_left (mul_lt_mul_of_pos_left hdb (Nat.cast_pos.mpr hk)) ht) (limit_pos hc hcd k)
    (coefficient_limit (hc.trans (hcd.trans hdb)) hbe k) (coefficient_limit hc hcd k)
    (fun h => coefficient_nonneg b e h s k)
  · intro h
    simpa only [t,sub_sub_cancel,mul_div_assoc] using (coefficient_tilt_neg b e h ht.le k).2
  · intro h
    simpa only [t,sub_sub_cancel,mul_div_assoc] using (coefficient_tilt_neg c d h ht.le k).1

/-- Below unit inverse temperature, low-to-high odds vanish on the very same count slice. -/
theorem low_odds_below {c d b e s : ℝ} (hc : 0 < c) (hcd : c < d) (hdb : d < b) (hbe : b < e)
    (hs : s < 1) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun h => coefficient (added c d h) s k / coefficient (added b e h) s k)
      criticalApproach (𝓝 0) := by
  let t := 1-s
  have ht : 0 < t := sub_pos.mpr hs
  have hb := hc.trans (hcd.trans hdb)
  apply odds_zero (x := t*(k*d)) (y := t*(k*b))
    (mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hdb (Nat.cast_pos.mpr hk)) ht) (limit_pos hb hbe k)
    (coefficient_limit hc hcd k) (coefficient_limit hb hbe k) (fun h => coefficient_nonneg c d h s k)
  · intro h
    simpa only [t,sub_sub_cancel,mul_div_assoc] using (coefficient_tilt_pos c d h ht.le k).2
  · intro h
    simpa only [t,sub_sub_cancel,mul_div_assoc] using (coefficient_tilt_pos b e h ht.le k).1

#print axioms coefficient_eventually_pos
#print axioms high_odds_above
#print axioms low_odds_below

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization
