import GaloisForLFunctions.RHTower.Sieve.MoebiusLogarithmicNormalizationRate
import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusOneLimit

/-!
# Quantitative modulus-one coprime logarithmic Möbius kernel

The integer two-logarithm normalization rate is transported to arbitrary real cutoffs.  Exact
floor decomposition retains the Möbius harmonic boundary and proves it has the same rate.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Filter Topology
open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

/-- Exact real-cutoff decomposition into the logarithmic Möbius partial sum and its boundary. -/
theorem coprimeLogMoebius_one_eq_partial (Y : ℝ) (hY : 1 ≤ Y) :
    coprimeLogMoebius 1 Y =
      moebiusLogHarmonicPartial ⌊Y⌋₊ +
        Real.log Y * RHTower.deningerHarmonicPartial ⌊Y⌋₊ := by
  let N : ℕ := ⌊Y⌋₊
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff Y |>.mpr hY
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hpartial : RHTower.deningerHarmonicPartial N =
      ∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ) := by
    rw [RHTower.deningerHarmonicPartial, Finset.sum_range_succ']
    simp
    convert RHTower.sum_range_succ_eq_sum_Icc
      (fun d : ℕ => ((moebius d : ℤ) : ℝ) / (d : ℝ)) N using 1 <;>
        push_cast <;> ring
  have hlogpartial : moebiusLogHarmonicPartial N =
      ∑ d ∈ Finset.Icc 1 N,
        -(((moebius d : ℤ) : ℝ) / (d : ℝ) * Real.log (d : ℝ)) := by
    rw [moebiusLogHarmonicPartial, Finset.sum_range_succ']
    simp only [moebiusLogHarmonicTerm_zero, add_zero]
    rw [RHTower.sum_range_succ_eq_sum_Icc moebiusLogHarmonicTerm N]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd0 : (0 : ℝ) < (d : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd).1)
    rw [moebiusLogHarmonicTerm, Real.rpow_neg_one]
    field_simp
  have hmain :
      (∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ) *
        Real.log ((N : ℝ) / (d : ℝ))) =
      moebiusLogHarmonicPartial N +
        Real.log (N : ℝ) * RHTower.deningerHarmonicPartial N := by
    rw [hpartial, hlogpartial, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd0 : (0 : ℝ) < (d : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd).1)
    rw [Real.log_div hN0.ne' hd0.ne']
    ring
  rw [coprimeLogMoebius_one_eq_floor Y hY, show ⌊Y⌋₊ = N from rfl, hmain]
  rw [Real.log_div hY0.ne' hN0.ne']
  ring

/-- The modulus-one real-cutoff kernel has the quantitative two-logarithm rate. -/
theorem exists_abs_coprimeLogMoebius_one_sub_one_log_sq_rate :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Y : ℝ in atTop,
      |coprimeLogMoebius 1 Y - 1| ≤ C / (Real.log Y) ^ 2 := by
  obtain ⟨A, hA, hpartial⟩ :=
    exists_abs_moebiusLogHarmonicPartial_sub_one_log_sq_rate
  obtain ⟨B, hB, hharmonic⟩ := exists_abs_deningerHarmonicPartial_log_rate
  let E : ℝ := 2 * B + B / 3
  let C : ℝ := 4 * (A + 2 * E)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hfloor : Tendsto (fun Y : ℝ => ⌊Y⌋₊) atTop atTop := tendsto_nat_floor_atTop
  have hpartialY : ∀ᶠ Y : ℝ in atTop,
      |moebiusLogHarmonicPartial ⌊Y⌋₊ - 1| ≤
        A / (Real.log (⌊Y⌋₊ : ℝ)) ^ 2 := hfloor.eventually hpartial
  have hharmonicY : ∀ᶠ Y : ℝ in atTop,
      |RHTower.deningerHarmonicPartial ⌊Y⌋₊| ≤
        2 * B / (Real.log (⌊Y⌋₊ : ℝ)) ^ 4 +
          B / (3 * (Real.log (⌊Y⌋₊ : ℝ)) ^ 3) := hfloor.eventually hharmonic
  filter_upwards [hpartialY, hharmonicY,
    eventually_ge_atTop (Real.exp 1 + 1)] with
      Y hpartY hharmY hYe
  let N : ℕ := ⌊Y⌋₊
  have hY1 : 1 ≤ Y := le_trans (by linarith [Real.exp_pos 1]) hYe
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff Y |>.mpr hY1
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
  have hNle : (N : ℝ) ≤ Y := Nat.floor_le hY0.le
  have hYlt : Y < (N : ℝ) + 1 := Nat.lt_floor_add_one Y
  have hNge : Real.exp 1 ≤ (N : ℝ) := by
    linarith
  have hlogN : 1 ≤ Real.log (N : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hNge
  have hlogN0 : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlogN
  have hlogY0 : 0 < Real.log Y := Real.log_pos
    (lt_of_lt_of_le (by linarith [Real.exp_pos 1] : (1 : ℝ) < Real.exp 1 + 1) hYe)
  have htwoN : Y ≤ 2 * (N : ℝ) := by
    have hNcast1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith
  have hlogY_le : Real.log Y ≤ 2 * Real.log (N : ℝ) := by
    have hlogmono : Real.log Y ≤ Real.log (2 * (N : ℝ)) :=
      Real.log_le_log hY0 htwoN
    have hlogtwo : Real.log (2 : ℝ) ≤ Real.log (N : ℝ) := by
      have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at h
        exact h
      exact le_trans hlog2 hlogN
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne'] at hlogmono
    linarith
  have hcollapse :
      2 * B / (Real.log (N : ℝ)) ^ 4 + B / (3 * (Real.log (N : ℝ)) ^ 3) ≤
        E / (Real.log (N : ℝ)) ^ 3 := by
    have hp3 : 0 < (Real.log (N : ℝ)) ^ 3 := pow_pos hlogN0 3
    have hp34 : (Real.log (N : ℝ)) ^ 3 ≤ (Real.log (N : ℝ)) ^ 4 := by
      calc
        (Real.log (N : ℝ)) ^ 3 ≤
            (Real.log (N : ℝ)) ^ 3 * Real.log (N : ℝ) :=
          le_mul_of_one_le_right (pow_nonneg hlogN0.le 3) hlogN
        _ = (Real.log (N : ℝ)) ^ 4 := by ring
    have hfirst : 2 * B / (Real.log (N : ℝ)) ^ 4 ≤
        2 * B / (Real.log (N : ℝ)) ^ 3 := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [one_div] using one_div_le_one_div_of_le hp3 hp34)
        (mul_nonneg (by norm_num) hB)
    calc
      2 * B / (Real.log (N : ℝ)) ^ 4 + B / (3 * (Real.log (N : ℝ)) ^ 3) ≤
          2 * B / (Real.log (N : ℝ)) ^ 3 + B / (3 * (Real.log (N : ℝ)) ^ 3) :=
        add_le_add hfirst le_rfl
      _ = E / (Real.log (N : ℝ)) ^ 3 := by dsimp [E]; ring
  have hboundary : |Real.log Y * RHTower.deningerHarmonicPartial N| ≤
      2 * E / (Real.log (N : ℝ)) ^ 2 := by
    rw [abs_mul, abs_of_pos hlogY0]
    calc
      Real.log Y * |RHTower.deningerHarmonicPartial N| ≤
          (2 * Real.log (N : ℝ)) *
            (E / (Real.log (N : ℝ)) ^ 3) :=
        mul_le_mul hlogY_le (le_trans hharmY hcollapse) (abs_nonneg _) (by positivity)
      _ = 2 * E / (Real.log (N : ℝ)) ^ 2 := by field_simp
  have htotal : |coprimeLogMoebius 1 Y - 1| ≤
      (A + 2 * E) / (Real.log (N : ℝ)) ^ 2 := by
    rw [coprimeLogMoebius_one_eq_partial Y hY1]
    change |moebiusLogHarmonicPartial N +
        Real.log Y * RHTower.deningerHarmonicPartial N - 1| ≤ _
    calc
      |moebiusLogHarmonicPartial N +
          Real.log Y * RHTower.deningerHarmonicPartial N - 1| ≤
        |moebiusLogHarmonicPartial N - 1| +
          |Real.log Y * RHTower.deningerHarmonicPartial N| := by
        rw [show moebiusLogHarmonicPartial N +
            Real.log Y * RHTower.deningerHarmonicPartial N - 1 =
          (moebiusLogHarmonicPartial N - 1) +
            Real.log Y * RHTower.deningerHarmonicPartial N by ring]
        exact abs_add_le _ _
      _ ≤ A / (Real.log (N : ℝ)) ^ 2 +
          2 * E / (Real.log (N : ℝ)) ^ 2 := add_le_add hpartY hboundary
      _ = (A + 2 * E) / (Real.log (N : ℝ)) ^ 2 := by ring
  have hsq : (Real.log Y) ^ 2 ≤ 4 * (Real.log (N : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (2 * Real.log (N : ℝ) - Real.log Y)]
  have hrecip : 1 / (Real.log (N : ℝ)) ^ 2 ≤ 4 / (Real.log Y) ^ 2 := by
    rw [div_le_div_iff₀ (pow_pos hlogN0 2) (pow_pos hlogY0 2)]
    nlinarith
  calc
    |coprimeLogMoebius 1 Y - 1| ≤
        (A + 2 * E) / (Real.log (N : ℝ)) ^ 2 := htotal
    _ ≤ (A + 2 * E) * (4 / (Real.log Y) ^ 2) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [one_div] using hrecip)
        (add_nonneg hA (mul_nonneg (by norm_num) hE))
    _ = C / (Real.log Y) ^ 2 := by dsimp [C]; ring

end

end RHTower.Sieve
