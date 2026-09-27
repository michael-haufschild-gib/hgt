import GaloisForLFunctions.RHTower.CCMPrimeDeficitEntryBoundary
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# A polynomial budget for the complete entry boundary

After removing the limiting constant, the absolute sum of all boundary
entries is at most logarithm squared. The continuous boundary work thus
differs from the actual prime deficit by an explicit quadratic polynomial
in logarithmic time. No estimate on a Möbius partial sum is assumed.
-/

noncomputable section
open Filter
open scoped BigOperators
open scoped Topology

namespace RHTower

def ccmPrimeDeficitEntryTransient (n : ℕ) : ℝ :=
  2 * moebiusCoeff n *
    (ccmPrimeDeficitDilationRemainder (Real.log n) - ccmPrimeDeficitDilationLimit)

theorem abs_ccmPrimeDeficitEntryTransient_le (n : ℕ) :
    |ccmPrimeDeficitEntryTransient n| ≤ (Real.log n + 14) / (2 * n) := by
  by_cases hn : n = 0
  · simp [ccmPrimeDeficitEntryTransient, moebiusCoeff, hn]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hr := abs_ccmPrimeDeficitDilationRemainder_sub_limit_le (Real.log_natCast_nonneg n)
  rw [Real.exp_neg, Real.exp_log hnpos] at hr
  calc
    _ = 2 * (|moebiusCoeff n| *
        |ccmPrimeDeficitDilationRemainder (Real.log n) - ccmPrimeDeficitDilationLimit|) := by
      rw [ccmPrimeDeficitEntryTransient, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring
    _ ≤ 2 * ((n : ℝ)⁻¹ * (Real.log n + 14) / 4) := by
      gcongr
      simpa only [one_mul] using mul_le_mul (abs_moebiusCoeff_le_one n) hr
        (abs_nonneg _) zero_le_one
    _ = _ := by ring

theorem sum_abs_ccmPrimeDeficitEntryTransient_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, |ccmPrimeDeficitEntryTransient n|) ≤
      (Real.log N + 14) / 2 * (1 + Real.log N) := by
  have hh : (∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹) ≤ 1 + Real.log N := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
      harmonic_le_one_add_log N
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (Real.log N + 14) / 2 * (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
      calc
        _ ≤ (Real.log n + 14) / (2 * n) := abs_ccmPrimeDeficitEntryTransient_le n
        _ ≤ (Real.log N + 14) / (2 * n) := by
          gcongr
        _ = _ := by ring
    _ = (Real.log N + 14) / 2 * ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)

theorem sum_abs_ccmPrimeDeficitEntryTransient_half_le {T : ℝ} (hT : 0 ≤ T) :
    (∑ n ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊, |ccmPrimeDeficitEntryTransient n|) ≤
      (T + 28) * (T + 2) / 8 := by
  have hU : 1 ≤ ⌊Real.exp (T / 2)⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr (by linarith))
  have hlog : Real.log ⌊Real.exp (T / 2)⌋₊ ≤ T / 2 :=
    (Real.log_le_iff_le_exp (by exact_mod_cast hU)).mpr (Nat.floor_le (Real.exp_pos _).le)
  calc
    _ ≤ (Real.log ⌊Real.exp (T / 2)⌋₊ + 14) / 2 *
        (1 + Real.log ⌊Real.exp (T / 2)⌋₊) := sum_abs_ccmPrimeDeficitEntryTransient_le _
    _ ≤ (T / 2 + 14) / 2 * (1 + T / 2) := by gcongr
    _ = _ := by ring

theorem ccmPrimeDeficitShortBoundaryCorrection_sub_limit (T : ℝ) :
    ccmPrimeDeficitShortBoundaryCorrection T - 2 * ccmPrimeDeficitDilationLimit *
        (∑ n ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊, moebiusCoeff n) =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊, ccmPrimeDeficitEntryTransient n := by
  simp only [ccmPrimeDeficitShortBoundaryCorrection, ccmPrimeDeficitEntryTransient,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem abs_ccmLogChebyshevDeficitPrimitive_sub_shortBoundaryWork_le
    {T : ℝ} (hT : 0 ≤ T) :
    |ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitShortBoundaryWork T| ≤
      (T ^ 2 + 34 * T + 112) / 8 := by
  have he : ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitShortBoundaryWork T =
      (ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitShortQuadraticWork T -
        2 * ccmPrimeDeficitDilationLimit *
          (∑ n ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊, moebiusCoeff n)) -
            ∑ n ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊, ccmPrimeDeficitEntryTransient n := by
    rw [← ccmPrimeDeficitShortBoundaryCorrection_sub_limit, ccmPrimeDeficitShortBoundaryWork]
    ring
  rw [he]
  calc
    _ ≤ _ := abs_sub _ _
    _ ≤ (T + 14) / 2 + (T + 28) * (T + 2) / 8 :=
      add_le_add (abs_ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork_sub_limit_le hT)
        ((Finset.abs_sum_le_sum_abs _ _).trans (sum_abs_ccmPrimeDeficitEntryTransient_half_le hT))
    _ = _ := by ring

theorem tendsto_ccmPrimeDeficitShortBoundaryWork_normalized_error :
    Tendsto (fun T => Real.exp (-(T / 2)) *
      (ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitShortBoundaryWork T))
        atTop (𝓝 0) := by
  have hh : Tendsto (fun T : ℝ => T / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  have hp (n : ℕ) := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp hh
  have h := (((hp 2).const_mul (1 / 2)).add ((hp 1).const_mul (17 / 2))).add
    ((hp 0).const_mul 14)
  have hb : Tendsto
      (fun T : ℝ => Real.exp (-(T / 2)) * (T ^ 2 + 34 * T + 112) / 8)
        atTop (𝓝 0) := by
    convert h using 1 <;> (try simp only [Function.comp_apply, pow_zero, pow_one]) <;> ring
  apply squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-(T / 2)) * ((T ^ 2 + 34 * T + 112) / 8) :=
      mul_le_mul_of_nonneg_left (abs_ccmLogChebyshevDeficitPrimitive_sub_shortBoundaryWork_le hT)
        (Real.exp_pos _).le
    _ = _ := by ring

end RHTower
