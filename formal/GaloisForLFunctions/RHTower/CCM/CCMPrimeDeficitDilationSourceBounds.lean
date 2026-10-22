import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitDilationConservation
import GaloisForLFunctions.RHTower.LogarithmicEntryIntegration
import GaloisForLFunctions.RHTower.HarmonicStirlingExactBounds

/-!
# Quantitative control of the complete elementary dilation source

The source is the integral of an elementary harmonic-minus-logarithmic
force. Exact harmonic and Stirling bounds control its centered force,
including every floor oscillation. The resulting polynomial bound is on
the complete dilation source; its signed Möbius inverse remains separate.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RHTower

def ccmPrimeDeficitDilationForce (T : ℝ) : ℝ :=
  Real.exp T * logarithmicEntrySum (fun n => (n : ℝ)⁻¹) T -
    logarithmicEntrySum (fun n => Real.log n) T

def ccmPrimeDeficitDilationRemainder (T : ℝ) : ℝ :=
  ccmPrimeDeficitDilationSource T -
    (Real.eulerMascheroniConstant + 1) * (Real.exp T - 1) + Real.log (2 * Real.pi) / 2 * T

theorem intervalIntegrable_ccmPrimeDeficitDilationForce {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable ccmPrimeDeficitDilationForce volume 0 T := by
  have hlog : IntervalIntegrable (logarithmicEntrySum (fun n => Real.log n)) volume 0 T := by
    simpa only [one_mul] using
      intervalIntegrable_mul_logarithmicEntrySum (fun n => Real.log n)
        (fun _ => 1) continuous_const hT
  exact (intervalIntegrable_mul_logarithmicEntrySum (fun n => (n : ℝ)⁻¹)
    Real.exp Real.continuous_exp hT).sub hlog

theorem integral_ccmPrimeDeficitDilationForce {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ccmPrimeDeficitDilationForce t) = ccmPrimeDeficitDilationSource T := by
  have hlog : IntervalIntegrable (logarithmicEntrySum (fun n => Real.log n)) volume 0 T := by
    simpa only [one_mul] using
      intervalIntegrable_mul_logarithmicEntrySum (fun n => Real.log n)
        (fun _ => 1) continuous_const hT
  have hlogint := integral_mul_logarithmicEntrySum (fun n => Real.log n)
    (fun _ => 1) continuous_const hT
  simp only [one_mul, intervalIntegral.integral_const, smul_eq_mul, mul_one] at hlogint
  change (∫ t in (0 : ℝ)..T, Real.exp t * logarithmicEntrySum (fun n => (n : ℝ)⁻¹) t -
    logarithmicEntrySum (fun n => Real.log n) t) = _
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_mul_logarithmicEntrySum (fun n => (n : ℝ)⁻¹)
      Real.exp Real.continuous_exp hT) hlog,
    integral_mul_logarithmicEntrySum _ _ Real.continuous_exp hT, hlogint]
  have hsum : (∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
      (n : ℝ)⁻¹ * ∫ t in Real.log n..T, Real.exp t) =
        Real.exp T * (∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, (n : ℝ)⁻¹) -
          (⌊Real.exp T⌋₊ : ℝ) := by
    calc
      _ = ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, (Real.exp T * (n : ℝ)⁻¹ - 1) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        rw [integral_exp, Real.exp_log hnpos, mul_sub, inv_mul_cancel₀ hnpos.ne']
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
          Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  rw [hsum]
  rfl

/-- The actual elementary force retains the exact Stirling constant, with
a linear bound on its complete signed floor error. -/
theorem abs_ccmPrimeDeficitDilationForce_centered_le {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitDilationForce T - (Real.eulerMascheroniConstant + 1) * Real.exp T +
      Real.log (2 * Real.pi) / 2| ≤ T / 2 + 2 := by
  let N := ⌊Real.exp T⌋₊
  let H : ℝ := ((harmonic N : ℚ) : ℝ)
  let S : ℝ := ∑ k ∈ Finset.Icc 1 N, Real.log k
  let c : ℝ := Real.log (2 * Real.pi) / 2
  have hN : 1 ≤ N :=
    (Nat.le_floor_iff (Real.exp_pos T).le).mpr (by simpa using Real.one_le_exp_iff.mpr hT)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos := zero_lt_one.trans_le hNR
  have hNx : (N : ℝ) ≤ Real.exp T := Nat.floor_le (Real.exp_pos T).le
  have hxN : Real.exp T < (N : ℝ) + 1 := Nat.lt_floor_add_one (Real.exp T)
  have hL0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNR
  have hLT : Real.log (N : ℝ) ≤ T := (Real.log_le_iff_le_exp hpos).mpr hNx
  have hH := harmonic_mascheroni_half_bounds hN
  have hH0 : 0 ≤ H - Real.log (N : ℝ) - Real.eulerMascheroniConstant :=
    (by positivity : (0 : ℝ) ≤ 1 / (2 * ((N : ℝ) + 1))).trans hH.1
  have hU0 : 0 ≤ Real.exp T * (H - Real.log (N : ℝ) - Real.eulerMascheroniConstant) :=
    mul_nonneg (Real.exp_pos T).le hH0
  have hU1 : Real.exp T * (H - Real.log (N : ℝ) - Real.eulerMascheroniConstant) ≤ 1 := by
    apply (mul_le_mul_of_nonneg_left hH.2 (Real.exp_pos T).le).trans
    rw [mul_one_div, div_le_one (by positivity : (0 : ℝ) < 2 * N)]
    linarith only [hxN, hNR]
  have hSt : (N : ℝ) * Real.log N - N + Real.log N / 2 + c ≤ S ∧
      S ≤ (N : ℝ) * Real.log N - N + Real.log N / 2 + c + 1 / (12 * N) :=
    sum_log_Icc_exact_stirling_bounds hN
  have hE0 : 0 ≤ S - ((N : ℝ) * Real.log N - N + Real.log N / 2 + c) := by
    linarith only [hSt.1]
  have hE1 : S - ((N : ℝ) * Real.log N - N + Real.log N / 2 + c) ≤ 1 := by
    have hb : 1 / (12 * (N : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < 12 * N)]
      linarith only [hNR]
    linarith only [hSt.2, hb]
  have hDL0 : 0 ≤ (Real.exp T - N) * Real.log (N : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hNx) hL0
  have hDL1 : (Real.exp T - N) * Real.log (N : ℝ) ≤ Real.log (N : ℝ) := by
    have h := mul_le_mul_of_nonneg_right (show Real.exp T - (N : ℝ) ≤ 1 by linarith) hL0
    simpa only [one_mul] using h
  have heq : ccmPrimeDeficitDilationForce T = Real.exp T * H - S := by
    simp only [ccmPrimeDeficitDilationForce, logarithmicEntrySum, H, S, N,
      harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [heq, abs_le]
  change -(T / 2 + 2) ≤ Real.exp T * H - S -
    (Real.eulerMascheroniConstant + 1) * Real.exp T + c ∧
      Real.exp T * H - S - (Real.eulerMascheroniConstant + 1) * Real.exp T + c ≤ T / 2 + 2
  constructor <;> nlinarith only [hU0, hU1, hE0, hE1, hDL0, hDL1, hNx, hxN, hLT]

theorem ccmPrimeDeficitDilationRemainder_eq_integral {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitDilationRemainder T =
      ∫ t in (0 : ℝ)..T, ccmPrimeDeficitDilationForce t -
        (Real.eulerMascheroniConstant + 1) * Real.exp t + Real.log (2 * Real.pi) / 2 := by
  have he : IntervalIntegrable
      (fun t : ℝ => (Real.eulerMascheroniConstant + 1) * Real.exp t) volume 0 T :=
    (Real.continuous_exp.const_mul _).intervalIntegrable 0 T
  rw [intervalIntegral.integral_add ((intervalIntegrable_ccmPrimeDeficitDilationForce hT).sub he)
      intervalIntegrable_const,
    intervalIntegral.integral_sub (intervalIntegrable_ccmPrimeDeficitDilationForce hT) he,
    intervalIntegral.integral_const_mul, integral_exp, integral_ccmPrimeDeficitDilationForce hT,
    intervalIntegral.integral_const]
  simp only [Real.exp_zero, sub_zero, smul_eq_mul, ccmPrimeDeficitDilationRemainder]
  ring

/-- Complete signed control after removing the explicitly known pole and
Stirling terms. This bounds the dilation sum, not its Möbius inverse. -/
theorem abs_ccmPrimeDeficitDilationRemainder_le {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitDilationRemainder T| ≤ T ^ 2 / 4 + 2 * T := by
  let f : ℝ → ℝ := fun t => ccmPrimeDeficitDilationForce t -
    (Real.eulerMascheroniConstant + 1) * Real.exp t + Real.log (2 * Real.pi) / 2
  have hi : IntervalIntegrable f volume 0 T :=
    ((intervalIntegrable_ccmPrimeDeficitDilationForce hT).sub
      ((Real.continuous_exp.const_mul _).intervalIntegrable 0 T)).add intervalIntegrable_const
  have hia : IntervalIntegrable (fun t => |f t|) volume 0 T := by
    simpa only [Real.norm_eq_abs] using hi.norm
  have hb : IntervalIntegrable (fun t : ℝ => t / 2 + 2) volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => t ^ 2 / 4 + 2 * t) (t / 2 + 2) t := by
    convert! (((hasDerivAt_id t).pow 2).div_const 4).add ((hasDerivAt_id t).const_mul 2) using 1
    norm_num
    ring
  rw [ccmPrimeDeficitDilationRemainder_eq_integral hT]
  calc
    _ ≤ ∫ t in (0 : ℝ)..T, |f t| := intervalIntegral.abs_integral_le_integral_abs hT
    _ ≤ ∫ t in (0 : ℝ)..T, (t / 2 + 2) :=
      intervalIntegral.integral_mono_on hT hia hb
        (fun t ht => abs_ccmPrimeDeficitDilationForce_centered_le ht.1)
    _ = _ := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hb]
      ring

end RHTower
