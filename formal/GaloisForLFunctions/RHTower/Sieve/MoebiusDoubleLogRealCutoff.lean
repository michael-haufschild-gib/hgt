import GaloisForLFunctions.RHTower.Sieve.MoebiusDoubleLogNormalization
import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusOneLimit

open Finset ArithmeticFunction Filter Topology
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Quadratic logarithmic Möbius kernel at a real cutoff. -/
def moebiusDoubleLogKernelReal (Y : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊Y⌋₊,
    ((moebius d : ℤ) : ℝ) / (d : ℝ) * Real.log (Y / (d : ℝ)) ^ (2 : ℕ)

/-- Exact transfer of the real-cutoff quadratic kernel to its integer floor. -/
theorem moebiusDoubleLogKernelReal_eq_floor (Y : ℝ) (hY : 1 ≤ Y) :
    moebiusDoubleLogKernelReal Y =
      moebiusDoubleLogKernel ⌊Y⌋₊ +
        2 * Real.log (Y / (⌊Y⌋₊ : ℝ)) *
          coprimeLogMoebius 1 (⌊Y⌋₊ : ℝ) +
        Real.log (Y / (⌊Y⌋₊ : ℝ)) ^ (2 : ℕ) *
          RHTower.deningerHarmonicPartial ⌊Y⌋₊ := by
  classical
  let N : ℕ := ⌊Y⌋₊
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff Y |>.mpr hY
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlinear : coprimeLogMoebius 1 (N : ℝ) =
      ∑ d ∈ Finset.Icc 1 N,
        ((moebius d : ℤ) : ℝ) / (d : ℝ) *
          Real.log ((N : ℝ) / (d : ℝ)) := by
    rw [coprimeLogMoebius, Nat.floor_natCast]
    rw [Finset.filter_true_of_mem (fun d _ => Nat.coprime_one_left d)]
  have hpartial : RHTower.deningerHarmonicPartial N =
      ∑ d ∈ Finset.Icc 1 N,
        ((moebius d : ℤ) : ℝ) / (d : ℝ) := by
    rw [RHTower.deningerHarmonicPartial, Finset.sum_range_succ']
    simp
    convert RHTower.sum_range_succ_eq_sum_Icc
      (fun d : ℕ => ((moebius d : ℤ) : ℝ) / (d : ℝ)) N using 1
    all_goals push_cast
    all_goals ring
  rw [moebiusDoubleLogKernelReal, moebiusDoubleLogKernel,
    show ⌊Y⌋₊ = N from rfl, hlinear, hpartial,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hlog : Real.log (Y / (d : ℝ)) =
      Real.log ((N : ℝ) / (d : ℝ)) + Real.log (Y / (N : ℝ)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [hlog]
  ring

/-- Taking a natural floor preserves the logarithmic scale. -/
theorem tendsto_log_natFloor_div_log_one :
    Tendsto (fun Y : ℝ => Real.log (⌊Y⌋₊ : ℝ) / Real.log Y) atTop (𝓝 1) := by
  have hfloorRatio : Tendsto (fun Y : ℝ => ((⌊Y⌋₊ : ℕ) : ℝ) / Y)
      atTop (𝓝 1) := tendsto_nat_floor_div_atTop
  have hlogRatio : Tendsto
      (fun Y : ℝ => Real.log (((⌊Y⌋₊ : ℕ) : ℝ) / Y)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hfloorRatio
  have hgap : Tendsto
      (fun Y : ℝ => Real.log (⌊Y⌋₊ : ℝ) - Real.log Y) atTop (𝓝 0) := by
    refine hlogRatio.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    have hfloor1 : 1 ≤ ⌊Y⌋₊ := Nat.one_le_floor_iff Y |>.mpr hY
    rw [Real.log_div (by positivity) (by positivity)]
  have hlog : Tendsto (fun Y : ℝ => Real.log Y) atTop atTop := Real.tendsto_log_atTop
  have hsmall : Tendsto
      (fun Y : ℝ => (Real.log (⌊Y⌋₊ : ℝ) - Real.log Y) / Real.log Y)
      atTop (𝓝 0) := hgap.div_atTop hlog
  have hadd := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add hsmall
  rw [add_zero] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
  have hlogne : Real.log Y ≠ 0 := (Real.log_pos (by linarith)).ne'
  field_simp [hlogne]
  ring

/-- The real-cutoff quadratic logarithmic Möbius kernel has leading coefficient two. -/
theorem tendsto_moebiusDoubleLogKernelReal_div_log_two :
    Tendsto (fun Y : ℝ => moebiusDoubleLogKernelReal Y / Real.log Y)
      atTop (𝓝 2) := by
  have hfloor : Tendsto (fun Y : ℝ => ⌊Y⌋₊) atTop atTop := tendsto_nat_floor_atTop
  have hfloorCast : Tendsto (fun Y : ℝ => ((⌊Y⌋₊ : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hfloor
  have hlog : Tendsto (fun Y : ℝ => Real.log Y) atTop atTop := Real.tendsto_log_atTop
  have hmainRatio : Tendsto
      (fun Y : ℝ => moebiusDoubleLogKernel ⌊Y⌋₊ /
        Real.log (⌊Y⌋₊ : ℝ)) atTop (𝓝 2) :=
    tendsto_moebiusDoubleLogKernel_div_log_two.comp hfloor
  have hmain : Tendsto
      (fun Y : ℝ => moebiusDoubleLogKernel ⌊Y⌋₊ / Real.log Y)
      atTop (𝓝 2) := by
    have hmul := hmainRatio.mul tendsto_log_natFloor_div_log_one
    simpa only [mul_one] using hmul.congr' (by
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
      have hlogY : Real.log Y ≠ 0 := (Real.log_pos (by linarith)).ne'
      have hfloor2 : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
      have hlogN : Real.log (⌊Y⌋₊ : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hfloor2)).ne'
      field_simp [hlogY, hlogN])
  have hfloorRatio : Tendsto (fun Y : ℝ => ((⌊Y⌋₊ : ℕ) : ℝ) / Y)
      atTop (𝓝 1) := tendsto_nat_floor_div_atTop
  have hinvRatio : Tendsto (fun Y : ℝ => Y / ((⌊Y⌋₊ : ℕ) : ℝ))
      atTop (𝓝 1) := by
    have hinv := hfloorRatio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa only [inv_div, inv_one] using hinv
  have hdelta : Tendsto
      (fun Y : ℝ => Real.log (Y / (⌊Y⌋₊ : ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hinvRatio
  have hlinear : Tendsto
      (fun Y : ℝ => coprimeLogMoebius 1 (⌊Y⌋₊ : ℝ)) atTop (𝓝 1) :=
    tendsto_coprimeLogMoebius_one.comp hfloorCast
  have hpartial : Tendsto
      (fun Y : ℝ => RHTower.deningerHarmonicPartial ⌊Y⌋₊) atTop (𝓝 0) := by
    have hzero : Tendsto RHTower.deningerHarmonicPartial atTop (𝓝 0) := by
      rw [← RHTower.deningerHarmonicLimit_eq_zero]
      exact RHTower.deningerHarmonicPartial_tendsto
    exact hzero.comp hfloor
  have hcorrOne : Tendsto (fun Y : ℝ =>
      (2 * Real.log (Y / (⌊Y⌋₊ : ℝ)) *
        coprimeLogMoebius 1 (⌊Y⌋₊ : ℝ)) / Real.log Y) atTop (𝓝 0) := by
    have hnum := (hdelta.const_mul 2).mul hlinear
    simpa only [mul_one, zero_mul] using hnum.div_atTop hlog
  have hcorrTwo : Tendsto (fun Y : ℝ =>
      (Real.log (Y / (⌊Y⌋₊ : ℝ)) ^ (2 : ℕ) *
        RHTower.deningerHarmonicPartial ⌊Y⌋₊) / Real.log Y) atTop (𝓝 0) := by
    have hnum := hdelta.pow 2 |>.mul hpartial
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] using hnum.div_atTop hlog
  have hadd := hmain.add (hcorrOne.add hcorrTwo)
  rw [zero_add, add_zero] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
  rw [moebiusDoubleLogKernelReal_eq_floor Y (by linarith)]
  ring

/-- The real-cutoff quadratic Möbius kernel has a global linear-logarithmic envelope. -/
theorem exists_abs_moebiusDoubleLogKernelReal_le_const_mul_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 1 ≤ Y →
      |moebiusDoubleLogKernelReal Y| ≤ C * Real.log Y := by
  obtain ⟨C₀, hC₀⟩ := RHTower.deningerBounded_of_tendsto
    tendsto_moebiusDoubleLogKernel_div_log_two
  have hC₀nonneg : 0 ≤ C₀ := (abs_nonneg _).trans (hC₀ 0)
  obtain ⟨C₁, hC₁⟩ := RHTower.deningerBounded_of_tendsto
    RHTower.deningerHarmonicPartial_tendsto
  have hC₁nonneg : 0 ≤ C₁ :=
    (abs_nonneg (RHTower.deningerHarmonicPartial 0)).trans (hC₁ 0)
  let B : ℝ := 6 + |Real.eulerMascheroniConstant|
  have hB : 0 ≤ B := by
    dsimp [B]
    nlinarith [abs_nonneg Real.eulerMascheroniConstant]
  refine ⟨C₀ + 2 * B + C₁, by positivity, ?_⟩
  intro Y hY
  let N : ℕ := ⌊Y⌋₊
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff Y |>.mpr hY
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNle : (N : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have hYlt : Y < (N : ℝ) + 1 := Nat.lt_floor_add_one Y
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN1)
  let δ : ℝ := Real.log (Y / (N : ℝ))
  have hratioOne : (1 : ℝ) ≤ Y / (N : ℝ) := (one_le_div hNR).mpr hNle
  have hratioTwo : Y / (N : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hNR]
    have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith
  have hδnonneg : 0 ≤ δ := Real.log_nonneg hratioOne
  have hδone : δ ≤ 1 := by
    have hpos : 0 < Y / (N : ℝ) := by positivity
    dsimp [δ]
    nlinarith [Real.log_le_sub_one_of_pos hpos]
  have hδlog : δ ≤ Real.log Y := by
    have hlogeq : δ = Real.log Y - Real.log (N : ℝ) := by
      dsimp [δ]
      rw [Real.log_div (by positivity) hNR.ne']
    linarith
  have hδsq : δ ^ (2 : ℕ) ≤ Real.log Y := by nlinarith
  have hinteger : |moebiusDoubleLogKernel N| ≤ C₀ * Real.log (N : ℝ) := by
    rcases hN1.eq_or_lt with hN | hN2
    · rw [← hN]
      simp [moebiusDoubleLogKernel]
    · have hlogNpos : 0 < Real.log (N : ℝ) :=
        Real.log_pos (by exact_mod_cast hN2)
      have hfactor : moebiusDoubleLogKernel N =
          (moebiusDoubleLogKernel N / Real.log (N : ℝ)) * Real.log (N : ℝ) := by
        field_simp [hlogNpos.ne']
      rw [hfactor, abs_mul, abs_of_pos hlogNpos]
      exact mul_le_mul_of_nonneg_right (hC₀ N) hlogNpos.le
  have hintegerY : |moebiusDoubleLogKernel N| ≤ C₀ * Real.log Y := by
    refine hinteger.trans (mul_le_mul_of_nonneg_left ?_ hC₀nonneg)
    exact Real.log_le_log hNR hNle
  have hlinear : |2 * δ * coprimeLogMoebius 1 (N : ℝ)| ≤
      2 * B * Real.log Y := by
    have hT : |coprimeLogMoebius 1 (N : ℝ)| ≤ B :=
      abs_coprimeLogMoebius_one_le _
    rw [abs_mul, abs_mul, abs_of_nonneg hδnonneg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [abs_nonneg (coprimeLogMoebius 1 (N : ℝ))]
  have hquadratic : |δ ^ (2 : ℕ) * RHTower.deningerHarmonicPartial N| ≤
      C₁ * Real.log Y := by
    rw [abs_mul, abs_pow, abs_of_nonneg hδnonneg]
    have hprod := mul_le_mul hδsq (hC₁ N)
      (abs_nonneg (RHTower.deningerHarmonicPartial N)) hlogY
    nlinarith
  rw [moebiusDoubleLogKernelReal_eq_floor Y hY,
    show ⌊Y⌋₊ = N from rfl]
  calc
    |moebiusDoubleLogKernel N + 2 * δ * coprimeLogMoebius 1 (N : ℝ) +
        δ ^ (2 : ℕ) * RHTower.deningerHarmonicPartial N| ≤
        |moebiusDoubleLogKernel N| +
          |2 * δ * coprimeLogMoebius 1 (N : ℝ)| +
          |δ ^ (2 : ℕ) * RHTower.deningerHarmonicPartial N| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C₀ * Real.log Y + 2 * B * Real.log Y + C₁ * Real.log Y :=
      add_le_add (add_le_add hintegerY hlinear) hquadratic
    _ = (C₀ + 2 * B + C₁) * Real.log Y := by ring

end

end RHTower.Sieve
