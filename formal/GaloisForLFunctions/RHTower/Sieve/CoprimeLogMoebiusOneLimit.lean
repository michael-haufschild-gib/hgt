import GaloisForLFunctions.RHTower.Sieve.MoebiusLogarithmicNormalization
import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusRecursion

/-!
# The modulus-one coprime logarithmic Möbius limit
-/

open Finset ArithmeticFunction Filter Topology
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- Exact passage from a real cutoff to its integer floor. -/
theorem coprimeLogMoebius_one_eq_floor (Y : ℝ) (hY : 1 ≤ Y) :
    coprimeLogMoebius 1 Y =
      (∑ d ∈ Finset.Icc 1 ⌊Y⌋₊,
        ((moebius d : ℤ) : ℝ) / (d : ℝ) *
          Real.log ((⌊Y⌋₊ : ℝ) / (d : ℝ))) +
      Real.log (Y / (⌊Y⌋₊ : ℝ)) * RHTower.deningerHarmonicPartial ⌊Y⌋₊ := by
  classical
  let N : ℕ := ⌊Y⌋₊
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff Y |>.mpr hY
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hfil : (Finset.Icc 1 N).filter (fun j => Nat.Coprime 1 j) = Finset.Icc 1 N := by
    refine Finset.filter_true_of_mem fun j _ => Nat.coprime_one_left j
  have hpartial : RHTower.deningerHarmonicPartial N =
      ∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ) := by
    rw [RHTower.deningerHarmonicPartial, Finset.sum_range_succ']
    simp
    convert RHTower.sum_range_succ_eq_sum_Icc
      (fun d : ℕ => ((moebius d : ℤ) : ℝ) / (d : ℝ)) N using 1 <;>
        push_cast <;> ring
  rw [coprimeLogMoebius, show ⌊Y⌋₊ = N from rfl, hfil, hpartial,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hlog : Real.log (Y / (d : ℝ)) =
      Real.log ((N : ℝ) / (d : ℝ)) + Real.log (Y / (N : ℝ)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [hlog]
  ring

/-- At modulus one, the real-cutoff logarithmic Möbius kernel tends to one. -/
theorem tendsto_coprimeLogMoebius_one :
    Tendsto (coprimeLogMoebius 1) atTop (𝓝 1) := by
  let main : ℝ → ℝ := fun Y =>
    ∑ d ∈ Finset.Icc 1 ⌊Y⌋₊,
      ((moebius d : ℤ) : ℝ) / (d : ℝ) *
        Real.log ((⌊Y⌋₊ : ℝ) / (d : ℝ))
  let corr : ℝ → ℝ := fun Y =>
    Real.log (Y / (⌊Y⌋₊ : ℝ)) * RHTower.deningerHarmonicPartial ⌊Y⌋₊
  have hfloor : Tendsto (fun Y : ℝ => ⌊Y⌋₊) atTop atTop := tendsto_nat_floor_atTop
  have hmain : Tendsto main atTop (𝓝 1) := by
    exact tendsto_sum_moebius_log_div_one.comp hfloor
  have hpartial : Tendsto
      (fun Y : ℝ => RHTower.deningerHarmonicPartial ⌊Y⌋₊) atTop (𝓝 0) := by
    have hzero : Tendsto RHTower.deningerHarmonicPartial atTop (𝓝 0) := by
      rw [← RHTower.deningerHarmonicLimit_eq_zero]
      exact RHTower.deningerHarmonicPartial_tendsto
    exact hzero.comp hfloor
  have hcorr : Tendsto corr atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun Y => norm_nonneg (corr Y)) ?_
      (by simpa using hpartial.norm)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    let N : ℕ := ⌊Y⌋₊
    have hN1 : 1 ≤ N := Nat.one_le_floor_iff Y |>.mpr hY
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hNle : (N : ℝ) ≤ Y := Nat.floor_le (by linarith)
    have hYlt : Y < (N : ℝ) + 1 := Nat.lt_floor_add_one Y
    have hlogle : |Real.log (Y / (N : ℝ))| ≤ 1 := by
      have h1 : (1 : ℝ) ≤ Y / (N : ℝ) := (one_le_div hNR).mpr hNle
      have hpos : (0 : ℝ) < Y / (N : ℝ) := by positivity
      have hupper : Real.log (Y / (N : ℝ)) ≤ 1 := by
        have h2 : Y / (N : ℝ) ≤ 2 := by
          rw [div_le_iff₀ hNR]
          have hNR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
          linarith
        have := Real.log_le_sub_one_of_pos hpos
        linarith
      rw [abs_of_nonneg (Real.log_nonneg h1)]
      exact hupper
    change ‖Real.log (Y / (N : ℝ)) * RHTower.deningerHarmonicPartial N‖ ≤
      ‖RHTower.deningerHarmonicPartial N‖
    rw [norm_mul, Real.norm_eq_abs]
    nlinarith [norm_nonneg (RHTower.deningerHarmonicPartial N)]
  have hadd := hmain.add hcorr
  rw [add_zero] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
  exact (coprimeLogMoebius_one_eq_floor Y hY).symm

end RHTower.Sieve
