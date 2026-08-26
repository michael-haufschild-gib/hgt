import GaloisForLFunctions.RHTower.Sieve.MoebiusLogPowerNormalization
import GaloisForLFunctions.RHTower.Sieve.MoebiusDoubleLogRealCutoff
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

open Finset ArithmeticFunction Filter Topology
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Möbius logarithmic-power kernel at a real cutoff. -/
def moebiusLogPowerKernelReal (p : ℕ) (Y : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊Y⌋₊,
    ((moebius d : ℤ) : ℝ) / (d : ℝ) * Real.log (Y / (d : ℝ)) ^ p

@[simp] theorem moebiusLogPowerKernelReal_natCast (p N : ℕ) :
    moebiusLogPowerKernelReal p (N : ℝ) = moebiusLogPowerKernel p N := by
  rw [moebiusLogPowerKernelReal, moebiusLogPowerKernel, Nat.floor_natCast]

/-- The degree-zero real-cutoff kernel is the harmonic Möbius partial sum at the natural floor. -/
@[simp] theorem moebiusLogPowerKernelReal_zero (Y : ℝ) :
    moebiusLogPowerKernelReal 0 Y =
      RHTower.deningerHarmonicPartial ⌊Y⌋₊ := by
  rw [moebiusLogPowerKernelReal, RHTower.deningerHarmonicPartial]
  simp only [pow_zero, mul_one]
  have hmem : 0 ∈ Finset.range (⌊Y⌋₊ + 1) := by simp
  have herase : (Finset.range (⌊Y⌋₊ + 1)).erase 0 =
      Finset.Icc 1 ⌊Y⌋₊ := by
    ext m
    simp
    omega
  rw [← herase, ← Finset.sum_erase_add _ _ hmem]
  simp

/-- The logarithmic displacement from a real cutoff to its natural floor beats every fixed
logarithmic power. -/
theorem tendsto_log_div_natFloor_mul_log_pow_zero (q : ℕ) :
    Tendsto (fun Y : ℝ =>
      Real.log (Y / (⌊Y⌋₊ : ℝ)) * Real.log Y ^ q) atTop (𝓝 0) := by
  have hdecay := Real.tendsto_pow_log_div_pow_atTop (1 : ℝ) (q : ℝ) (by norm_num)
  have hmajor : Tendsto (fun Y : ℝ => 2 * (Real.log Y ^ q / Y)) atTop (𝓝 0) := by
    have h := hdecay.const_mul 2
    simpa only [Real.rpow_natCast, Real.rpow_one, mul_zero] using h
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun Y => norm_nonneg _) ?_
    (by simpa only [norm_zero] using hmajor.norm)
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
  let N : ℕ := ⌊Y⌋₊
  have hYpos : 0 < Y := by linarith
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hY)
  have hNR : (0 : ℝ) < (N : ℝ) := by positivity
  have hNle : (N : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have hYlt : Y < (N : ℝ) + 1 := Nat.lt_floor_add_one Y
  have hratio : 0 < Y / (N : ℝ) := div_pos hYpos hNR
  have hdelta0 : 0 ≤ Real.log (Y / (N : ℝ)) :=
    Real.log_nonneg ((one_le_div hNR).mpr hNle)
  have hdelta_le_inv : Real.log (Y / (N : ℝ)) ≤ 1 / (N : ℝ) := by
    calc
      Real.log (Y / (N : ℝ)) ≤ Y / (N : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos hratio
      _ ≤ 1 / (N : ℝ) := by
        rw [div_sub_one hNR.ne', div_le_iff₀ hNR]
        have hone : (1 / (N : ℝ)) * (N : ℝ) = 1 := by field_simp [hNR.ne']
        rw [hone]
        linarith
  have hYleTwoN : Y ≤ 2 * (N : ℝ) := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    linarith
  have hinv_le : 1 / (N : ℝ) ≤ 2 / Y := by
    rw [div_le_div_iff₀ hNR hYpos]
    nlinarith
  have hdelta : Real.log (Y / (N : ℝ)) ≤ 2 / Y :=
    hdelta_le_inv.trans hinv_le
  have hlog0 : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hdelta0, abs_pow,
    abs_of_nonneg hlog0]
  calc
    Real.log (Y / (N : ℝ)) * Real.log Y ^ q ≤
        (2 / Y) * Real.log Y ^ q :=
      mul_le_mul_of_nonneg_right hdelta (pow_nonneg hlog0 q)
    _ = 2 * (Real.log Y ^ q / Y) := by ring
    _ ≤ ‖2 * (Real.log Y ^ q / Y)‖ := by
      rw [Real.norm_eq_abs]
      exact le_abs_self _

/-- Quantitative comparison of a real-cutoff logarithmic kernel with the kernel at its floor. -/
theorem abs_moebiusLogPowerKernelReal_sub_floor_le
    (p : ℕ) {Y : ℝ} (hY : 2 ≤ Y) :
    |moebiusLogPowerKernelReal p Y - moebiusLogPowerKernel p ⌊Y⌋₊| ≤
      (p : ℝ) * (1 + Real.log Y) * Real.log Y ^ (p - 1) *
        Real.log (Y / (⌊Y⌋₊ : ℝ)) := by
  classical
  let N : ℕ := ⌊Y⌋₊
  let δ : ℝ := Real.log (Y / (N : ℝ))
  have hYpos : 0 < Y := by linarith
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hY)
  have hNR : (0 : ℝ) < (N : ℝ) := by positivity
  have hNle : (N : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hδ : 0 ≤ δ := by
    exact Real.log_nonneg ((one_le_div hNR).mpr hNle)
  let P : ℝ := (p : ℝ) * Real.log Y ^ (p - 1) * δ
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hterm : ∀ d ∈ Finset.Icc 1 N,
      |((moebius d : ℤ) : ℝ) / (d : ℝ) *
          (Real.log (Y / (d : ℝ)) ^ p -
            Real.log ((N : ℝ) / (d : ℝ)) ^ p)| ≤
        P * (1 / (d : ℝ)) := by
    intro d hd
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
    have hdOne : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
    have hdY : (d : ℝ) ≤ Y := (by exact_mod_cast hdN : (d : ℝ) ≤ (N : ℝ)).trans hNle
    have hratioY : (1 : ℝ) ≤ Y / (d : ℝ) := (one_le_div hdR).mpr hdY
    have hratioN : (1 : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
      rw [one_le_div hdR]
      exact_mod_cast hdN
    have hratioYle : Y / (d : ℝ) ≤ Y := by
      rw [div_le_iff₀ hdR]
      nlinarith
    have hratioNle : (N : ℝ) / (d : ℝ) ≤ Y := by
      rw [div_le_iff₀ hdR]
      nlinarith
    have hx0 : 0 ≤ Real.log (Y / (d : ℝ)) := Real.log_nonneg hratioY
    have hy0 : 0 ≤ Real.log ((N : ℝ) / (d : ℝ)) := Real.log_nonneg hratioN
    have hx : |Real.log (Y / (d : ℝ))| ≤ Real.log Y := by
      rw [abs_of_nonneg hx0]
      exact Real.log_le_log (by positivity) hratioYle
    have hy : |Real.log ((N : ℝ) / (d : ℝ))| ≤ Real.log Y := by
      rw [abs_of_nonneg hy0]
      exact Real.log_le_log (by positivity) hratioNle
    have hlogdiff : Real.log (Y / (d : ℝ)) -
        Real.log ((N : ℝ) / (d : ℝ)) = δ := by
      dsimp [δ]
      rw [Real.log_div hYpos.ne' hdR.ne', Real.log_div hNR.ne' hdR.ne',
        Real.log_div hYpos.ne' hNR.ne']
      ring
    have hpow := GaloisForLFunctions.RHTower.Matveev.abs_pow_sub_pow_le hx hy p
    have hpow' : |Real.log (Y / (d : ℝ)) ^ p -
        Real.log ((N : ℝ) / (d : ℝ)) ^ p| ≤
        (p : ℝ) * Real.log Y ^ (p - 1) * δ := by
      rw [hlogdiff] at hpow
      simpa [abs_of_nonneg hδ] using hpow
    have hmu : |((moebius d : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    rw [abs_mul, abs_div, abs_of_pos hdR]
    calc
      (|((moebius d : ℤ) : ℝ)| / (d : ℝ)) *
          |Real.log (Y / (d : ℝ)) ^ p -
            Real.log ((N : ℝ) / (d : ℝ)) ^ p| ≤
        (1 / (d : ℝ)) * P := by
          exact mul_le_mul
            (div_le_div_of_nonneg_right hmu hdR.le)
            (by simpa [P] using hpow') (abs_nonneg _) (by positivity)
      _ = P * (1 / (d : ℝ)) := by ring
  rw [moebiusLogPowerKernelReal, moebiusLogPowerKernel,
    show ⌊Y⌋₊ = N from rfl, ← Finset.sum_sub_distrib]
  calc
    |∑ d ∈ Finset.Icc 1 N,
        (((moebius d : ℤ) : ℝ) / (d : ℝ) * Real.log (Y / (d : ℝ)) ^ p -
          ((moebius d : ℤ) : ℝ) / (d : ℝ) *
            Real.log ((N : ℝ) / (d : ℝ)) ^ p)| ≤
      ∑ d ∈ Finset.Icc 1 N,
        |((moebius d : ℤ) : ℝ) / (d : ℝ) *
          (Real.log (Y / (d : ℝ)) ^ p -
            Real.log ((N : ℝ) / (d : ℝ)) ^ p)| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
        apply Finset.sum_congr rfl
        intro d hd
        congr 1
        ring
    _ ≤ ∑ d ∈ Finset.Icc 1 N, P * (1 / (d : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = P * ∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ P * (1 + Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_Icc_one_div_le_one_add_log N) hP
    _ ≤ P * (1 + Real.log Y) := by
      exact mul_le_mul_of_nonneg_left
        (by linarith [Real.log_le_log hNR hNle]) hP
    _ = (p : ℝ) * (1 + Real.log Y) * Real.log Y ^ (p - 1) *
        Real.log (Y / (⌊Y⌋₊ : ℝ)) := by
      dsimp [P, δ]
      rw [show N = ⌊Y⌋₊ from rfl]
      ring

/-- Real cutoffs preserve the classical leading coefficient of every positive logarithmic
Möbius kernel. -/
theorem tendsto_moebiusLogPowerKernelReal_div_log_pow (p : ℕ) :
    Tendsto (fun Y : ℝ =>
      moebiusLogPowerKernelReal (p + 1) Y / Real.log Y ^ p)
      atTop (𝓝 ((p + 1 : ℕ) : ℝ)) := by
  have hfloor : Tendsto (fun Y : ℝ => ⌊Y⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop
  have hinteger : Tendsto (fun Y : ℝ =>
      moebiusLogPowerKernel (p + 1) ⌊Y⌋₊ /
        Real.log (⌊Y⌋₊ : ℝ) ^ p) atTop (𝓝 ((p + 1 : ℕ) : ℝ)) :=
    (tendsto_moebiusLogPowerKernel_div_log_pow p).comp hfloor
  have hscale : Tendsto (fun Y : ℝ =>
      (Real.log (⌊Y⌋₊ : ℝ) / Real.log Y) ^ p) atTop (𝓝 1) := by
    simpa only [one_pow] using tendsto_log_natFloor_div_log_one.pow p
  have hmain : Tendsto (fun Y : ℝ =>
      moebiusLogPowerKernel (p + 1) ⌊Y⌋₊ / Real.log Y ^ p)
      atTop (𝓝 ((p + 1 : ℕ) : ℝ)) := by
    have hprod := hinteger.mul hscale
    simpa only [mul_one] using hprod.congr' (by
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
      have hlogY : Real.log Y ≠ 0 := (Real.log_pos (by linarith)).ne'
      have hfloor2 : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
      have hlogN : Real.log (⌊Y⌋₊ : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hfloor2)).ne'
      rw [div_pow]
      field_simp [hlogY, hlogN])
  have hgapZero := tendsto_log_div_natFloor_mul_log_pow_zero 0
  have hgapOne := tendsto_log_div_natFloor_mul_log_pow_zero 1
  have hgap : Tendsto (fun Y : ℝ =>
      ((p + 1 : ℕ) : ℝ) * (1 + Real.log Y) *
        Real.log (Y / (⌊Y⌋₊ : ℝ))) atTop (𝓝 0) := by
    have hadd : Tendsto (fun Y : ℝ =>
        Real.log (Y / (⌊Y⌋₊ : ℝ)) +
          Real.log (Y / (⌊Y⌋₊ : ℝ)) * Real.log Y) atTop (𝓝 0) := by
      have hzero : Tendsto (fun Y : ℝ =>
          Real.log (Y / (⌊Y⌋₊ : ℝ))) atTop (𝓝 0) := by
        simpa only [pow_zero, mul_one] using hgapZero
      have hone : Tendsto (fun Y : ℝ =>
          Real.log (Y / (⌊Y⌋₊ : ℝ)) * Real.log Y) atTop (𝓝 0) := by
        simpa only [pow_one] using hgapOne
      simpa only [add_zero] using hzero.add hone
    have hconst := hadd.const_mul (((p + 1 : ℕ) : ℝ))
    simpa only [mul_zero] using hconst.congr' (Eventually.of_forall fun Y => by ring)
  have herr : Tendsto (fun Y : ℝ =>
      (moebiusLogPowerKernelReal (p + 1) Y -
        moebiusLogPowerKernel (p + 1) ⌊Y⌋₊) / Real.log Y ^ p)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun Y => norm_nonneg _) ?_
      (by simpa only [norm_zero] using hgap.norm)
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
    have hlog : 0 < Real.log Y := Real.log_pos (by linarith)
    have hbound := abs_moebiusLogPowerKernelReal_sub_floor_le (p + 1) hY
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hlog p)]
    calc
      |moebiusLogPowerKernelReal (p + 1) Y -
          moebiusLogPowerKernel (p + 1) ⌊Y⌋₊| / Real.log Y ^ p ≤
        ((((p + 1 : ℕ) : ℝ) * (1 + Real.log Y) *
          Real.log Y ^ (p + 1 - 1) *
            Real.log (Y / (⌊Y⌋₊ : ℝ))) / Real.log Y ^ p) :=
          div_le_div_of_nonneg_right hbound (pow_pos hlog p).le
      _ = ((p + 1 : ℕ) : ℝ) * (1 + Real.log Y) *
          Real.log (Y / (⌊Y⌋₊ : ℝ)) := by
        rw [show p + 1 - 1 = p by omega]
        field_simp [hlog.ne']
      _ ≤ ‖((p + 1 : ℕ) : ℝ) * (1 + Real.log Y) *
          Real.log (Y / (⌊Y⌋₊ : ℝ))‖ := by
        rw [Real.norm_eq_abs]
        exact le_abs_self _
  have hadd := hmain.add herr
  rw [add_zero] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
  have hlog : Real.log Y ≠ 0 := (Real.log_pos (by linarith)).ne'
  field_simp [hlog]
  ring

/-- Global elementary envelope for every real-cutoff logarithmic Möbius kernel. -/
theorem abs_moebiusLogPowerKernelReal_le_one_add_log_mul_pow
    (p : ℕ) {Y : ℝ} (hY : 1 ≤ Y) :
    |moebiusLogPowerKernelReal p Y| ≤
      (1 + Real.log Y) * Real.log Y ^ p := by
  classical
  let N : ℕ := ⌊Y⌋₊
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff Y |>.mpr hY
  have hNR : (0 : ℝ) < (N : ℝ) := by positivity
  have hNle : (N : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hterm : ∀ d ∈ Finset.Icc 1 N,
      |((moebius d : ℤ) : ℝ) / (d : ℝ) *
          Real.log (Y / (d : ℝ)) ^ p| ≤
        Real.log Y ^ p * (1 / (d : ℝ)) := by
    intro d hd
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
    have hdOne : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
    have hdY : (d : ℝ) ≤ Y := (by exact_mod_cast hdN : (d : ℝ) ≤ (N : ℝ)).trans hNle
    have hratioOne : (1 : ℝ) ≤ Y / (d : ℝ) := (one_le_div hdR).mpr hdY
    have hratioLe : Y / (d : ℝ) ≤ Y := by
      rw [div_le_iff₀ hdR]
      nlinarith
    have hlog0 : 0 ≤ Real.log (Y / (d : ℝ)) := Real.log_nonneg hratioOne
    have hlogLe : Real.log (Y / (d : ℝ)) ≤ Real.log Y :=
      Real.log_le_log (by positivity) hratioLe
    have hpowLe : Real.log (Y / (d : ℝ)) ^ p ≤ Real.log Y ^ p :=
      pow_le_pow_left₀ hlog0 hlogLe p
    have hmu : |((moebius d : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    rw [abs_mul, abs_div, abs_of_pos hdR, abs_pow, abs_of_nonneg hlog0]
    calc
      (|((moebius d : ℤ) : ℝ)| / (d : ℝ)) *
          Real.log (Y / (d : ℝ)) ^ p ≤
        (1 / (d : ℝ)) * Real.log Y ^ p :=
          mul_le_mul (div_le_div_of_nonneg_right hmu hdR.le) hpowLe
            (pow_nonneg hlog0 p) (by positivity)
      _ = Real.log Y ^ p * (1 / (d : ℝ)) := by ring
  rw [moebiusLogPowerKernelReal, show ⌊Y⌋₊ = N from rfl]
  calc
    |∑ d ∈ Finset.Icc 1 N,
        ((moebius d : ℤ) : ℝ) / (d : ℝ) *
          Real.log (Y / (d : ℝ)) ^ p| ≤
      ∑ d ∈ Finset.Icc 1 N,
        |((moebius d : ℤ) : ℝ) / (d : ℝ) *
          Real.log (Y / (d : ℝ)) ^ p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N, Real.log Y ^ p * (1 / (d : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = Real.log Y ^ p * ∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ Real.log Y ^ p * (1 + Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_Icc_one_div_le_one_add_log N)
        (pow_nonneg hlogY p)
    _ ≤ Real.log Y ^ p * (1 + Real.log Y) := by
      exact mul_le_mul_of_nonneg_left
        (by linarith [Real.log_le_log hNR hNle]) (pow_nonneg hlogY p)
    _ = (1 + Real.log Y) * Real.log Y ^ p := by ring

end


end RHTower.Sieve
