import GaloisForLFunctions.RHTower.Sieve.HarmonicLogWindowLowerMoments
import GaloisForLFunctions.RHTower.Sieve.SelbergPrincipalHarmonicModel

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

theorem harmonicLogWindowMoment_zero_zero_eq_harmonic (N : ℕ) :
    harmonicLogWindowMoment 0 0 N = (harmonic N : ℝ) := by
  have hset : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext d
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [harmonicLogWindowMoment, hset]
  simp only [pow_zero]
  exact sum_Icc_one_div_eq_harmonic N

/-- A fixed natural dilation and successor do not change the logarithmic scale. -/
theorem tendsto_log_natDiv_add_one_div_log_one {c : ℕ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => Real.log (N / c + 1 : ℕ) / Real.log N)
      atTop (𝓝 1) := by
  have hratio := RHTower.tendsto_harmonic_natDiv_div_log (d := c) hc
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop := hlog
  have herr : Tendsto (fun N : ℕ =>
      ((harmonic (N / c) : ℝ) - Real.log (N / c + 1 : ℕ)) / Real.log N)
      atTop (𝓝 0) := by
    have hmaj : Tendsto (fun N : ℕ => (20 : ℝ) / Real.log N) atTop (𝓝 0) :=
      hscale.const_div_atTop 20
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hlog]
    apply div_le_div_of_nonneg_right _ hlog.le
    rw [← harmonicLogWindowMoment_zero_zero_eq_harmonic]
    exact abs_harmonicLogWindowMoment_zero_zero_sub_log_le (N / c)
  have hsub := hratio.sub herr
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  field_simp [hlog]
  ring

/-- First harmonic logarithmic moment at a fixed dilation has coefficient `1/2`. -/
theorem tendsto_harmonicLogWindowMoment_one_natDiv_div_log_sq_half
    {c : ℕ} (hc : 0 < c) :
    Tendsto (fun N : ℕ =>
      harmonicLogWindowMoment 1 0 (N / c) / Real.log N ^ 2)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (n := 2) (by norm_num)).comp hlog
  have herr : Tendsto (fun N : ℕ =>
      (harmonicLogWindowMoment 1 0 (N / c) -
        Real.log (N / c + 1 : ℕ) ^ 2 / 2) / Real.log N ^ 2)
      atTop (𝓝 0) := by
    have hmaj : Tendsto (fun N : ℕ => (100 : ℝ) / Real.log N ^ 2)
        atTop (𝓝 0) := hscale.const_div_atTop 100
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos hlog)]
    exact div_le_div_of_nonneg_right
      (abs_harmonicLogWindowMoment_one_zero_sub_logSquare_le (N / c))
      (sq_nonneg _)
  have hratio := tendsto_log_natDiv_add_one_div_log_one hc
  have hmain : Tendsto (fun N : ℕ =>
      (Real.log (N / c + 1 : ℕ) ^ 2 / 2) / Real.log N ^ 2)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    have h := (hratio.pow 2).const_mul (1 / 2 : ℝ)
    simpa only [one_pow, mul_one] using h.congr' (by
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hlog : Real.log (N : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hN)).ne'
      field_simp [hlog])
  have hadd := herr.add hmain
  rw [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  field_simp [hlog]
  ring

/-- Second harmonic logarithmic moment at a fixed dilation has coefficient `1/3`. -/
theorem tendsto_harmonicLogWindowMoment_two_natDiv_div_log_cube_third
    {c : ℕ} (hc : 0 < c) :
    Tendsto (fun N : ℕ =>
      harmonicLogWindowMoment 2 0 (N / c) / Real.log N ^ 3)
      atTop (𝓝 (1 / 3 : ℝ)) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (n := 3) (by norm_num)).comp hlog
  have herr : Tendsto (fun N : ℕ =>
      (harmonicLogWindowMoment 2 0 (N / c) -
        Real.log (N / c + 1 : ℕ) ^ 3 / 3) / Real.log N ^ 3)
      atTop (𝓝 0) := by
    have hmaj : Tendsto (fun N : ℕ => (1000 : ℝ) / Real.log N ^ 3)
        atTop (𝓝 0) := hscale.const_div_atTop 1000
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hlog 3)]
    exact div_le_div_of_nonneg_right
      (abs_harmonicLogWindowMoment_two_zero_sub_cubic_le (N / c))
      (pow_nonneg hlog.le 3)
  have hratio := tendsto_log_natDiv_add_one_div_log_one hc
  have hmain : Tendsto (fun N : ℕ =>
      (Real.log (N / c + 1 : ℕ) ^ 3 / 3) / Real.log N ^ 3)
      atTop (𝓝 (1 / 3 : ℝ)) := by
    have h := (hratio.pow 3).const_mul (1 / 3 : ℝ)
    simpa only [one_pow, mul_one] using h.congr' (by
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hlog : Real.log (N : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hN)).ne'
      field_simp [hlog])
  have hadd := herr.add hmain
  rw [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  field_simp [hlog]
  ring

end

end RHTower.Sieve
