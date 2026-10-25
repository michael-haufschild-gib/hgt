import GaloisForLFunctions.BezoutValuationIncidence.UniformCancellationInTheUndampedVaughanConvolution
import GaloisForLFunctions.RHTower.MobiusTwoJetLinearDensity
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# Uniform logarithmic cancellation in the Vaughan convolution

A quarter-power split turns the finite Vaughan identity into every logarithmic
summatory saving, uniformly in both truncation cutoffs. The constants come from
the actual Mertens and harmonic Möbius logarithmic estimates.
-/

open Finset Filter RHTower
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false


private theorem eventually_log_pow_le_sqrt (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ^ q ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
  have hlim : Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ q /
      (n : ℝ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast] using
      ((isLittleO_log_rpow_rpow_atTop (q : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop)
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  exact ((div_lt_one (Real.rpow_pos_of_pos hn0 _)).mp hn).le

private theorem quarter_cutoff_head_le {n : ℕ} (hn : 1 ≤ n) :
    ((⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊ : ℕ) : ℝ) ^ 2 +
      (⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊ : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD := Nat.floor_le (Real.rpow_nonneg hn0.le (1 / 4 : ℝ))
  have hsq : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
  have hDsq := pow_le_pow_left₀ (Nat.cast_nonneg ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊) hD 2
  rw [hsq] at hDsq
  have hquarter : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  linarith only [hDsq, hD, hquarter]

/-- The summatory undamped Vaughan convolution has every logarithmic saving, uniformly in both cutoffs. -/
theorem exists_uniform_pmUndampedVaughanConvolutionPrefix_log_rate (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ U V : ℕ,
      |pmUndampedVaughanConvolutionPrefix U V n -
        (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V| ≤
          C * (n : ℝ) / Real.log (n : ℝ) ^ q := by
  obtain ⟨B, C, hB, hC, D₀, hD₀, hbound⟩ :=
    exists_uniform_pmUndampedVaughanConvolutionPrefix_log_bound (q + 2) (by omega)
  let D : ℕ → ℕ := fun n => ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊
  have hDlim : Tendsto D atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop)
  have hloglim : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨2 + 8 ^ (q + 2) * (11 * B + C), by positivity, ?_⟩
  filter_upwards [hDlim.eventually_ge_atTop D₀, hloglim.eventually_ge_atTop 1,
    hloglim.eventually_ge_atTop (8 * Real.log 2), eventually_log_pow_le_sqrt q,
    eventually_ge_atTop 2] with n hD hlog1 hlog8 hhead hn2 U V
  have hn : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hlog1
  have hDn : D n ≤ n := by
    apply Nat.floor_le_of_le
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1
      (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hD2 : 2 ≤ D n := hD₀.trans hD
  have hlogD : Real.log (n : ℝ) / 8 ≤ Real.log (D n : ℝ) := by
    have h := CubicGamma.log_floor_rpow_ge hn1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    change 1 / 4 * Real.log (n : ℝ) - Real.log 2 ≤ Real.log (D n : ℝ) at h
    linarith only [h, hlog8]
  have hden : (Real.log (n : ℝ) / 8) ^ (q + 2) ≤ Real.log (D n : ℝ) ^ (q + 2) :=
    pow_le_pow_left₀ (by positivity) hlogD _
  have hld : 0 < Real.log (D n : ℝ) := (by positivity : 0 < Real.log (n : ℝ) / 8).trans_le hlogD
  have hden0 : 0 < (Real.log (n : ℝ) / 8) ^ (q + 2) := by positivity
  have hH : (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) ^ 2 ≤ 4 * Real.log (n : ℝ) ^ 2 := by
    have hsum := Sieve.sum_Icc_one_div_le_one_add_log n
    have hlin : (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
      linarith only [hsum, hlog1]
    have hnonneg : 0 ≤ ∑ k ∈ Icc 1 n, 1 / (k : ℝ) := sum_nonneg fun k _ => by positivity
    simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using pow_le_pow_left₀ hnonneg hlin 2
  have hlog2 : 1 ≤ Real.log (n : ℝ) ^ 2 := one_le_pow₀ hlog1
  have hnum : 3 * B * n + 2 * B * n * (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) ^ 2 + C * n ≤
      (11 * B + C) * n * Real.log (n : ℝ) ^ 2 := by
    have hfirst := mul_le_mul_of_nonneg_left hlog2 (by positivity : 0 ≤ 3 * B * n)
    have hmiddle := mul_le_mul_of_nonneg_left hH (by positivity : 0 ≤ 2 * B * n)
    have hlast := mul_le_mul_of_nonneg_left hlog2 (by positivity : 0 ≤ C * n)
    nlinarith only [hfirst, hmiddle, hlast]
  have htail : (3 * B * n + 2 * B * n * (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) ^ 2 + C * n) /
      Real.log (D n : ℝ) ^ (q + 2) ≤
        (8 ^ (q + 2) * (11 * B + C)) * n / Real.log (n : ℝ) ^ q := by
    calc
      _ ≤ ((11 * B + C) * n * Real.log (n : ℝ) ^ 2) /
          (Real.log (n : ℝ) / 8) ^ (q + 2) :=
        (div_le_div_of_nonneg_right hnum (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) hden0 hden)
      _ = _ := by
        rw [div_pow, pow_add]
        field_simp [hl.ne']
  have hhead' : (D n : ℝ) ^ 2 + D n ≤ 2 * n / Real.log (n : ℝ) ^ q := by
    refine (quarter_cutoff_head_le hn).trans ?_
    apply (le_div_iff₀ (pow_pos hl q)).mpr
    have hsquare : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = n := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hn0.le]
    have h := mul_le_mul_of_nonneg_left hhead (Real.rpow_nonneg hn0.le (1 / 2 : ℝ))
    rw [← pow_two, hsquare] at h
    linarith only [h]
  exact (hbound (D n) n hD hDn U V).trans
    ((add_le_add hhead' htail).trans_eq (by ring))

end GaloisForLFunctions.BezoutValuationIncidence
