import GaloisForLFunctions.RHTower.Sieve.ChebyshevMainTermLimit
import GaloisForLFunctions.RHTower.Sieve.ChebyshevSmoothVsSharp

/-!
# The prime number theorem in Chebyshev form

Combining the contour estimate with the two limits of the main term gives

    ∑ₙ Λ(n)w(n) / N → 1,

and the smoothing costs `(H+1)·log(N+H) = o(N)`, so the sharp sum obeys the same law:

    ψ(N)/N → 1.

Every step is unconditional.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset ArithmeticFunction Filter Topology RHTower
open GaloisForLFunctions.HTGeometry

/-- The relative width in closed form. -/
theorem chebWidth_div_eq {x : ℝ} (hx : 0 < x) :
    chebWidth x / x = Real.exp (-((Real.log x) ^ ((1 : ℝ) / 20))) := by
  rw [chebWidth, Real.exp_neg]
  field_simp

/-- The twentieth power of the width's exponent. -/
theorem logRoot20_pow {L : ℝ} (hL : 0 ≤ L) : (L ^ ((1 : ℝ) / 20)) ^ 20 = L := by
  rw [← Real.rpow_natCast (L ^ ((1 : ℝ) / 20)) 20, ← Real.rpow_mul hL]
  norm_num

/-- The relative width beats the logarithm. -/
theorem tendsto_width_mul_log :
    Tendsto (fun x : ℝ => chebWidth x / x * Real.log x) atTop (𝓝 0) := by
  have hroot : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 20)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hbase := tendsto_pow_mul_exp_neg_mul 20 (κ := 1) (by norm_num)
  have hcomp := hbase.comp hroot
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hL : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx.le
  simp only [Function.comp_apply]
  rw [logRoot20_pow hL, chebWidth_div_eq hx0, one_mul]
  ring

/-- **The smoothing error is `o(N)`.** -/
theorem tendsto_window_mass_div :
    Tendsto (fun x : ℝ => (chebWidth x + 1) * Real.log (x + chebWidth x) / x) atTop (𝓝 0) := by
  have hlogdiv : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hconstdiv : Tendsto (fun x : ℝ => Real.log 2 / x) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.const_mul (Real.log 2))
    simpa [div_eq_mul_inv] using this
  have hwidth := tendsto_width_mul_log
  have hwidth0 : Tendsto (fun x : ℝ => chebWidth x / x * Real.log 2) atTop (𝓝 0) := by
    have := tendsto_chebWidth_div.mul_const (Real.log 2)
    simpa using this
  have hmaj : Tendsto (fun x : ℝ => chebWidth x / x * Real.log 2 + chebWidth x / x * Real.log x
      + (Real.log 2 / x + Real.log x / x)) atTop (𝓝 0) := by
    have := ((hwidth0.add hwidth).add (hconstdiv.add hlogdiv))
    simpa using this
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hH0 : (0 : ℝ) < chebWidth x := chebWidth_pos hx0
    have hlog : (0 : ℝ) ≤ Real.log (x + chebWidth x) :=
      Real.log_nonneg (by linarith)
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hH0 : (0 : ℝ) < chebWidth x := chebWidth_pos hx0
    have hHle : chebWidth x ≤ x := chebWidth_le (Real.log_nonneg hx) hx0
    have hlog2 : Real.log (x + chebWidth x) ≤ Real.log 2 + Real.log x := by
      have h := Real.log_le_log (by linarith) (by linarith : x + chebWidth x ≤ 2 * x)
      rwa [Real.log_mul (by norm_num) (ne_of_gt hx0)] at h
    have hstep : (chebWidth x + 1) * Real.log (x + chebWidth x)
        ≤ (chebWidth x + 1) * (Real.log 2 + Real.log x) :=
      mul_le_mul_of_nonneg_left hlog2 (by linarith)
    rw [div_le_iff₀ hx0]
    have hrw : (chebWidth x / x * Real.log 2 + chebWidth x / x * Real.log x
        + (Real.log 2 / x + Real.log x / x)) * x
        = (chebWidth x + 1) * (Real.log 2 + Real.log x) := by
      field_simp
    rw [hrw]
    exact hstep

/-- **The smoothed Chebyshev sum, relative to the cutoff, tends to one.** -/
theorem tendsto_tsum_vonMangoldt_smoothWeight_div :
    Tendsto (fun x : ℝ => (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
        * ((smoothWeight x (chebWidth x) (n : ℝ) : ℝ) : ℂ)) / (x : ℂ)) atTop (𝓝 1) := by
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    have := Real.pi_pos
    intro h
    linarith
  have herr : Tendsto (fun x : ℝ =>
      ((2 * Real.pi : ℝ) • (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
            * ((smoothWeight x (chebWidth x) (n : ℝ) : ℝ) : ℂ))
          - mellin (fun y : ℝ => ((smoothWeight x (chebWidth x) y : ℝ) : ℂ)) 1
            * (((2 * Real.arctan (chebHeight x / (zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10)))
                - 2 * Real.arctan (chebHeight x
                    / (-(zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10)))) : ℝ)) : ℂ))
        / (x : ℂ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_norm_tsum_vonMangoldt_sub_main_div.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  have hW : Tendsto (fun x : ℝ =>
      mellin (fun y : ℝ => ((smoothWeight x (chebWidth x) y : ℝ) : ℂ)) 1 / (x : ℂ))
      atTop (𝓝 1) := by
    have hre := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp tendsto_mass_div
    simp only [Complex.ofReal_one] at hre
    refine hre.congr fun x => ?_
    simp only [Function.comp_apply]
    rw [Complex.ofReal_div, mellin_smoothWeight_one_eq_ofReal]
  have hB : Tendsto (fun x : ℝ =>
      (((2 * Real.arctan (chebHeight x / (zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10)))
          - 2 * Real.arctan (chebHeight x
              / (-(zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10)))) : ℝ)) : ℂ))
      atTop (𝓝 ((2 * Real.pi : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp tendsto_bracket_at_choice
  have hprod := hW.mul hB
  rw [one_mul] at hprod
  have hkey := herr.add hprod
  rw [zero_add] at hkey
  have hkey' : Tendsto (fun x : ℝ => ((2 * Real.pi : ℝ) : ℂ)
      * ((∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
          * ((smoothWeight x (chebWidth x) (n : ℝ) : ℝ) : ℂ)) / (x : ℂ)))
      atTop (𝓝 ((2 * Real.pi : ℝ) : ℂ)) := by
    refine hkey.congr fun x => ?_
    rw [Complex.real_smul]
    ring
  have hfinal := hkey'.const_mul (((2 * Real.pi : ℝ) : ℂ))⁻¹
  rw [inv_mul_cancel₀ hpi] at hfinal
  refine hfinal.congr fun x => ?_
  rw [← mul_assoc, inv_mul_cancel₀ hpi, one_mul]

/-- The smoothed and sharp sums agree to `o(N)`. -/
theorem tendsto_smooth_sub_sharp_div :
    Tendsto (fun x : ℝ => ((∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
          * ((smoothWeight x (chebWidth x) (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.range (⌊x⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ)) / (x : ℂ))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' ?_ ?_ tendsto_window_mass_div
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _
    exact norm_nonneg _
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hH0 : (0 : ℝ) < chebWidth x := chebWidth_pos hx0
    have hNH1 : (1 : ℝ) ≤ x + chebWidth x := by linarith
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    have hb := norm_tsum_vonMangoldt_smoothWeight_sub_sum_le hx0 hH0 hNH1
    gcongr

/-- **The prime number theorem in Chebyshev form**, as a complex limit. -/
theorem tendsto_sum_vonMangoldt_div_complex :
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.range (⌊x⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ)) / (x : ℂ))
      atTop (𝓝 1) := by
  have h := tendsto_tsum_vonMangoldt_smoothWeight_div.sub tendsto_smooth_sub_sharp_div
  rw [sub_zero] at h
  refine h.congr fun x => ?_
  ring

/-- **The prime number theorem in Chebyshev form**: `ψ(x)/x → 1`. -/
theorem tendsto_sum_vonMangoldt_div :
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.range (⌊x⌋₊ + 1), (vonMangoldt n : ℝ)) / x)
      atTop (𝓝 1) := by
  have h := (Complex.continuous_re.tendsto (1 : ℂ)).comp tendsto_sum_vonMangoldt_div_complex
  simp only [Complex.one_re] at h
  refine h.congr fun x => ?_
  simp only [Function.comp_apply]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_div, Complex.ofReal_re]

end RHTower.Sieve
