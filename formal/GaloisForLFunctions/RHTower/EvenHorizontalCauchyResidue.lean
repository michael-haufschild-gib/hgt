import GaloisForLFunctions.RHTower.RectangleCauchyFormulaOn
import GaloisForLFunctions.HTGeometry.VerticalContourShift
import GaloisForLFunctions.RHTower.StripHorizontalShift
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Half-residue formula for even functions on a horizontal line below the real axis

Let `F` be holomorphic on the strip `|Im z| < a`, even (`F(-z) = F(z)`), and exponentially
decaying on the closed substrip `|Im z| ≤ d` for some `0 < d < a`. This module shows that the
integral of `F(z)/z` along the horizontal line `Im z = -d` equals `π i F(0)`. The rectangle
Cauchy formula gives `2π i F(0)` for the difference of the lines `Im z = -d` and `Im z = d`,
and evenness of `F` makes the two line integrals negatives of each other.

## Main results

- `integral_even_horizontal_cauchy_of_decay`: `∫_ℝ F(x - id)/(x - id) dx = π i F(0)`.

## Hypotheses

Unconditional given its explicit premises: `0 < d < a`, `F` holomorphic on `|Im z| < a`, `F`
even, and the decay bound `|F(z)| ≤ C e^(-r |Re z|)` on `|Im z| ≤ d` with `C ≥ 0`, `r > 0`.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- For `F` holomorphic on `|Im z| < a`, even, and bounded by `C e^(-r |Re z|)` on `|Im z| ≤ d` with
`0 < d < a`, the integral of `F(z)/z` over the line `Im z = -d` equals `π i F(0)`. -/
theorem integral_even_horizontal_cauchy_of_decay
    {F : ℂ → ℂ} {a d C r : ℝ}
    (hd : 0 < d) (hda : d < a) (hC : 0 ≤ C) (hr : 0 < r)
    (hg : AnalyticOnNhd ℂ F {z : ℂ | |z.im| < a})
    (heven : ∀ z : ℂ, F (-z) = F z)
    (hbound : ∀ z : ℂ, |z.im| ≤ d →
      ‖F z‖ ≤ C * Real.exp (-(r * |z.re|))) :
    (∫ x : ℝ, F ((x : ℂ) - d * I) * (((x : ℂ) - d * I)⁻¹)) =
      Real.pi * I * F 0 := by
  let L : ℝ → ℂ := fun x => F ((x : ℂ) - d * I) * (((x : ℂ) - d * I)⁻¹)
  let U : ℝ → ℂ := fun x => F ((x : ℂ) + d * I) * (((x : ℂ) + d * I)⁻¹)
  have hinv_lower (x : ℝ) : ‖(((x : ℂ) - d * I)⁻¹)‖ ≤ d⁻¹ := by
    rw [norm_inv]
    have him : (((x : ℂ) - d * I)).im = -d := by simp
    have hge : d ≤ ‖((x : ℂ) - d * I)‖ := by
      have h := Complex.abs_im_le_norm ((x : ℂ) - d * I)
      rw [him, abs_neg, abs_of_pos hd] at h
      exact h
    exact inv_anti₀ hd hge
  have hinv_upper (x : ℝ) : ‖(((x : ℂ) + d * I)⁻¹)‖ ≤ d⁻¹ := by
    rw [norm_inv]
    have him : (((x : ℂ) + d * I)).im = d := by simp
    have hge : d ≤ ‖((x : ℂ) + d * I)‖ := by
      have h := Complex.abs_im_le_norm ((x : ℂ) + d * I)
      rw [him, abs_of_pos hd] at h
      exact h
    exact inv_anti₀ hd hge
  have hLint : Integrable L := by
    have hmajor : Integrable (fun x : ℝ =>
        (C * d⁻¹) * Real.exp (-(r * |x|))) :=
      (integrable_exp_neg_mul_abs' hr).const_mul (C * d⁻¹)
    refine Integrable.mono' hmajor ?_ (Filter.Eventually.of_forall fun x => ?_)
    · have hcont : Continuous L := by
        rw [continuous_iff_continuousAt]
        intro x
        have hzmem : ((x : ℂ) - d * I) ∈ {z : ℂ | |z.im| < a} := by
          change |(((x : ℂ) - d * I)).im| < a
          simpa [abs_of_pos hd] using hda
        have hz0 : ((x : ℂ) - d * I) ≠ 0 := by
          intro h
          have him := congrArg Complex.im h
          simp at him
          linarith
        exact (((hg _ hzmem).continuousAt.comp (x := x)
          (by fun_prop)).mul ((by fun_prop : ContinuousAt
            (fun y : ℝ => (((y : ℂ) - d * I)⁻¹)) x)))
      exact hcont.aestronglyMeasurable
    · simp only [L, norm_mul]
      have hb := hbound ((x : ℂ) - d * I) (by simp [abs_of_pos hd])
      have hre : (((x : ℂ) - d * I)).re = x := by simp
      rw [hre] at hb
      calc
        ‖F ((x : ℂ) - d * I)‖ * ‖(((x : ℂ) - d * I)⁻¹)‖ ≤
            (C * Real.exp (-(r * |x|))) * d⁻¹ :=
          mul_le_mul hb (hinv_lower x) (norm_nonneg _) (by positivity)
        _ = (C * d⁻¹) * Real.exp (-(r * |x|)) := by ring
  have hUint : Integrable U := by
    have hmajor : Integrable (fun x : ℝ =>
        (C * d⁻¹) * Real.exp (-(r * |x|))) :=
      (integrable_exp_neg_mul_abs' hr).const_mul (C * d⁻¹)
    refine Integrable.mono' hmajor ?_ (Filter.Eventually.of_forall fun x => ?_)
    · have hcont : Continuous U := by
        rw [continuous_iff_continuousAt]
        intro x
        have hzmem : ((x : ℂ) + d * I) ∈ {z : ℂ | |z.im| < a} := by
          change |(((x : ℂ) + d * I)).im| < a
          simpa [abs_of_pos hd] using hda
        have hz0 : ((x : ℂ) + d * I) ≠ 0 := by
          intro h
          have him := congrArg Complex.im h
          simp at him
          linarith
        exact (((hg _ hzmem).continuousAt.comp (x := x)
          (by fun_prop)).mul ((by
            apply ContinuousAt.inv₀
            · fun_prop
            · exact hz0) : ContinuousAt
              (fun y : ℝ => (((y : ℂ) + d * I)⁻¹)) x))
      exact hcont.aestronglyMeasurable
    · simp only [U, norm_mul]
      have hb := hbound ((x : ℂ) + d * I) (by simp [abs_of_pos hd])
      have hre : (((x : ℂ) + d * I)).re = x := by simp
      rw [hre] at hb
      calc
        ‖F ((x : ℂ) + d * I)‖ * ‖(((x : ℂ) + d * I)⁻¹)‖ ≤
            (C * Real.exp (-(r * |x|))) * d⁻¹ :=
          mul_le_mul hb (hinv_upper x) (norm_nonneg _) (by positivity)
        _ = (C * d⁻¹) * Real.exp (-(r * |x|)) := by ring
  have hULpoint (x : ℝ) : U x = -L (-x) := by
    have hz : ((x : ℂ) + d * I) = -(((-x : ℝ) : ℂ) - d * I) := by
      push_cast
      ring
    simp only [U, L, hz, heven, inv_neg]
    ring
  have hUL : (∫ x : ℝ, U x) = -(∫ x : ℝ, L x) := by
    calc
      (∫ x : ℝ, U x) = ∫ x : ℝ, -L (-x) := by
        exact integral_congr_ae (Filter.Eventually.of_forall hULpoint)
      _ = -(∫ x : ℝ, L (-x)) := by rw [integral_neg]
      _ = -(∫ x : ℝ, L x) := by
        rw [MeasureTheory.integral_neg_eq_self]
  have hbottom : Tendsto (fun R : ℝ => ∫ x in -R..R, L x)
      atTop (𝓝 (∫ x : ℝ, L x)) :=
    MeasureTheory.intervalIntegral_tendsto_integral hLint
      (tendsto_neg_atBot_iff.mpr tendsto_id) tendsto_id
  have htop : Tendsto (fun R : ℝ => ∫ x in -R..R, U x)
      atTop (𝓝 (∫ x : ℝ, U x)) :=
    MeasureTheory.intervalIntegral_tendsto_integral hUint
      (tendsto_neg_atBot_iff.mpr tendsto_id) tendsto_id
  let G : ℂ → ℂ := fun w => F (I * w) * ((I * w)⁻¹)
  have hM : Tendsto (fun T : ℝ => C * Real.exp (-(r * |T|)))
      atTop (𝓝 0) := by
    have hexp : Tendsto (fun T : ℝ => Real.exp (-(r * |T|)))
        atTop (𝓝 0) := by
      have harg : Tendsto (fun T : ℝ => -(r * |T|)) atTop atBot := by
        exact tendsto_neg_atTop_atBot.comp
          (Filter.Tendsto.const_mul_atTop hr tendsto_abs_atTop_atTop)
      exact Real.tendsto_exp_atBot.comp harg
    simpa using hexp.const_mul C
  have hGbound_all (T : ℝ) (hT : 1 ≤ |T|) :
      ∀ u ∈ Set.uIoc (-d) d,
        ‖G ((u : ℂ) + ((T : ℝ) : ℂ) * I)‖ ≤
          C * Real.exp (-(r * |T|)) := by
    intro u hu
    have huabs : |u| ≤ d := by
      rcases Set.mem_uIoc.mp hu with h | h
      · rw [abs_le]
        constructor <;> linarith
      · rw [abs_le]
        constructor <;> linarith
    have hpoint : I * ((u : ℂ) + (T : ℂ) * I) = (-T : ℂ) + u * I := by
      ring_nf
      rw [Complex.I_sq]
      ring
    simp only [G, hpoint, norm_mul]
    have hb := hbound ((-T : ℂ) + u * I) (by simpa using huabs)
    have hre : (((-T : ℂ) + u * I)).re = -T := by simp
    rw [hre, abs_neg] at hb
    have hinv : ‖(((-T : ℂ) + u * I)⁻¹)‖ ≤ 1 := by
      rw [norm_inv, inv_le_one₀]
      · have hrele := Complex.abs_re_le_norm ((-T : ℂ) + u * I)
        have hre : (((-T : ℂ) + u * I)).re = -T := by simp
        rw [hre, abs_neg] at hrele
        exact le_trans hT hrele
      · have hrele := Complex.abs_re_le_norm ((-T : ℂ) + u * I)
        have hre : (((-T : ℂ) + u * I)).re = -T := by simp
        rw [hre, abs_neg] at hrele
        exact lt_of_lt_of_le zero_lt_one (le_trans hT hrele)
    exact (mul_le_mul hb hinv (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
  have hGbound : ∀ᶠ T : ℝ in atTop,
      ∀ u ∈ Set.uIoc (-d) d,
        ‖G ((u : ℂ) + ((T : ℝ) : ℂ) * I)‖ ≤
          C * Real.exp (-(r * |T|)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact hGbound_all T (le_trans hT (le_abs_self T))
  have hright0 : Tendsto
      (fun T : ℝ => ∫ u in (-d)..d,
        F ((T : ℂ) + u * I) * (((T : ℂ) + u * I)⁻¹))
      atTop (𝓝 0) := by
    have hrot := GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
      (G := G) (c := -d) (d := d) (hgt := fun T : ℝ => -T)
      (M := fun T : ℝ => C * Real.exp (-(r * |T|))) ?_ hM
    · apply hrot.congr'
      filter_upwards with T
      apply intervalIntegral.integral_congr
      intro u hu
      have hpoint : I * ((u : ℂ) + ((-T : ℝ) : ℂ) * I) =
          (T : ℂ) + u * I := by
        push_cast
        ring_nf
        rw [Complex.I_sq]
        ring
      simp only [G, hpoint]
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      intro u hu
      simpa only [abs_neg] using hGbound_all (-T)
        (by simpa only [abs_neg] using le_trans hT (le_abs_self T)) u hu
  have hleft0 : Tendsto
      (fun T : ℝ => ∫ u in (-d)..d,
        F ((-T : ℂ) + u * I) * (((-T : ℂ) + u * I)⁻¹))
      atTop (𝓝 0) := by
    have hrot := GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
      (G := G) (c := -d) (d := d) (hgt := fun T : ℝ => T)
      (M := fun T : ℝ => C * Real.exp (-(r * |T|))) hGbound hM
    apply hrot.congr'
    filter_upwards with T
    apply intervalIntegral.integral_congr
    intro u hu
    have hpoint : I * ((u : ℂ) + (T : ℂ) * I) =
        (-T : ℂ) + u * I := by
      ring_nf
      rw [Complex.I_sq]
      ring
    simp only [G, hpoint]
  have hrect : ∀ᶠ R : ℝ in atTop,
      rectIntegral (fun z => F z * z⁻¹)
        ((-R : ℂ) - d * I) ((R : ℂ) + d * I) =
          2 * Real.pi * I * F 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hsub :
        (Set.uIcc (((-R : ℂ) - d * I).re) (((R : ℂ) + d * I).re) ×ℂ
          Set.uIcc (((-R : ℂ) - d * I).im) (((R : ℂ) + d * I).im)) ⊆
            {z : ℂ | |z.im| < a} := by
      intro z hz
      rw [Complex.mem_reProdIm] at hz
      have hzim : z.im ∈ Set.uIcc (-d) d := by
        simpa using hz.2
      rw [Set.uIcc_of_le (by linarith : -d ≤ d)] at hzim
      change |z.im| < a
      exact (abs_le.mpr hzim).trans_lt hda
    have h := rectIntegral_cauchyFormula_analyticOnNhd
      (g := F) (U := {z : ℂ | |z.im| < a}) (p := 0)
      (z₁ := ((-R : ℂ) - d * I)) (z₂ := ((R : ℂ) + d * I))
      hsub hg (by simp; linarith) (by simp; linarith)
      (by simp; linarith) (by simp; linarith)
    simpa using h
  have hexpr : Tendsto (fun R : ℝ =>
      (((∫ x in -R..R, L x) - ∫ x in -R..R, U x) +
          I * (∫ y in (-d)..d,
            F ((R : ℂ) + y * I) * (((R : ℂ) + y * I)⁻¹))) -
        I * (∫ y in (-d)..d,
          F ((-R : ℂ) + y * I) * (((-R : ℂ) + y * I)⁻¹)))
      atTop (𝓝 (((∫ x : ℝ, L x) - ∫ x : ℝ, U x) + I * 0 - I * 0)) := by
    exact ((hbottom.sub htop).add (hright0.const_mul I)).sub (hleft0.const_mul I)
  have hrectExpr : ∀ᶠ R : ℝ in atTop,
      (((∫ x in -R..R, L x) - ∫ x in -R..R, U x) +
          I * (∫ y in (-d)..d,
            F ((R : ℂ) + y * I) * (((R : ℂ) + y * I)⁻¹))) -
        I * (∫ y in (-d)..d,
          F ((-R : ℂ) + y * I) * (((-R : ℂ) + y * I)⁻¹)) =
        2 * Real.pi * I * F 0 := by
    filter_upwards [hrect] with R hR
    simpa [rectIntegral, L, U, sub_eq_add_neg] using hR
  have hconst : Tendsto (fun _R : ℝ => 2 * Real.pi * I * F 0)
      atTop (𝓝 (2 * Real.pi * I * F 0)) := tendsto_const_nhds
  have hconstExpr := hconst.congr' (Filter.EventuallyEq.symm hrectExpr)
  have hlimit : (∫ x : ℝ, L x) - ∫ x : ℝ, U x =
      2 * Real.pi * I * F 0 := by
    have hu := tendsto_nhds_unique hexpr hconstExpr
    simpa using hu
  have hfinal : (∫ x : ℝ, L x) = Real.pi * I * F 0 := by
    rw [hUL] at hlimit
    linear_combination (1 / 2 : ℂ) * hlimit
  simpa only [L] using hfinal

end

end RHTower
