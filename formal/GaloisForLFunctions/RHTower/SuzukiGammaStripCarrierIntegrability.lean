import GaloisForLFunctions.RHTower.GammaVerticalRatioAsymptotic
import GaloisForLFunctions.HTGeometry.PowerTailIntegral
import GaloisForLFunctions.HTGeometry.GammaVerticalRatioBound
import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# Integrability of the trace-zero Suzuki Gamma strip carrier

On the shifted frequency line `z = x + iσ`, the squared modulus of the scalar trace-zero
propagator

`z⁻¹/² [Γ(1+iz)/Γ(1-iz)]¹/²`

is exactly `suzukiGammaStripNormSq σ x`.  The vertical Gamma-ratio theorem makes this density
asymptotic to `|x|⁻¹⁻²σ`.  Hence it is integrable for every `0 < σ < 1`; `σ < 1` is the literal
first-Gamma-pole strip.
-/

open Complex Filter Topology MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Squared scalar norm of the Gamma propagator on `z = x + iσ`. -/
def suzukiGammaStripNormSq (σ x : ℝ) : ℝ :=
  (‖Complex.Gamma (((1 - σ : ℝ) : ℂ) + (x : ℂ) * I)‖ /
      ‖Complex.Gamma (((1 + σ : ℝ) : ℂ) + (x : ℂ) * I)‖) /
    ‖(x : ℂ) + (σ : ℂ) * I‖

private theorem gamma_pos_re_ne_neg_nat {a x : ℝ} (ha : 0 < a) (n : ℕ) :
    (a : ℂ) + (x : ℂ) * I ≠ -(n : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

private theorem gamma_pos_re_ne_zero {a x : ℝ} (ha : 0 < a) :
    Complex.Gamma ((a : ℂ) + (x : ℂ) * I) ≠ 0 :=
  Complex.Gamma_ne_zero (gamma_pos_re_ne_neg_nat ha)

/-- Exact vertical Gamma-ratio exponent on the trace-zero strip. -/
theorem suzukiGamma_vertical_ratio_rpow_tendsto
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    Tendsto (fun x : ℝ =>
      (‖Complex.Gamma (((1 - σ : ℝ) : ℂ) + (x : ℂ) * I)‖ /
        ‖Complex.Gamma (((1 + σ : ℝ) : ℂ) + (x : ℂ) * I)‖) * x ^ (2 * σ))
      atTop (nhds 1) := by
  have ha : 0 ≤ 1 - σ := by linarith
  have hδ : 0 ≤ 2 * σ := by linarith
  have h := _root_.RHTower.gamma_vertical_ratio_norm_rpow_tendsto ha hδ
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hnum : 0 < ‖Complex.Gamma (((1 - σ : ℝ) : ℂ) + (x : ℂ) * I)‖ :=
    norm_pos_iff.mpr (gamma_pos_re_ne_zero (by linarith))
  have hden : 0 < ‖Complex.Gamma (((1 + σ : ℝ) : ℂ) + (x : ℂ) * I)‖ :=
    norm_pos_iff.mpr (gamma_pos_re_ne_zero (by linarith))
  have harg : 1 - σ + 2 * σ = 1 + σ := by ring
  rw [harg]
  rw [Real.exp_sub, Real.exp_log hnum, Real.exp_log hden]

theorem tendsto_x_div_norm_add_I (σ : ℝ) :
    Tendsto (fun x : ℝ => x / ‖(x : ℂ) + (σ : ℂ) * I‖) atTop (nhds 1) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hsx : Tendsto (fun x : ℝ => σ * x⁻¹) atTop (nhds 0) := by
    simpa using hinv.const_mul σ
  have hbase : Tendsto (fun x : ℝ => (1 + (σ * x⁻¹) ^ 2)) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add (hsx.pow 2))
  have hsqrt : Tendsto (fun x : ℝ => Real.sqrt (1 + (σ * x⁻¹) ^ 2))
      atTop (nhds 1) := by
    simpa [Function.comp_def] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hbase)
  have hinv' : Tendsto (fun x : ℝ => (Real.sqrt (1 + (σ * x⁻¹) ^ 2))⁻¹)
      atTop (nhds 1) := by
    simpa using hsqrt.inv₀ one_ne_zero
  refine hinv'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [HTGeometry.norm_ofReal_add_mul_I]
  have hsqrtpos : 0 < Real.sqrt (x ^ 2 + σ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hxne : x ≠ 0 := ne_of_gt hx
  have hsq :
      Real.sqrt (1 + (σ * x⁻¹) ^ 2) = Real.sqrt (x ^ 2 + σ ^ 2) / x := by
    have hinside : 1 + (σ * x⁻¹) ^ 2 = (x ^ 2 + σ ^ 2) / x ^ 2 := by
      field_simp
    rw [hinside, Real.sqrt_div (by positivity)]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hx]
  rw [hsq]
  field_simp

/-- The squared strip carrier has exact tail exponent `1 + 2σ`. -/
theorem suzukiGammaStripNormSq_rpow_tendsto
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    Tendsto (fun x : ℝ =>
      suzukiGammaStripNormSq σ x * x ^ (1 + 2 * σ))
      atTop (nhds 1) := by
  have hratio := suzukiGamma_vertical_ratio_rpow_tendsto hσ0 hσ1
  have hnorm := tendsto_x_div_norm_add_I σ
  have hmul := hratio.mul hnorm
  have hcongr : (fun x : ℝ =>
      suzukiGammaStripNormSq σ x * x ^ (1 + 2 * σ)) =ᶠ[atTop]
      (fun x : ℝ =>
        (‖Complex.Gamma (((1 - σ : ℝ) : ℂ) + (x : ℂ) * I)‖ /
            ‖Complex.Gamma (((1 + σ : ℝ) : ℂ) + (x : ℂ) * I)‖ *
          x ^ (2 * σ)) *
        (x / ‖(x : ℂ) + (σ : ℂ) * I‖)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [suzukiGammaStripNormSq]
    have hrpow : x ^ (1 + 2 * σ) = x ^ (2 * σ) * x := by
      rw [Real.rpow_add hx]
      norm_num
      ring
    rw [hrpow]
    ring
  simpa using hmul.congr' hcongr.symm

@[simp] theorem suzukiGammaStripNormSq_neg (σ x : ℝ) :
    suzukiGammaStripNormSq σ (-x) = suzukiGammaStripNormSq σ x := by
  have hnum :
      (((1 - σ : ℝ) : ℂ) + ((-x : ℝ) : ℂ) * I) =
        starRingEnd ℂ (((1 - σ : ℝ) : ℂ) + (x : ℂ) * I) := by
    simp [map_add, map_mul, Complex.conj_I]
  have hden :
      (((1 + σ : ℝ) : ℂ) + ((-x : ℝ) : ℂ) * I) =
        starRingEnd ℂ (((1 + σ : ℝ) : ℂ) + (x : ℂ) * I) := by
    simp [map_add, map_mul, Complex.conj_I]
  have hz :
      (((-x : ℝ) : ℂ) + (σ : ℂ) * I) =
        -(starRingEnd ℂ ((x : ℂ) + (σ : ℂ) * I)) := by
    apply Complex.ext <;> simp
  simp only [suzukiGammaStripNormSq, hnum, hden, hz,
    Complex.Gamma_conj, norm_conj, norm_neg]

private theorem continuous_norm_Gamma_vertical {a : ℝ} (ha : 0 < a) :
    Continuous (fun x : ℝ =>
      ‖Complex.Gamma ((a : ℂ) + (x : ℂ) * I)‖) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hline : ContinuousAt (fun x : ℝ => (a : ℂ) + (x : ℂ) * I) x :=
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
  have hgamma : ContinuousAt Complex.Gamma ((a : ℂ) + (x : ℂ) * I) :=
    Complex.continuousAt_Gamma
      ((a : ℂ) + (x : ℂ) * I) (gamma_pos_re_ne_neg_nat ha)
  have hcomp := ContinuousAt.comp
    (f := fun x : ℝ => (a : ℂ) + (x : ℂ) * I)
    (g := Complex.Gamma) hgamma hline
  simpa [Function.comp_def] using (ContinuousAt.norm hcomp)

theorem continuous_suzukiGammaStripNormSq
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Continuous (suzukiGammaStripNormSq σ) := by
  have hnum := continuous_norm_Gamma_vertical (a := 1 - σ) (by linarith)
  have hden := continuous_norm_Gamma_vertical (a := 1 + σ) (by linarith)
  have hden_ne : ∀ x : ℝ,
      ‖Complex.Gamma (((1 + σ : ℝ) : ℂ) + (x : ℂ) * I)‖ ≠ 0 := by
    intro x
    exact norm_ne_zero_iff.mpr (gamma_pos_re_ne_zero (by linarith))
  have hz : Continuous (fun x : ℝ => ‖(x : ℂ) + (σ : ℂ) * I‖) := by
    exact (Complex.continuous_ofReal.add continuous_const).norm
  have hz_ne : ∀ x : ℝ, ‖(x : ℂ) + (σ : ℂ) * I‖ ≠ 0 := by
    intro x h
    rw [norm_eq_zero] at h
    have him := congrArg Complex.im h
    simp at him
    linarith
  exact (hnum.div hden hden_ne).div hz hz_ne

theorem suzukiGammaStripNormSq_isBigO
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    suzukiGammaStripNormSq σ =O[atTop]
      (fun x : ℝ => x ^ (-(1 + 2 * σ))) := by
  have htend :=
    suzukiGammaStripNormSq_rpow_tendsto (σ := σ) hσ0.le hσ1
  have hev : ∀ᶠ x : ℝ in atTop,
      suzukiGammaStripNormSq σ x * x ^ (1 + 2 * σ) < 2 :=
    htend.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  rw [Asymptotics.isBigO_iff]
  refine ⟨2, ?_⟩
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with x hxprod hx
  have hpow : 0 < x ^ (1 + 2 * σ) := Real.rpow_pos_of_pos hx _
  have hdensity : 0 ≤ suzukiGammaStripNormSq σ x := by
    unfold suzukiGammaStripNormSq
    positivity
  have hle :
      suzukiGammaStripNormSq σ x ≤ 2 * x ^ (-(1 + 2 * σ)) := by
    rw [Real.rpow_neg (le_of_lt hx)]
    apply (le_div_iff₀ hpow).mpr
    nlinarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hdensity,
    abs_of_pos (Real.rpow_pos_of_pos hx _)]
  exact hle

/-- **Trace-zero Gamma strip carrier is square integrable.** -/
theorem integrable_suzukiGammaStripNormSq
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Integrable (suzukiGammaStripNormSq σ) := by
  have hlocal : LocallyIntegrable (suzukiGammaStripNormSq σ) volume :=
    (continuous_suzukiGammaStripNormSq hσ0 hσ1).locallyIntegrable
  have hsymm :
      norm ∘ suzukiGammaStripNormSq σ =ᵐ[volume]
        norm ∘ suzukiGammaStripNormSq σ ∘ Neg.neg := by
    filter_upwards [] with x
    simp [Function.comp_def]
  apply hlocal.integrable_of_isBigO_atTop_of_norm_isNegInvariant hsymm
    (suzukiGammaStripNormSq_isBigO hσ0 hσ1)
  rw [integrableAtFilter_rpow_atTop_iff]
  linarith

end GaloisForLFunctions.RHTower
