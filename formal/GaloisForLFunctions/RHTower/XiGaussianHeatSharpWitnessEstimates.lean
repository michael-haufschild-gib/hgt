import GaloisForLFunctions.RHTower.XiGaussianHeatSharpWitnessSetup

/-!
# Strip-weighted estimates for the heat-smoothed source and its truncation

For a smooth source `u` vanishing outside `[−A, A]` and `u_a = u ⋆ G_a`:

* `|u_a(x)| ≤ ‖u‖₁ (2πa)^{-1/2}` everywhere, and `≤ ‖u‖₁ (2πa)^{-1/2} e^{-x²/(8a)}` for `|x| ≥ 2A`
  (`abs_heatSmooth_le`, `abs_heatSmooth_le_of_far`);
* `∫_{|x| ≥ X} |u_a| e^{|x|/2} ≤ 4 ‖u‖₁ e^{-X²/(32a)}` for `a ≤ 1/16`, `X ≥ max(1, 2A)`
  (`setIntegral_tail_heatSmooth_le`);
* on `|x| < X`, `(∫ |f| e^{|x|/2})² ≤ 2eπ e^{X²} ∫ f²` (`sq_setIntegral_inner_abs_mul_exp_half_le`).
-/

open scoped Real
open Complex MeasureTheory Set
open GaloisForLFunctions (sq_setIntegral_abs_mul_exp_half_le)

namespace RHTower

noncomputable section

variable {a A : ℝ} {u : ℝ → ℝ}

theorem continuous_heatSmooth (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcpt : HasCompactSupport u)
    (ha : 0 < a) : Continuous (heatSmooth a u) := by
  have h : heatSmooth a u = fun x => (sourceSmooth u hu hcpt ha (x / heatHermiteScale a)).re := by
    funext x
    rw [sourceSmooth_apply, mul_div_cancel₀ _ (heatHermiteScale_pos ha).ne', Complex.ofReal_re]
  rw [h]
  exact Complex.continuous_re.comp ((sourceSmooth u hu hcpt ha).continuous.comp
    (continuous_id.div_const _))

theorem heatKernel_le (ha : 0 < a) (x : ℝ) : gaussHeatKernel a x ≤ (2 * π * a) ^ (-(1 / 2 : ℝ)) := by
  rw [gaussHeatKernel]
  have h1 : Real.exp (-(x ^ 2 / (2 * a))) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ x ^ 2 / (2 * a) := by positivity
    linarith)
  have h2 : 0 ≤ (2 * π * a) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
  nlinarith

theorem heatKernel_nonneg (ha : 0 < a) (x : ℝ) : 0 ≤ gaussHeatKernel a x := by
  rw [gaussHeatKernel]
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le

theorem integrable_mul_heatKernel (hu : Continuous u) (hcpt : HasCompactSupport u) (x : ℝ) :
    Integrable (fun t => u t * gaussHeatKernel a (x - t)) := by
  refine (hu.mul ?_).integrable_of_hasCompactSupport hcpt.mul_right
  unfold gaussHeatKernel
  fun_prop

/-- `|u_a(x)| ≤ ‖u‖₁ (2πa)^{-1/2}`. -/
theorem abs_heatSmooth_le (hu : Continuous u) (hcpt : HasCompactSupport u) (ha : 0 < a) (x : ℝ) :
    |heatSmooth a u x| ≤ (∫ t, |u t|) * (2 * π * a) ^ (-(1 / 2 : ℝ)) := by
  rw [heatSmooth, ← integral_mul_const]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    ((hu.abs.integrable_of_hasCompactSupport hcpt.abs).mul_const _)
    (Filter.Eventually.of_forall fun t => ?_))
  simp only
  rw [abs_mul, abs_of_nonneg (heatKernel_nonneg ha _)]
  exact mul_le_mul_of_nonneg_left (heatKernel_le ha _) (abs_nonneg _)

/-- Far from the support, `|u_a(x)| ≤ ‖u‖₁ (2πa)^{-1/2} e^{-x²/(8a)}`. -/
theorem abs_heatSmooth_le_of_far (hu : Continuous u) (hcpt : HasCompactSupport u)
    (hsupp : ∀ t : ℝ, A < |t| → u t = 0) (ha : 0 < a) {x : ℝ} (hx : 2 * A ≤ |x|) :
    |heatSmooth a u x| ≤
      (∫ t, |u t|) * ((2 * π * a) ^ (-(1 / 2 : ℝ)) * Real.exp (-(x ^ 2 / (8 * a)))) := by
  rw [heatSmooth, ← integral_mul_const]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    ((hu.abs.integrable_of_hasCompactSupport hcpt.abs).mul_const _)
    (Filter.Eventually.of_forall fun t => ?_))
  simp only
  rw [abs_mul, abs_of_nonneg (heatKernel_nonneg ha _)]
  by_cases ht : A < |t|
  · rw [hsupp t ht, abs_zero, zero_mul, zero_mul]
  · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [gaussHeatKernel]
    have hxt : x ^ 2 / 4 ≤ (x - t) ^ 2 := by
      have h1 : |x| / 2 ≤ |x - t| := by
        have := abs_sub_abs_le_abs_sub x t
        linarith
      have h2 : (|x| / 2) ^ 2 ≤ |x - t| ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      rw [div_pow, sq_abs, sq_abs] at h2
      linarith
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg (by positivity) _)
    rw [neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

theorem integrableOn_tail_heatSmooth (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcpt : HasCompactSupport u)
    (hsupp : ∀ t : ℝ, A < |t| → u t = 0) (ha : 0 < a) (ha16 : a ≤ 1 / 16) {X : ℝ}
    (hX1 : 1 ≤ X) (hX : 2 * A ≤ X) :
    IntegrableOn (fun x => |heatSmooth a u x| * Real.exp (|x| / 2)) (heatTailSet X) ∧
      ∫ x in heatTailSet X, |heatSmooth a u x| * Real.exp (|x| / 2) ≤
        4 * (∫ t, |u t|) * Real.exp (-(X ^ 2 / (32 * a))) := by
  set U := ∫ t, |u t| with hU
  have hU0 : 0 ≤ U := integral_nonneg fun _ => abs_nonneg _
  set c := (2 * π * a) ^ (-(1 / 2 : ℝ)) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by positivity) _
  have hb : 0 < 1 / (32 * a) := by positivity
  have hgi : Integrable (fun x : ℝ => Real.exp (-(1 / (32 * a)) * x ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  set B : ℝ → ℝ := fun x => U * c * Real.exp (-(X ^ 2 / (32 * a))) *
    Real.exp (-(1 / (32 * a)) * x ^ 2) with hB
  have hpt : ∀ x ∈ heatTailSet X, |heatSmooth a u x| * Real.exp (|x| / 2) ≤ B x := by
    intro x hx
    have hxX : X ≤ |x| := hx
    have hfar := abs_heatSmooth_le_of_far hu.continuous hcpt hsupp ha (hX.trans hxX)
    have hexp : -(x ^ 2 / (8 * a)) + |x| / 2 ≤ -(X ^ 2 / (32 * a)) + -(1 / (32 * a)) * x ^ 2 := by
      have hx2 : X ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x]
      have h8 : 8 * a ≤ |x| := by linarith
      have hsq : |x| * (8 * a) ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
      have e1 : |x| / 2 ≤ x ^ 2 / (16 * a) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have e2 : x ^ 2 / (8 * a) = x ^ 2 / (16 * a) + x ^ 2 / (16 * a) := by field_simp; ring
      have e3 : X ^ 2 / (32 * a) + 1 / (32 * a) * x ^ 2 ≤ x ^ 2 / (16 * a) := by
        have : X ^ 2 / (32 * a) + 1 / (32 * a) * x ^ 2 = (X ^ 2 + x ^ 2) / (32 * a) := by ring
        rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
    calc |heatSmooth a u x| * Real.exp (|x| / 2)
        ≤ U * (c * Real.exp (-(x ^ 2 / (8 * a)))) * Real.exp (|x| / 2) :=
          mul_le_mul_of_nonneg_right hfar (Real.exp_pos _).le
      _ = U * c * Real.exp (-(x ^ 2 / (8 * a)) + |x| / 2) := by rw [Real.exp_add]; ring
      _ ≤ U * c * Real.exp (-(X ^ 2 / (32 * a)) + -(1 / (32 * a)) * x ^ 2) := by gcongr
      _ = B x := by rw [hB, Real.exp_add]; ring
  have hBi : Integrable B := (hgi.const_mul _)
  have hmeas : AEStronglyMeasurable (fun x => |heatSmooth a u x| * Real.exp (|x| / 2))
      (volume.restrict (heatTailSet X)) :=
    ((continuous_abs.comp (continuous_heatSmooth hu hcpt ha)).mul
      (Real.continuous_exp.comp (continuous_abs.div_const 2))).aestronglyMeasurable
  have hint : IntegrableOn (fun x => |heatSmooth a u x| * Real.exp (|x| / 2)) (heatTailSet X) :=
    hBi.integrableOn.mono' hmeas ((ae_restrict_iff' (measurableSet_heatTailSet X)).2
      (Filter.Eventually.of_forall fun x hx => by
        rw [Real.norm_of_nonneg (by positivity)]; exact hpt x hx))
  refine ⟨hint, ?_⟩
  calc ∫ x in heatTailSet X, |heatSmooth a u x| * Real.exp (|x| / 2)
      ≤ ∫ x in heatTailSet X, B x :=
        setIntegral_mono_on hint hBi.integrableOn (measurableSet_heatTailSet X) hpt
    _ ≤ ∫ x, B x := setIntegral_le_integral hBi (Filter.Eventually.of_forall fun x => by
        rw [hB]; positivity)
    _ = U * c * Real.exp (-(X ^ 2 / (32 * a))) * Real.sqrt (π / (1 / (32 * a))) := by
        rw [hB, integral_const_mul, integral_gaussian]
    _ = 4 * U * Real.exp (-(X ^ 2 / (32 * a))) := by
        have hsq : c * Real.sqrt (π / (1 / (32 * a))) = 4 := by
          rw [hc, show π / (1 / (32 * a)) = 16 * (2 * π * a) by field_simp; ring,
            Real.sqrt_mul (by norm_num), show Real.sqrt 16 = 4 by
              rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
            Real.sqrt_eq_rpow, ← mul_assoc, mul_comm _ (4 : ℝ), mul_assoc,
            ← Real.rpow_add (by positivity)]
          norm_num
        calc U * c * Real.exp (-(X ^ 2 / (32 * a))) * Real.sqrt (π / (1 / (32 * a)))
            = U * (c * Real.sqrt (π / (1 / (32 * a)))) * Real.exp (-(X ^ 2 / (32 * a))) := by
              ring
          _ = 4 * U * Real.exp (-(X ^ 2 / (32 * a))) := by rw [hsq]; ring

/-- On `|x| < X`, `(∫ |f| e^{|x|/2})² ≤ 2eπ e^{X²} ∫ f²`. -/
theorem sq_setIntegral_inner_abs_mul_exp_half_le {f : ℝ → ℝ} (hf : Continuous f)
    (hf2 : Integrable (fun x => f x ^ 2)) {X : ℝ} (hX : 0 ≤ X) :
    IntegrableOn (fun x => |f x| * Real.exp (|x| / 2)) (Ioo (-X) X) ∧
      (∫ x in Ioo (-X) X, |f x| * Real.exp (|x| / 2)) ^ 2 ≤
        2 * Real.exp 1 * π * Real.exp (X ^ 2) * ∫ x, f x ^ 2 := by
  have hcont : Continuous fun x => f x ^ 2 * Real.exp (x ^ 2) :=
    (hf.pow 2).mul (Real.continuous_exp.comp (continuous_pow 2))
  have hIcc : IntegrableOn (fun x => f x ^ 2 * Real.exp (x ^ 2)) (Icc (-X) X) :=
    hcont.continuousOn.integrableOn_Icc
  obtain ⟨hI, hsq⟩ := sq_setIntegral_abs_mul_exp_half_le hf measurableSet_Ioo
    (hIcc.mono_set Ioo_subset_Icc_self)
  refine ⟨hI, hsq.trans ?_⟩
  have hin : ∫ x in Ioo (-X) X, f x ^ 2 * Real.exp (x ^ 2) ≤
      ∫ x in Ioo (-X) X, Real.exp (X ^ 2) * f x ^ 2 := by
    refine setIntegral_mono_on (hIcc.mono_set Ioo_subset_Icc_self)
      (hf2.integrableOn.const_mul _) measurableSet_Ioo fun x hx => ?_
    have hx2 : x ^ 2 ≤ X ^ 2 := by
      have := abs_lt.2 ⟨hx.1, hx.2⟩
      nlinarith [sq_abs x, abs_nonneg x]
    have := Real.exp_le_exp.2 hx2
    nlinarith [sq_nonneg (f x)]
  rw [integral_const_mul] at hin
  have hin2 : ∫ x in Ioo (-X) X, f x ^ 2 ≤ ∫ x, f x ^ 2 :=
    setIntegral_le_integral hf2 (Filter.Eventually.of_forall fun x => sq_nonneg _)
  have he : 0 ≤ 2 * Real.exp 1 * π := by positivity
  calc 2 * Real.exp 1 * π * ∫ x in Ioo (-X) X, f x ^ 2 * Real.exp (x ^ 2)
      ≤ 2 * Real.exp 1 * π * (Real.exp (X ^ 2) * ∫ x in Ioo (-X) X, f x ^ 2) :=
        mul_le_mul_of_nonneg_left hin he
    _ ≤ 2 * Real.exp 1 * π * (Real.exp (X ^ 2) * ∫ x, f x ^ 2) := by gcongr
    _ = _ := by ring

end

end RHTower
