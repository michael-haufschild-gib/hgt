import GaloisForLFunctions.HTGeometry.FourierScaledInversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Lorentzian cosine integrals with a complex width

For `w` in the open upper half-plane the two-sided exponential `e^{iw|y|}` is integrable, with
Fourier transform `2iw / (w² - (2πξ)²)`.  Fourier inversion, rescaled to the angular frequency,
gives

`∫_ℝ e^{itx} / (t² - w²) dt = (πi/w) e^{iw|x|}`,

and hence the half-line cosine and subtracted-cosine integrals

`∫₀^∞ cos(tx) / (t² - w²) dt = (πi/(2w)) e^{iw|x|}`,
`∫₀^∞ (1 - cos(tx)) / (t² - w²) dt = (πi/(2w)) (1 - e^{iw|x|})`.

The kernel `t² - w²` is bounded below by a multiple of `1 + t²`, since `w²` avoids the closed
positive half-line.  At `w = ir` the formulas specialise to the real Poisson kernel.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MeasureTheory Complex FourierTransform Set Filter

/-- Away from the closed positive half-line, `t ↦ t - ζ` grows linearly on `[0, ∞)`. -/
theorem exists_mul_one_add_le_norm_sub {ζ : ℂ} (hζ : -ζ ∈ slitPlane) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t → c * (1 + t) ≤ ‖(t : ℂ) - ζ‖ := by
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 ≤ t → δ ≤ ‖(t : ℂ) - ζ‖ := by
    rcases hζ with h | h
    · refine ⟨-ζ.re, by simpa using h, fun t ht => ?_⟩
      have := Complex.abs_re_le_norm ((t : ℂ) - ζ)
      simp only [sub_re, ofReal_re] at this
      have h' : -ζ.re ≤ |t - ζ.re| := le_trans (by linarith) (le_abs_self _)
      linarith
    · refine ⟨|ζ.im|, abs_pos.mpr (by simpa using h), fun t _ => ?_⟩
      have := Complex.abs_im_le_norm ((t : ℂ) - ζ)
      simpa using this
  refine ⟨δ / (1 + ‖ζ‖ + δ), by positivity, fun t ht => ?_⟩
  have hn : t - ‖ζ‖ ≤ ‖(t : ℂ) - ζ‖ := by
    have := norm_sub_norm_le (t : ℂ) ζ
    rwa [Complex.norm_real, Real.norm_of_nonneg ht] at this
  have hpos : 0 < 1 + ‖ζ‖ + δ := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  have hz := norm_nonneg ζ
  rcases le_or_gt t (‖ζ‖ + δ) with htle | htgt
  · nlinarith [hδle t ht]
  · nlinarith

/-- A square of an upper half-plane point avoids the closed positive half-line. -/
theorem neg_sq_mem_slitPlane {w : ℂ} (hw : 0 < w.im) : -(w ^ 2) ∈ slitPlane := by
  rcases eq_or_ne w.re 0 with h | h
  · left
    simp only [neg_re, sq, mul_re, h, zero_mul, zero_sub, neg_neg]
    positivity
  · right
    simp only [neg_im, sq, mul_im, ne_eq, neg_eq_zero]
    intro h'
    have : w.re * w.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact h h1
    · exact hw.ne' h1

/-- The squared kernel `t² - w²` grows quadratically on the real line when `Im w > 0`. -/
theorem exists_mul_one_add_sq_le_norm_sq_sub {w : ℂ} (hw : 0 < w.im) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, c * (1 + t ^ 2) ≤ ‖(t : ℂ) ^ 2 - w ^ 2‖ := by
  obtain ⟨c, hc, h⟩ := exists_mul_one_add_le_norm_sub (neg_sq_mem_slitPlane hw)
  exact ⟨c, hc, fun t => by simpa using h (t ^ 2) (sq_nonneg t)⟩

theorem sq_sub_sq_ne_zero {w : ℂ} (hw : 0 < w.im) (t : ℝ) : (t : ℂ) ^ 2 - w ^ 2 ≠ 0 := by
  obtain ⟨c, hc, h⟩ := exists_mul_one_add_sq_le_norm_sq_sub hw
  intro h0
  have := h t
  rw [h0, norm_zero] at this
  nlinarith [sq_nonneg t]

/-- The reciprocal of the squared kernel is integrable on the line. -/
theorem integrable_inv_sq_sub_sq {w : ℂ} (hw : 0 < w.im) :
    Integrable fun t : ℝ => ((t : ℂ) ^ 2 - w ^ 2)⁻¹ := by
  obtain ⟨c, hc, h⟩ := exists_mul_one_add_sq_le_norm_sq_sub hw
  refine (integrable_inv_one_add_sq.const_mul c⁻¹).mono' (by fun_prop) ?_
  refine Eventually.of_forall fun t => ?_
  have hpos : 0 < 1 + t ^ 2 := by positivity
  rw [norm_inv, inv_eq_one_div, div_le_iff₀ (lt_of_lt_of_le (by positivity) (h t))]
  calc (1 : ℝ) = c⁻¹ * (1 + t ^ 2)⁻¹ * (c * (1 + t ^ 2)) := by field_simp
    _ ≤ c⁻¹ * (1 + t ^ 2)⁻¹ * ‖(t : ℂ) ^ 2 - w ^ 2‖ := by gcongr; exact h t

theorem integrable_mul_inv_sq_sub_sq {w : ℂ} (hw : 0 < w.im) {g : ℝ → ℂ}
    (hg : Continuous g) (hb : ∀ t, ‖g t‖ ≤ 1) :
    Integrable fun t : ℝ => g t / ((t : ℂ) ^ 2 - w ^ 2) := by
  refine (integrable_inv_sq_sub_sq hw).norm.mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact (hg.div (by fun_prop) (sq_sub_sq_ne_zero hw)).aestronglyMeasurable
  · rw [norm_div, div_eq_mul_inv, norm_inv]
    exact mul_le_of_le_one_left (by positivity) (hb t)

/-! ## The two-sided exponential and its Fourier transform -/

/-- The two-sided exponential `e^{iw|y|}`. -/
def upperTwoSidedExp (w : ℂ) (y : ℝ) : ℂ := cexp (I * w * |y|)

theorem continuous_upperTwoSidedExp (w : ℂ) : Continuous (upperTwoSidedExp w) := by
  unfold upperTwoSidedExp; fun_prop

theorem integrableOn_Ioi_cexp_I_mul {w : ℂ} (hw : 0 < w.im) (c : ℝ) :
    IntegrableOn (fun y : ℝ => cexp (I * w * y)) (Ioi c) :=
  integrableOn_exp_mul_complex_Ioi (by simpa using hw) c

theorem integrable_upperTwoSidedExp {w : ℂ} (hw : 0 < w.im) : Integrable (upperTwoSidedExp w) := by
  have hIoi : IntegrableOn (upperTwoSidedExp w) (Ioi 0) :=
    (integrableOn_Ioi_cexp_I_mul hw 0).congr_fun
      (fun y hy => by simp [upperTwoSidedExp, abs_of_pos (mem_Ioi.mp hy)]) measurableSet_Ioi
  have hIci : IntegrableOn (fun y : ℝ => cexp (I * w * y)) (Ici (-0)) := by
    rw [neg_zero, integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_cexp_I_mul hw 0
  have hIic : IntegrableOn (upperTwoSidedExp w) (Iic 0) :=
    hIci.comp_neg_Iic.congr_fun
      (fun y hy => by simp [upperTwoSidedExp, abs_of_nonpos (mem_Iic.mp hy)]) measurableSet_Iic
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hIoi

theorem integral_Ioi_cexp_I_mul {w : ℂ} (hw : 0 < w.im) :
    ∫ y in Ioi (0 : ℝ), cexp (I * w * y) = I / w := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  rw [integral_exp_mul_complex_Ioi (by simpa using hw) 0]
  field_simp
  simp

/-- The Fourier transform of `e^{iw|y|}` is `2iw / (w² - (2πξ)²)`. -/
theorem fourier_upperTwoSidedExp {w : ℂ} (hw : 0 < w.im) (ξ : ℝ) :
    𝓕 (upperTwoSidedExp w) ξ = 2 * I * w / (w ^ 2 - ((2 * Real.pi * ξ : ℝ) : ℂ) ^ 2) := by
  set a : ℂ := ((2 * Real.pi * ξ : ℝ) : ℂ)
  have hp : 0 < (w - a).im := by simpa [a] using hw
  have hm : 0 < (w + a).im := by simpa [a] using hw
  have hp0 : w - a ≠ 0 := fun h => by simp [h] at hp
  have hm0 : w + a ≠ 0 := fun h => by simp [h] at hm
  have hsq : w ^ 2 - a ^ 2 ≠ 0 := by
    rw [show w ^ 2 - a ^ 2 = (w - a) * (w + a) by ring]; exact mul_ne_zero hp0 hm0
  rw [Real.fourier_real_eq_integral_exp_smul]
  set F : ℝ → ℂ := fun v => cexp (↑(-2 * Real.pi * v * ξ) * I) • upperTwoSidedExp w v
  have hIoi : ∀ v ∈ Ioi (0 : ℝ), F v = cexp (I * (w - a) * v) := by
    intro v hv
    simp only [F, upperTwoSidedExp, abs_of_pos (mem_Ioi.mp hv), smul_eq_mul, ← Complex.exp_add, a]
    congr 1; push_cast; ring
  have hIic : ∀ v ∈ Ioi (0 : ℝ), F (-v) = cexp (I * (w + a) * v) := by
    intro v hv
    simp only [F, upperTwoSidedExp, abs_neg, abs_of_pos (mem_Ioi.mp hv), smul_eq_mul,
      ← Complex.exp_add, a]
    congr 1; push_cast; ring
  have hint : Integrable F := by
    refine (integrable_upperTwoSidedExp hw).norm.mono' ?_ (Eventually.of_forall fun v => ?_)
    · exact (by unfold F upperTwoSidedExp; fun_prop : Continuous F).aestronglyMeasurable
    · simp only [F, smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
  have hneg : ∫ v in Iic (0 : ℝ), F v = ∫ v in Ioi (0 : ℝ), F (-v) := by
    rw [integral_comp_neg_Ioi]; simp
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn,
    hneg, setIntegral_congr_fun measurableSet_Ioi hIic,
    setIntegral_congr_fun measurableSet_Ioi hIoi, integral_Ioi_cexp_I_mul hm,
    integral_Ioi_cexp_I_mul hp]
  field_simp
  ring

theorem integrable_fourier_upperTwoSidedExp {w : ℂ} (hw : 0 < w.im) :
    Integrable (𝓕 (upperTwoSidedExp w)) := by
  have hint : Integrable fun ξ : ℝ =>
      -(2 * I * w) * (((2 * Real.pi * ξ : ℝ) : ℂ) ^ 2 - w ^ 2)⁻¹ := by
    refine Integrable.const_mul ?_ _
    have h := (integrable_inv_sq_sub_sq hw).comp_mul_left' (R := 2 * Real.pi)
      (by positivity)
    simpa using h
  refine hint.congr (Eventually.of_forall fun ξ => ?_)
  rw [fourier_upperTwoSidedExp hw]
  have h0 := sq_sub_sq_ne_zero hw (2 * Real.pi * ξ)
  have h1 : w ^ 2 - ((2 * Real.pi * ξ : ℝ) : ℂ) ^ 2 ≠ 0 := by
    intro h; apply h0; linear_combination -h
  field_simp
  ring

/-! ## The Lorentzian cosine integrals -/

/-- **Lorentzian exponential integral.** For `Im w > 0`,
`∫_ℝ e^{itx} / (t² - w²) dt = (πi/w) e^{iw|x|}`. -/
theorem integral_cexp_div_sq_sub_sq {w : ℂ} (hw : 0 < w.im) (x : ℝ) :
    ∫ t : ℝ, cexp (I * t * x) / ((t : ℂ) ^ 2 - w ^ 2) =
      Real.pi * I / w * cexp (I * w * |x|) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have h := _root_.HTGeometry.integral_exp_mul_fourier_scaled (continuous_upperTwoSidedExp w)
    (integrable_upperTwoSidedExp hw) (integrable_fourier_upperTwoSidedExp hw) (-x)
  have hcongr : ∀ t : ℝ, cexp (-I * t * ((-x : ℝ) : ℂ)) * 𝓕 (upperTwoSidedExp w) (t / (2 * Real.pi)) =
      (-(2 * I * w)) * (cexp (I * t * x) / ((t : ℂ) ^ 2 - w ^ 2)) := by
    intro t
    rw [fourier_upperTwoSidedExp hw]
    have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have h0 := sq_sub_sq_ne_zero hw t
    have h1 : w ^ 2 - ((2 * Real.pi * (t / (2 * Real.pi)) : ℝ) : ℂ) ^ 2 ≠ 0 := by
      rw [show 2 * Real.pi * (t / (2 * Real.pi)) = t by field_simp]
      intro h; apply h0; linear_combination -h
    rw [show 2 * Real.pi * (t / (2 * Real.pi)) = t by field_simp] at h1 ⊢
    field_simp
    push_cast
    ring_nf
  simp_rw [hcongr, integral_const_mul] at h
  rw [upperTwoSidedExp, neg_neg] at h
  set J := ∫ t : ℝ, cexp (I * t * x) / ((t : ℂ) ^ 2 - w ^ 2)
  field_simp
  linear_combination (I / 2) * h + J * w * I_sq

theorem norm_cexp_I_mul_ofReal_mul (t x : ℝ) : ‖cexp (I * t * x)‖ = 1 := by
  rw [norm_exp]; simp

theorem integrable_cexp_div_sq_sub_sq {w : ℂ} (hw : 0 < w.im) (x : ℝ) :
    Integrable fun t : ℝ => cexp (I * t * x) / ((t : ℂ) ^ 2 - w ^ 2) :=
  integrable_mul_inv_sq_sub_sq hw (by fun_prop) fun t => (norm_cexp_I_mul_ofReal_mul t x).le

theorem integrable_cos_div_sq_sub_sq {w : ℂ} (hw : 0 < w.im) (x : ℝ) :
    Integrable fun t : ℝ => (Real.cos (t * x) : ℂ) / ((t : ℂ) ^ 2 - w ^ 2) :=
  integrable_mul_inv_sq_sub_sq hw (by fun_prop) fun t => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _

/-- **Lorentzian cosine integral on the line.** For `Im w > 0`,
`∫_ℝ cos(tx) / (t² - w²) dt = (πi/w) e^{iw|x|}`. -/
theorem integral_cos_div_sq_sub_sq {w : ℂ} (hw : 0 < w.im) (x : ℝ) :
    ∫ t : ℝ, (Real.cos (t * x) : ℂ) / ((t : ℂ) ^ 2 - w ^ 2) =
      Real.pi * I / w * cexp (I * w * |x|) := by
  have hcos : ∀ t : ℝ, (Real.cos (t * x) : ℂ) / ((t : ℂ) ^ 2 - w ^ 2) =
      (1 / 2 : ℂ) * (cexp (I * t * x) / ((t : ℂ) ^ 2 - w ^ 2) +
        cexp (I * t * ((-x : ℝ) : ℂ)) / ((t : ℂ) ^ 2 - w ^ 2)) := by
    intro t
    rw [Complex.ofReal_cos, Complex.cos]
    push_cast
    ring_nf
  simp_rw [hcos]
  rw [integral_const_mul, integral_add (integrable_cexp_div_sq_sub_sq hw x)
    (integrable_cexp_div_sq_sub_sq hw (-x)), integral_cexp_div_sq_sub_sq hw,
    integral_cexp_div_sq_sub_sq hw, abs_neg]
  ring

/-- **Lorentzian cosine integral on the half-line.** For `Im w > 0`,
`∫₀^∞ cos(tx) / (t² - w²) dt = (πi/(2w)) e^{iw|x|}`. -/
theorem integral_Ioi_cos_div_sq_sub_sq {w : ℂ} (hw : 0 < w.im) (x : ℝ) :
    ∫ t in Ioi (0 : ℝ), (Real.cos (t * x) : ℂ) / ((t : ℂ) ^ 2 - w ^ 2) =
      Real.pi * I / (2 * w) * cexp (I * w * |x|) := by
  have hint := integrable_cos_div_sq_sub_sq hw x
  have hneg : ∫ t in Iic (0 : ℝ), (Real.cos (t * x) : ℂ) / ((t : ℂ) ^ 2 - w ^ 2) =
      ∫ t in Ioi (0 : ℝ), (Real.cos (t * x) : ℂ) / ((t : ℂ) ^ 2 - w ^ 2) := by
    rw [show Iic (0 : ℝ) = Iic (-0) by simp, ← integral_comp_neg_Ioi]
    simp [neg_mul, Real.cos_neg]
  have h := intervalIntegral.integral_Iic_add_Ioi (b := 0) hint.integrableOn hint.integrableOn
  rw [hneg, integral_cos_div_sq_sub_sq hw] at h
  rw [show Real.pi * I / (2 * w) * cexp (I * w * |x|) =
    (Real.pi * I / w * cexp (I * w * |x|)) / 2 by ring, ← h]
  ring

theorem integrableOn_Ioi_one_sub_cos_div_sq_sub_sq {w : ℂ} (hw : 0 < w.im) (x : ℝ) :
    IntegrableOn (fun t : ℝ => (1 - (Real.cos (t * x) : ℂ)) / ((t : ℂ) ^ 2 - w ^ 2))
      (Ioi 0) := by
  have h := ((integrable_cos_div_sq_sub_sq hw 0).sub
    (integrable_cos_div_sq_sub_sq hw x)).integrableOn (s := Ioi 0)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply, mul_zero, Real.cos_zero, ofReal_one, sub_div]

/-- **The subtracted Lorentzian cosine integral.** For `Im w > 0`,
`∫₀^∞ (1 - cos(tx)) / (t² - w²) dt = (πi/(2w)) (1 - e^{iw|x|})`. -/
theorem integral_Ioi_one_sub_cos_div_sq_sub_sq {w : ℂ} (hw : 0 < w.im) (x : ℝ) :
    ∫ t in Ioi (0 : ℝ), (1 - (Real.cos (t * x) : ℂ)) / ((t : ℂ) ^ 2 - w ^ 2) =
      Real.pi * I / (2 * w) * (1 - cexp (I * w * |x|)) := by
  have h0 := integral_Ioi_cos_div_sq_sub_sq hw 0
  simp only [mul_zero, Real.cos_zero, ofReal_one, abs_zero, ofReal_zero, Complex.exp_zero,
    mul_one] at h0
  simp_rw [sub_div]
  rw [integral_sub ((integrable_cos_div_sq_sub_sq hw 0).integrableOn.congr_fun
      (fun t _ => by simp) measurableSet_Ioi) (integrable_cos_div_sq_sub_sq hw x).integrableOn,
    h0, integral_Ioi_cos_div_sq_sub_sq hw]
  ring

/-- **The real subtracted Lorentzian integral.** For `r > 0`,
`∫₀^∞ (1 - cos(tx)) / (t² + r²) dt = (π/(2r)) (1 - e^{-r|x|})`. -/
theorem integral_Ioi_one_sub_cos_div_sq_add_sq {r : ℝ} (hr : 0 < r) (x : ℝ) :
    ∫ t in Ioi (0 : ℝ), (1 - Real.cos (t * x)) / (t ^ 2 + r ^ 2) =
      Real.pi / (2 * r) * (1 - Real.exp (-(r * |x|))) := by
  have hw : 0 < (I * r).im := by simpa using hr
  have h := integral_Ioi_one_sub_cos_div_sq_sub_sq hw x
  have hc : ∀ t : ℝ, (1 - (Real.cos (t * x) : ℂ)) / ((t : ℂ) ^ 2 - (I * r) ^ 2) =
      (((1 - Real.cos (t * x)) / (t ^ 2 + r ^ 2) : ℝ) : ℂ) := by
    intro t
    push_cast
    rw [mul_pow, I_sq]
    ring_nf
  simp_rw [hc, integral_complex_ofReal] at h
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have he : cexp (I * (I * r) * |x|) = ((Real.exp (-(r * |x|)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    linear_combination (r * |x| : ℂ) * I_sq
  rw [he] at h
  have h2 : ((Real.pi / (2 * r) * (1 - Real.exp (-(r * |x|))) : ℝ) : ℂ) =
      Real.pi * I / (2 * (I * r)) * (1 - ((Real.exp (-(r * |x|)) : ℝ) : ℂ)) := by
    push_cast
    field_simp
  exact_mod_cast h.trans h2.symm

theorem integrableOn_Ioi_one_sub_cos_div_sq_add_sq {r : ℝ} (hr : 0 < r) (x : ℝ) :
    IntegrableOn (fun t : ℝ => (1 - Real.cos (t * x)) / (t ^ 2 + r ^ 2)) (Ioi 0) := by
  have hw : 0 < (I * r).im := by simpa using hr
  have h := (integrableOn_Ioi_one_sub_cos_div_sq_sub_sq hw x).re
  refine IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
  have : (1 - (Real.cos (t * x) : ℂ)) / ((t : ℂ) ^ 2 - (I * r) ^ 2) =
      (((1 - Real.cos (t * x)) / (t ^ 2 + r ^ 2) : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, I_sq]
    ring_nf
  rw [this]
  exact Complex.ofReal_re _

end

end GaloisForLFunctions.HTGeometry
