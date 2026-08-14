import GaloisForLFunctions.HTGeometry.PolynomialExponentialDomination
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic
import GaloisForLFunctions.HTGeometry.VerticalContourShift
import GaloisForLFunctions.RHTower.BarnesMellinIntegrandBound

/-!
# Holomorphy and contour estimates for the Mellin integrand

The integrand `F(w) = x^{-w} ζ(-sw)(-π/sin(πw))` is holomorphic wherever `ζ(-sw)` and
`1/sin(πw)` are, that is off `w = -1/s` and off the integers.  On a vertical line missing those
points the exponential decay of the kernel makes `F` Bochner integrable, and on a horizontal
segment it makes the integral tend to zero as the height grows.  These are exactly the four side
conditions of a one-pole contour shift.
-/

open Complex Filter Set MeasureTheory

namespace RHTower

noncomputable section

/-- The integrand is holomorphic away from the zeta pole and the integers. -/
theorem differentiableAt_barnesIntegrand {s x : ℝ} (hx : 0 < x) {w : ℂ}
    (hζ : -(s : ℂ) * w ≠ 1) (hsin : Complex.sin ((Real.pi : ℂ) * w) ≠ 0) :
    DifferentiableAt ℂ (barnesIntegrand s x) w := by
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  have h1 : DifferentiableAt ℂ (fun v : ℂ => ((x : ℝ) : ℂ) ^ (-v)) w :=
    DifferentiableAt.const_cpow (differentiableAt_id.neg) (Or.inl hxne)
  have h2 : DifferentiableAt ℂ (fun v : ℂ => riemannZeta (-(s : ℂ) * v)) w := by
    have hz := (GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hζ).differentiableAt
    exact hz.comp w ((differentiableAt_id).const_mul (-(s : ℂ)))
  have h3 : DifferentiableAt ℂ
      (fun v : ℂ => -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * v))) w := by
    refine DifferentiableAt.neg ?_
    exact DifferentiableAt.div (differentiableAt_const _)
      ((Complex.differentiable_sin.comp (differentiable_id.const_mul _)).differentiableAt) hsin
  exact ((h1.mul h2).mul h3)

/-- Holomorphy on a punctured strip, provided the puncture is the strip's only singular point. -/
theorem holomorphicOn_barnesIntegrand {s x σ₀ σ₁ : ℝ} (hx : 0 < x) {p : ℂ}
    (hpoles : ∀ w : ℂ, w ∈ Icc σ₀ σ₁ ×ℂ (univ : Set ℝ) → w ≠ p →
      -(s : ℂ) * w ≠ 1 ∧ Complex.sin ((Real.pi : ℂ) * w) ≠ 0) :
    HolomorphicOn (barnesIntegrand s x) (Icc σ₀ σ₁ ×ℂ (univ : Set ℝ) \ {p}) := by
  intro w hw
  obtain ⟨hstrip, hne⟩ := hw
  have hne' : w ≠ p := hne
  obtain ⟨hζ, hsin⟩ := hpoles w hstrip hne'
  exact (differentiableAt_barnesIntegrand hx hζ hsin).differentiableWithinAt

/-- On a line missing the singularities the integrand is continuous. -/
theorem continuous_barnesIntegrand_vertical {s x σ : ℝ} (hx : 0 < x)
    (hζ : -(s : ℝ) * σ ≠ 1) (hsin : Real.sin (Real.pi * σ) ≠ 0) :
    Continuous fun t : ℝ => barnesIntegrand s x ((σ : ℂ) + (t : ℂ) * I) := by
  have hline : Continuous fun t : ℝ => ((σ : ℂ) + (t : ℂ) * I) := by
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  have him : ((σ : ℂ) + (t : ℂ) * I).im = t := by simp
  have hζ' : -(s : ℂ) * ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro hcon
    have hrepart := congrArg Complex.re hcon
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, Complex.one_re, hre, him] at hrepart
    exact hζ (by linear_combination hrepart)
  have hsin' : Complex.sin ((Real.pi : ℂ) * ((σ : ℂ) + (t : ℂ) * I)) ≠ 0 := by
    intro hcon
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hcon
    have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
    have hwk : ((σ : ℂ) + (t : ℂ) * I) = (k : ℂ) := by
      refine mul_left_cancel₀ hpi ?_
      rw [hk]
      ring
    have hσk : σ = (k : ℝ) := by
      have := congrArg Complex.re hwk
      rw [hre] at this
      simpa using this
    exact hsin (by rw [hσk, mul_comm]; exact Real.sin_int_mul_pi k)
  have hd := (differentiableAt_barnesIntegrand hx hζ' hsin').continuousAt
  exact ContinuousAt.comp (x := t) hd hline.continuousAt


/-! ### Contour estimates -/

theorem tendsto_inv_one_add_sq_atTop :
    Filter.Tendsto (fun y : ℝ => (1 + y ^ 2)⁻¹) atTop (nhds 0) := by
  have h : Filter.Tendsto (fun y : ℝ => 1 + y ^ 2) atTop atTop :=
    Filter.tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop (by norm_num))
  exact h.inv_tendsto_atTop

theorem tendsto_inv_one_add_sq_atBot :
    Filter.Tendsto (fun y : ℝ => (1 + y ^ 2)⁻¹) atBot (nhds 0) := by
  have h := tendsto_inv_one_add_sq_atTop.comp tendsto_neg_atBot_atTop
  exact Filter.Tendsto.congr (fun y => by simp) h

/-- The horizontal side of a rectangle, bounded by the strip estimate. -/
theorem eventually_norm_horizontal_le {s x σ₀ σ₁ : ℝ} (hs : 0 < s) (hx : 0 < x) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y : ℝ, 1 + 1 / s ≤ |y| →
      ‖∫ u in σ₀..σ₁, barnesIntegrand s x ((u : ℂ) + (y : ℂ) * I)‖
        ≤ (D * |σ₁ - σ₀|) * (1 + y ^ 2)⁻¹ := by
  obtain ⟨C, N, hC0, hC⟩ :=
    exists_bound_norm_barnesIntegrand hs hx (min σ₀ σ₁) (max σ₀ σ₁)
  refine ⟨C * Real.exp Real.pi * (((N + 2).factorial : ℝ) / Real.pi ^ (N + 2)), by positivity,
    fun y hy => ?_⟩
  have hbd : ∀ u ∈ Set.uIoc σ₀ σ₁,
      ‖barnesIntegrand s x ((u : ℂ) + (y : ℂ) * I)‖
        ≤ C * |y| ^ N * Real.exp (-(Real.pi * |y|)) := by
    intro u hu
    have hu' : u ∈ Set.uIcc σ₀ σ₁ := Set.uIoc_subset_uIcc hu
    rw [Set.uIcc_eq_union] at hu'
    have hmin : min σ₀ σ₁ ≤ u := by
      rcases hu' with h | h
      · exact le_trans (min_le_left _ _) h.1
      · exact le_trans (min_le_right _ _) h.1
    have hmax : u ≤ max σ₀ σ₁ := by
      rcases hu' with h | h
      · exact le_trans h.2 (le_max_right _ _)
      · exact le_trans h.2 (le_max_left _ _)
    exact hC u y hmin hmax hy
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  refine hint.trans ?_
  have hdom := GaloisForLFunctions.HTGeometry.polyExp_le_inv_one_add_sq hC0 Real.pi_pos N y
  calc C * |y| ^ N * Real.exp (-(Real.pi * |y|)) * |σ₁ - σ₀|
      ≤ (C * Real.exp Real.pi * (((N + 2).factorial : ℝ) / Real.pi ^ (N + 2)))
          * (1 + y ^ 2)⁻¹ * |σ₁ - σ₀| :=
        mul_le_mul_of_nonneg_right hdom (abs_nonneg _)
    _ = (C * Real.exp Real.pi * (((N + 2).factorial : ℝ) / Real.pi ^ (N + 2)) * |σ₁ - σ₀|)
          * (1 + y ^ 2)⁻¹ := by ring

/-- **The horizontal sides vanish.**  As the height grows the integral of the Mellin integrand
across a fixed abscissa range tends to zero. -/
theorem tendsto_horizontal_barnesIntegrand_atTop {s x σ₀ σ₁ : ℝ} (hs : 0 < s) (hx : 0 < x) :
    Filter.Tendsto (fun y : ℝ => ∫ u in σ₀..σ₁, barnesIntegrand s x ((u : ℂ) + (y : ℂ) * I))
      atTop (nhds 0) := by
  obtain ⟨D, hD0, hD⟩ := eventually_norm_horizontal_le (σ₀ := σ₀) (σ₁ := σ₁) hs hx
  have hg : Filter.Tendsto (fun y : ℝ => (D * |σ₁ - σ₀|) * (1 + y ^ 2)⁻¹) atTop (nhds 0) := by
    simpa using tendsto_inv_one_add_sq_atTop.const_mul (D * |σ₁ - σ₀|)
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [Filter.eventually_ge_atTop (1 + 1 / s)] with y hy
  have hs1 : (0 : ℝ) < 1 / s := by positivity
  have hy0 : (0 : ℝ) ≤ y := by linarith
  exact hD y (by rw [abs_of_nonneg hy0]; exact hy)

theorem tendsto_horizontal_barnesIntegrand_atBot {s x σ₀ σ₁ : ℝ} (hs : 0 < s) (hx : 0 < x) :
    Filter.Tendsto (fun y : ℝ => ∫ u in σ₀..σ₁, barnesIntegrand s x ((u : ℂ) + (y : ℂ) * I))
      atBot (nhds 0) := by
  obtain ⟨D, hD0, hD⟩ := eventually_norm_horizontal_le (σ₀ := σ₀) (σ₁ := σ₁) hs hx
  have hg : Filter.Tendsto (fun y : ℝ => (D * |σ₁ - σ₀|) * (1 + y ^ 2)⁻¹) atBot (nhds 0) := by
    simpa using tendsto_inv_one_add_sq_atBot.const_mul (D * |σ₁ - σ₀|)
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [Filter.eventually_le_atBot (-(1 + 1 / s))] with y hy
  refine hD y ?_
  have hs1 : (0 : ℝ) < 1 / s := by positivity
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- **The vertical line is integrable.**  Off the zeta pole and the integers the Mellin integrand is
Bochner integrable on every vertical line. -/
theorem integrable_barnesIntegrand_vertical {s x σ : ℝ} (hs : 0 < s) (hx : 0 < x)
    (hζ : -(s : ℝ) * σ ≠ 1) (hsin : Real.sin (Real.pi * σ) ≠ 0) :
    Integrable fun t : ℝ => barnesIntegrand s x ((σ : ℂ) + (t : ℂ) * I) := by
  classical
  set T : ℝ := 1 + 1 / s with hT
  have hT0 : 0 < T := by rw [hT]; positivity
  have hcont := continuous_barnesIntegrand_vertical hx hζ hsin
  obtain ⟨C, N, hC0, hC⟩ := exists_bound_norm_barnesIntegrand hs hx σ σ
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    hcont.continuousOn
  set K : ℝ := C * Real.exp Real.pi * (((N + 2).factorial : ℝ) / Real.pi ^ (N + 2)) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  set D : ℝ := max K (max C₂ 0 * (1 + T ^ 2)) with hD
  have hD0 : 0 ≤ D := le_trans hK0 (le_max_left _ _)
  refine MeasureTheory.Integrable.mono' (g := fun t : ℝ => D * (1 + t ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul D) hcont.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  have hden : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rcases le_or_gt T |t| with hbig | hsmall
  · have hb := hC σ t le_rfl le_rfl (by rw [← hT]; exact hbig)
    have hdom := GaloisForLFunctions.HTGeometry.polyExp_le_inv_one_add_sq hC0 Real.pi_pos N t
    refine hb.trans (hdom.trans ?_)
    rw [← hK]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hmem : t ∈ Set.Icc (-T) T := ⟨by
      have := abs_lt.mp hsmall
      linarith [this.1], by
      have := abs_lt.mp hsmall
      linarith [this.2]⟩
    have hb := hC₂ t hmem
    have hb' : ‖barnesIntegrand s x ((σ : ℂ) + (t : ℂ) * I)‖ ≤ max C₂ 0 :=
      hb.trans (le_max_left _ _)
    have hsq : 1 + t ^ 2 ≤ 1 + T ^ 2 := by
      have habs : |t| ≤ T := le_of_lt hsmall
      nlinarith [abs_nonneg t, sq_abs t]
    have hstep : max C₂ 0 ≤ D * (1 + t ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ hden]
      calc max C₂ 0 * (1 + t ^ 2) ≤ max C₂ 0 * (1 + T ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (le_max_right _ _)
        _ ≤ D := le_max_right _ _
    exact hb'.trans hstep

end

end RHTower
