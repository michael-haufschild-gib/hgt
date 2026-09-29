import GaloisForLFunctions.HTGeometry.StrelitzLogRadialDerivatives
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Calculus of the Euler logarithmic jets on circles

For an entire function `f` with Euler jets `u = z f'/f` and `v = z u'`:

* along the circle `θ ↦ r e^{iθ}` the first jet has derivative `i v`, so a bound `|v| ≤ ρ` on a
  zero-free circle keeps `u` within `3πρ` of its circle average;
* the circle average of `u` equals `(2πi)⁻¹ ∮ f'/f`, hence is constant across zero-free closed
  annuli;
* along logarithmic radii `log |f|` has derivative `Re u`, so two-sided bounds for `Re u` on an
  annulus integrate to two-sided bounds for the growth of `log |f|`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Complex Metric Set Filter Topology Real

variable {f : ℂ → ℂ}

/-- The Euler logarithmic derivative of an entire function is analytic off its zeros. -/
theorem analyticAt_eulerLogDeriv (hf : Differentiable ℂ f) {z : ℂ} (hfz : f z ≠ 0) :
    AnalyticAt ℂ (eulerLogDeriv f) z := by
  have hfa : AnalyticAt ℂ f z := hf.analyticAt z
  have h : AnalyticAt ℂ ((fun w => w * deriv f w) / f) z :=
    (analyticAt_id.mul hfa.deriv).div hfa hfz
  exact h

/-- The second Euler jet of an entire function is continuous off its zeros. -/
theorem continuousAt_eulerLogDerivSecond (hf : Differentiable ℂ f) {z : ℂ} (hfz : f z ≠ 0) :
    ContinuousAt (eulerLogDerivSecond f) z := by
  have h : AnalyticAt ℂ (fun w => w * deriv (eulerLogDeriv f) w) z :=
    analyticAt_id.mul (analyticAt_eulerLogDeriv hf hfz).deriv
  exact h.continuousAt

/-- Along a circle the first Euler jet has angular derivative `i v`. -/
theorem hasDerivAt_eulerLogDeriv_circleMap (hf : Differentiable ℂ f) {r θ : ℝ}
    (hfz : f (circleMap 0 r θ) ≠ 0) :
    HasDerivAt (fun t : ℝ => eulerLogDeriv f (circleMap 0 r t))
      (I * eulerLogDerivSecond f (circleMap 0 r θ)) θ := by
  have hu := (analyticAt_eulerLogDeriv hf hfz).differentiableAt.hasDerivAt
  have h := hu.comp θ (hasDerivAt_circleMap 0 r θ)
  convert h using 1
  done
  done

/-- **Angular oscillation.**  On a zero-free circle with `|v| ≤ ρ`, the first Euler jet stays
within `3πρ` of its circle average. -/
theorem norm_eulerLogDeriv_sub_circleAverage_le (hf : Differentiable ℂ f) {r ρ : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ)
    (hcirc : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0 ∧ ‖eulerLogDerivSecond f z‖ ≤ ρ)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) r) :
    ‖eulerLogDeriv f z - circleAverage (eulerLogDeriv f) 0 r‖ ≤ 3 * π * ρ := by
  set U : ℝ → ℂ := fun t => eulerLogDeriv f (circleMap 0 r t) with hU
  have hmem : ∀ t, circleMap 0 r t ∈ sphere (0 : ℂ) r := circleMap_mem_sphere 0 hr.le
  have hderiv : ∀ t, HasDerivAt U (I * eulerLogDerivSecond f (circleMap 0 r t)) t :=
    fun t => hasDerivAt_eulerLogDeriv_circleMap hf (hcirc _ (hmem t)).1
  have hbound : ∀ t, ‖I * eulerLogDerivSecond f (circleMap 0 r t)‖ ≤ ρ := fun t => by
    rw [norm_mul, Complex.norm_I, one_mul]
    exact (hcirc _ (hmem t)).2
  have hlip : ∀ s t : ℝ, ‖U s - U t‖ ≤ ρ * |s - t| := by
    intro s t
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := U) (s := univ)
      (fun x _ => (hderiv x).hasDerivWithinAt) (fun x _ => hbound x) convex_univ
      (mem_univ t) (mem_univ s)
    simpa [Real.norm_eq_abs] using h
  have hUcont : Continuous U :=
    continuous_iff_continuousAt.mpr fun t => (hderiv t).continuousAt
  have hint : IntervalIntegrable U MeasureTheory.volume 0 (2 * π) :=
    hUcont.intervalIntegrable _ _
  have hz' : U (arg z) = eulerLogDeriv f z := by
    have hnorm : ‖z‖ = r := by simpa using hz
    simp only [hU, circleMap, zero_add]
    rw [← hnorm, Complex.norm_mul_exp_arg_mul_I]
  have hpi : 0 < 2 * π := by positivity
  have hkey : eulerLogDeriv f z - circleAverage (eulerLogDeriv f) 0 r =
      (2 * π)⁻¹ • ∫ t in (0 : ℝ)..2 * π, (U (arg z) - U t) := by
    rw [circleAverage_def, intervalIntegral.integral_sub intervalIntegrable_const hint,
      intervalIntegral.integral_const, smul_sub, smul_smul, sub_zero,
      inv_mul_cancel₀ hpi.ne', one_smul, hz']
  rw [hkey, norm_smul]
  have hI : ‖∫ t in (0 : ℝ)..2 * π, (U (arg z) - U t)‖ ≤ (3 * π * ρ) * |2 * π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [Set.uIoc_of_le hpi.le] at ht
    refine (hlip _ _).trans ?_
    have h1 := Complex.neg_pi_lt_arg z
    have h2 := Complex.arg_le_pi z
    have habs : |arg z - t| ≤ 3 * π := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    calc ρ * |arg z - t| ≤ ρ * (3 * π) := mul_le_mul_of_nonneg_left habs hρ
      _ = 3 * π * ρ := by ring
  rw [sub_zero, abs_of_pos hpi] at hI
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos hpi]
  calc (2 * π)⁻¹ * ‖∫ t in (0 : ℝ)..2 * π, (U (arg z) - U t)‖
      ≤ (2 * π)⁻¹ * (3 * π * ρ * (2 * π)) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = 3 * π * ρ := by field_simp

/-- A pointwise bound for `u - N` on a zero-free circle bounds the circle average. -/
theorem norm_circleAverage_eulerLogDeriv_sub_le (hf : Differentiable ℂ f) {r δ : ℝ}
    (hr : 0 < r) {N : ℂ}
    (hcirc : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0 ∧ ‖eulerLogDeriv f z - N‖ ≤ δ) :
    ‖circleAverage (eulerLogDeriv f) 0 r - N‖ ≤ δ := by
  set U : ℝ → ℂ := fun t => eulerLogDeriv f (circleMap 0 r t) with hU
  have hmem : ∀ t, circleMap 0 r t ∈ sphere (0 : ℂ) r := circleMap_mem_sphere 0 hr.le
  have hUcont : Continuous U := continuous_iff_continuousAt.mpr fun t =>
    (analyticAt_eulerLogDeriv hf (hcirc _ (hmem t)).1).continuousAt.comp
      (continuous_circleMap 0 r).continuousAt
  have hint : IntervalIntegrable U MeasureTheory.volume 0 (2 * π) :=
    hUcont.intervalIntegrable _ _
  have hpi : 0 < 2 * π := by positivity
  have hkey : circleAverage (eulerLogDeriv f) 0 r - N =
      (2 * π)⁻¹ • ∫ t in (0 : ℝ)..2 * π, (U t - N) := by
    rw [circleAverage_def, intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const, smul_sub, smul_smul, sub_zero,
      inv_mul_cancel₀ hpi.ne', one_smul]
  rw [hkey, norm_smul]
  have hI : ‖∫ t in (0 : ℝ)..2 * π, (U t - N)‖ ≤ δ * |2 * π - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => (hcirc _ (hmem t)).2
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hcirc _ (hmem 0)).2
  rw [sub_zero, abs_of_pos hpi] at hI
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos hpi]
  calc (2 * π)⁻¹ * ‖∫ t in (0 : ℝ)..2 * π, (U t - N)‖
      ≤ (2 * π)⁻¹ * (δ * (2 * π)) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = δ := by field_simp

/-- **Annulus invariance.**  The circle average of `u` is constant across a zero-free closed
annulus, being the logarithmic-derivative contour integral `(2πi)⁻¹ ∮ f'/f`. -/
theorem circleAverage_eulerLogDeriv_eq_of_annulus (hf : Differentiable ℂ f) {r₁ r₂ : ℝ}
    (h₁ : 0 < r₁) (h₁₂ : r₁ ≤ r₂) (hne : ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ → f z ≠ 0) :
    circleAverage (eulerLogDeriv f) 0 r₁ = circleAverage (eulerLogDeriv f) 0 r₂ := by
  have h₂ : 0 < r₂ := h₁.trans_le h₁₂
  rw [circleAverage_eq_circleIntegral h₁.ne', circleAverage_eq_circleIntegral h₂.ne']
  simp only [sub_zero, smul_eq_mul]
  have hz0 : ∀ z : ℂ, r₁ ≤ ‖z‖ → z ≠ 0 := by
    intro z hz h
    rw [h, norm_zero] at hz
    linarith
  have hdiff : ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ →
      DifferentiableAt ℂ (fun w => w⁻¹ * eulerLogDeriv f w) z := by
    intro z hz1 hz2
    exact (differentiableAt_inv (hz0 z hz1)).mul
      (analyticAt_eulerLogDeriv hf (hne z hz1 hz2)).differentiableAt
  congr 1
  symm
  refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable h₁ h₁₂
    countable_empty ?_ ?_
  · intro z hz
    have hz1 : r₁ ≤ ‖z‖ := by
      have := hz.2
      simpa [mem_ball, dist_zero_right, not_lt] using this
    have hz2 : ‖z‖ ≤ r₂ := by simpa [mem_closedBall, dist_zero_right] using hz.1
    exact (hdiff z hz1 hz2).continuousAt.continuousWithinAt
  · intro z hz
    have hz' := hz.1
    have hz1 : r₁ ≤ ‖z‖ := by
      have := hz'.2
      simp only [mem_closedBall, dist_zero_right, not_le] at this
      exact this.le
    have hz2 : ‖z‖ ≤ r₂ := by
      have := hz'.1
      simp only [mem_ball, dist_zero_right] at this
      exact this.le
    exact hdiff z hz1 hz2

/-- An open set containing a circle contains a whole open annulus around it. -/
theorem exists_pos_forall_mem_of_sphere_subset {O : Set ℂ} (hO : IsOpen O) {R : ℝ}
    (hR : 0 < R) (hsub : sphere (0 : ℂ) R ⊆ O) :
    ∃ δ > 0, ∀ z : ℂ, |‖z‖ - R| < δ → z ∈ O := by
  obtain ⟨δ, hδ, hthick⟩ :=
    (isCompact_sphere (0 : ℂ) R).exists_thickening_subset_open hO hsub
  refine ⟨min δ R, lt_min hδ hR, fun z hz => hthick ?_⟩
  have hzR : |‖z‖ - R| < R := lt_of_lt_of_le hz (min_le_right _ _)
  have hz0 : 0 < ‖z‖ := by
    by_contra h
    push Not at h
    have h0 : ‖z‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [h0, zero_sub, abs_neg, abs_of_pos hR] at hzR
    exact lt_irrefl _ hzR
  rw [Metric.mem_thickening_iff]
  refine ⟨((R / ‖z‖ : ℝ) : ℂ) * z, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    field_simp
  · rw [dist_eq_norm]
    have hsplit : z - ((R / ‖z‖ : ℝ) : ℂ) * z = ((1 - R / ‖z‖ : ℝ) : ℂ) * z := by
      push_cast
      ring
    rw [hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have habs : |1 - R / ‖z‖| * ‖z‖ = |‖z‖ - R| := by
      calc |1 - R / ‖z‖| * ‖z‖ = |(1 - R / ‖z‖) * ‖z‖| := by
            rw [abs_mul, abs_of_pos hz0]
        _ = |‖z‖ - R| := by
            congr 1
            field_simp
    rw [habs]
    exact lt_of_lt_of_le hz (min_le_left _ _)

/-- Near a zero-free circle the circle average of `u` is locally constant in the radius. -/
theorem exists_pos_circleAverage_eulerLogDeriv_eq (hf : Differentiable ℂ f) {R : ℝ}
    (hR : 0 < R) (hne : ∀ z ∈ sphere (0 : ℂ) R, f z ≠ 0) :
    ∃ δ > 0, ∀ y : ℝ, |y - R| < δ → 0 < y ∧
      circleAverage (eulerLogDeriv f) 0 y = circleAverage (eulerLogDeriv f) 0 R := by
  have hO : IsOpen {z : ℂ | f z ≠ 0} := isOpen_ne_fun hf.continuous continuous_const
  obtain ⟨δ, hδ, hann⟩ := exists_pos_forall_mem_of_sphere_subset hO hR hne
  refine ⟨min δ R, lt_min hδ hR, fun y hy => ?_⟩
  have hyδ : |y - R| < δ := lt_of_lt_of_le hy (min_le_left _ _)
  have hyR : |y - R| < R := lt_of_lt_of_le hy (min_le_right _ _)
  have hy0 : 0 < y := by
    rw [abs_lt] at hyR
    linarith
  refine ⟨hy0, ?_⟩
  rcases le_total y R with hle | hle
  · refine circleAverage_eulerLogDeriv_eq_of_annulus hf hy0 hle fun z hz1 hz2 => hann z ?_
    rw [abs_lt] at hyδ ⊢
    constructor <;> linarith
  · refine (circleAverage_eulerLogDeriv_eq_of_annulus hf hR hle fun z hz1 hz2 => hann z ?_).symm
    rw [abs_lt] at hyδ ⊢
    constructor <;> linarith

/-- **Radial growth.**  Two-sided bounds `c₁ ≤ Re u ≤ c₂` on a zero-free closed annulus
`R ≤ |z| ≤ r` integrate along the logarithmic radius to two-sided bounds for the growth of
`log |f|`. -/
theorem log_norm_radial_sub_bounds (hf : Differentiable ℂ f) {R r c₁ c₂ : ℝ} (hR : 0 < R)
    (hRr : R ≤ r) {w : ℂ} (hw : ‖w‖ = R)
    (hann : ∀ z : ℂ, R ≤ ‖z‖ → ‖z‖ ≤ r →
      f z ≠ 0 ∧ c₁ ≤ (eulerLogDeriv f z).re ∧ (eulerLogDeriv f z).re ≤ c₂) :
    c₁ * (Real.log r - Real.log R) ≤
        Real.log ‖f (((r / R : ℝ) : ℂ) * w)‖ - Real.log ‖f w‖ ∧
      Real.log ‖f (((r / R : ℝ) : ℂ) * w)‖ - Real.log ‖f w‖ ≤
        c₂ * (Real.log r - Real.log R) := by
  have hr : 0 < r := hR.trans_le hRr
  set p : ℝ → ℂ := logRadialPath (Real.log R) w with hp
  have hpnorm : ∀ t, ‖p t‖ = Real.exp t := by
    intro t
    simp only [hp, logRadialPath, norm_mul, hw]
    rw [← Complex.ofReal_sub, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Real.exp_sub, Real.exp_log hR]
    field_simp
  set D : Set ℝ := Icc (Real.log R) (Real.log r) with hD
  have hlog : Real.log R ≤ Real.log r := Real.log_le_log hR hRr
  have hmemD : ∀ t ∈ D, R ≤ ‖p t‖ ∧ ‖p t‖ ≤ r := by
    intro t ht
    rw [hpnorm]
    constructor
    · calc R = Real.exp (Real.log R) := (Real.exp_log hR).symm
        _ ≤ Real.exp t := Real.exp_le_exp.mpr ht.1
    · calc Real.exp t ≤ Real.exp (Real.log r) := Real.exp_le_exp.mpr ht.2
        _ = r := Real.exp_log hr
  have hpath : ∀ t, logRadialPath t (p t) = p := by
    intro t
    funext s
    simp only [hp, logRadialPath]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  set g : ℝ → ℝ := fun t => Real.log ‖f (p t)‖ with hg
  have hderiv : ∀ t ∈ D, HasDerivAt g (eulerLogDeriv f (p t)).re t := by
    intro t ht
    have h := hasDerivAt_log_norm_logRadialPath (f := f) (x := t) (z := p t)
      (hf (p t)) (hann _ (hmemD t ht).1 (hmemD t ht).2).1
    rw [hpath t] at h
    exact h
  have hcont : ContinuousOn g D := fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ g (interior D) := fun t ht =>
    (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hderiv_eq : ∀ t ∈ interior D, deriv g t = (eulerLogDeriv f (p t)).re :=
    fun t ht => (hderiv t (interior_subset ht)).deriv
  have hbd : ∀ t ∈ interior D,
      c₁ ≤ (eulerLogDeriv f (p t)).re ∧ (eulerLogDeriv f (p t)).re ≤ c₂ := fun t ht =>
    (hann _ (hmemD t (interior_subset ht)).1 (hmemD t (interior_subset ht)).2).2
  have hlo := (convex_Icc (Real.log R) (Real.log r)).mul_sub_le_image_sub_of_le_deriv hcont
    hdiff (C := c₁) (fun t ht => by rw [hderiv_eq t ht]; exact (hbd t ht).1)
    (Real.log R) (left_mem_Icc.mpr hlog) (Real.log r) (right_mem_Icc.mpr hlog) hlog
  have hhi := (convex_Icc (Real.log R) (Real.log r)).image_sub_le_mul_sub_of_deriv_le hcont
    hdiff (C := c₂) (fun t ht => by rw [hderiv_eq t ht]; exact (hbd t ht).2)
    (Real.log R) (left_mem_Icc.mpr hlog) (Real.log r) (right_mem_Icc.mpr hlog) hlog
  have hgR : g (Real.log R) = Real.log ‖f w‖ := by
    simp [hg, hp, logRadialPath]
  have hgr : g (Real.log r) = Real.log ‖f (((r / R : ℝ) : ℂ) * w)‖ := by
    simp only [hg, hp, logRadialPath]
    rw [← Complex.ofReal_sub, ← Complex.ofReal_exp, Real.exp_sub, Real.exp_log hr,
      Real.exp_log hR]
  rw [hgR, hgr] at hlo hhi
  exact ⟨hlo, hhi⟩

end

end GaloisForLFunctions.HTGeometry
