import GaloisForLFunctions.HTGeometry.CauchyTransformOpenUniqueness

/-!
# A density with vanishing Cauchy transform on both half-planes is zero

If an integrable complex density against a finite measure on the line has vanishing Cauchy transform
on a nonempty open subset of each half-plane, the density vanishes almost everywhere.  Vanishing on
one half-plane alone is not enough: the density `(τ − i)⁻²` against Lebesgue measure has a Cauchy
transform vanishing throughout the upper half-plane.

The proof conjugates the lower-half-plane vanishing to reduce to a *real* density, and then splits
the real density into its positive and negative parts, whose Cauchy transforms coincide on the whole
upper half-plane; the uniqueness theorem for finite measures finishes.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex Filter Set Topology

open scoped ENNReal

noncomputable section

/-- The open lower half-plane. -/
def lowerHalfPlaneSet : Set ℂ := {z : ℂ | z.im < 0}

theorem isOpen_lowerHalfPlaneSet : IsOpen lowerHalfPlaneSet :=
  isOpen_lt Complex.continuous_im continuous_const

theorem isPreconnected_lowerHalfPlaneSet : IsPreconnected lowerHalfPlaneSet := by
  refine Convex.isPreconnected ?_
  intro x hx y hy a b ha hb hab
  have hx' : x.im < 0 := hx
  have hy' : y.im < 0 := hy
  show (a • x + b • y).im < 0
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · have hb0 : 0 < b := by
      rcases eq_or_lt_of_le hb with hb0 | hb0
      · exfalso
        rw [← ha0, ← hb0] at hab
        norm_num at hab
      · exact hb0
    rw [← ha0]
    have := mul_neg_of_pos_of_neg hb0 hy'
    simpa using this
  · have h1 := mul_neg_of_pos_of_neg ha0 hx'
    have h2 : b * y.im ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hy'.le
    linarith

/-- The resolvent transform of a finite real measure is analytic off the real axis. -/
theorem analyticOnNhd_resolventTransform_offReal (mu : Measure ℝ) [IsFiniteMeasure mu] {S : Set ℂ}
    (hSopen : IsOpen S) (hS : ∀ z ∈ S, z.im ≠ 0) :
    AnalyticOnNhd ℂ (resolventTransform mu) S := by
  have hsub : S ⊆ (algebraMap ℝ ℂ '' mu.support)ᶜ := by
    rintro z hz ⟨x, -, hx⟩
    have : z.im = 0 := by
      rw [← hx]
      simp
    exact hS z hz this
  have hA0 : AnalyticOn ℂ (resolventTransform mu) (algebraMap ℝ ℂ '' mu.support)ᶜ :=
    MeasureTheory.analyticOn_resolventTransform
  exact (hSopen.analyticOn_iff_analyticOnNhd).1 (hA0.mono hsub)

/-- The Cauchy transform of an integrable density against a finite measure. -/
def densityCauchyTransform (nu : Measure ℝ) (g : ℝ → ℂ) (w : ℂ) : ℂ :=
  ∫ τ : ℝ, g τ * ((τ : ℂ) - w)⁻¹ ∂nu

/-- The Cauchy kernel is bounded off the real axis. -/
theorem norm_cauchyKernel_le {w : ℂ} (hw : w.im ≠ 0) (τ : ℝ) :
    ‖((τ : ℂ) - w)⁻¹‖ ≤ |w.im|⁻¹ := by
  have hne : ((τ : ℂ) - w) ≠ 0 := by
    intro h
    have : ((τ : ℂ) - w).im = 0 := by rw [h]; simp
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_eq_zero] at this
    exact hw this
  rw [norm_inv]
  have h1 : |((τ : ℂ) - w).im| ≤ ‖(τ : ℂ) - w‖ := Complex.abs_im_le_norm _
  have h2 : |w.im| ≤ ‖(τ : ℂ) - w‖ := by
    simpa using h1
  exact inv_anti₀ (abs_pos.2 hw) h2

/-- Integrability of a dominated density against the Cauchy kernel. -/
theorem integrable_density_mul_cauchyKernel (nu : Measure ℝ) [IsFiniteMeasure nu] {p : ℝ → ℂ}
    (hpmeas : Measurable p) {h : ℝ → ℝ} (hint : Integrable h nu)
    (hbound : ∀ τ, ‖p τ‖ ≤ |h τ|) {w : ℂ} (hw : w.im ≠ 0) :
    Integrable (fun τ : ℝ => p τ * ((τ : ℂ) - w)⁻¹) nu := by
  have hker : Measurable fun τ : ℝ => ((τ : ℂ) - w)⁻¹ := by fun_prop
  refine Integrable.mono' (g := fun τ => |h τ| * |w.im|⁻¹) (hint.abs.mul_const _)
    (hpmeas.mul hker).aestronglyMeasurable ?_
  filter_upwards with τ
  calc ‖p τ * ((τ : ℂ) - w)⁻¹‖ = ‖p τ‖ * ‖((τ : ℂ) - w)⁻¹‖ := norm_mul _ _
    _ ≤ |h τ| * |w.im|⁻¹ :=
        mul_le_mul (hbound τ) (norm_cauchyKernel_le hw τ) (norm_nonneg _) (abs_nonneg _)

/-- The transform of a nonnegative real density is the resolvent transform of the weighted
measure. -/
theorem resolventTransform_withDensity_ofReal (nu : Measure ℝ) [IsFiniteMeasure nu] {h : ℝ → ℝ}
    (hmeas : Measurable h) (w : ℂ) :
    resolventTransform (nu.withDensity fun τ => ENNReal.ofReal (h τ)) w =
      ∫ τ : ℝ, ((ENNReal.ofReal (h τ)).toReal : ℂ) * ((τ : ℂ) - w)⁻¹ ∂nu := by
  rw [resolventTransform_eq_cauchy,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  show (ENNReal.ofReal (h τ)).toReal • ((τ : ℂ) - w)⁻¹ =
    ((ENNReal.ofReal (h τ)).toReal : ℂ) * ((τ : ℂ) - w)⁻¹
  rw [Complex.real_smul]

/-- Splitting a real number into the difference of the truncations of `h` and `-h`. -/
theorem toReal_ofReal_sub_toReal_ofReal_neg (r : ℝ) :
    (ENNReal.ofReal r).toReal - (ENNReal.ofReal (-r)).toReal = r := by
  rcases le_total 0 r with hpos | hneg
  · rw [ENNReal.toReal_ofReal hpos, ENNReal.ofReal_of_nonpos (by linarith)]
    simp
  · rw [ENNReal.ofReal_of_nonpos hneg, ENNReal.toReal_ofReal (by linarith)]
    simp

/-- Bounds for the two truncations. -/
theorem abs_toReal_ofReal_le (r : ℝ) : |(ENNReal.ofReal r).toReal| ≤ |r| := by
  rcases le_total 0 r with hpos | hneg
  · rw [ENNReal.toReal_ofReal hpos]
  · rw [ENNReal.ofReal_of_nonpos hneg]
    simp [abs_nonneg]

/-- **The real case.**  A real integrable density whose Cauchy transform vanishes on the whole upper
half-plane vanishes almost everywhere. -/
theorem real_density_eq_zero_of_transform_eq_zero_upper (nu : Measure ℝ) [IsFiniteMeasure nu]
    {h : ℝ → ℝ} (hmeas : Measurable h) (hint : Integrable h nu)
    (hzero : ∀ w ∈ upperHalfPlaneSet, densityCauchyTransform nu (fun τ => (h τ : ℂ)) w = 0) :
    h =ᵐ[nu] 0 := by
  set f₁ : ℝ → ℝ≥0∞ := fun τ => ENNReal.ofReal (h τ) with hf₁
  set f₂ : ℝ → ℝ≥0∞ := fun τ => ENNReal.ofReal (-h τ) with hf₂
  have hf₁meas : Measurable f₁ := by fun_prop
  have hf₂meas : Measurable f₂ := by fun_prop
  have hlint₁ : ∫⁻ τ, f₁ τ ∂nu ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun τ => ?_) hint.hasFiniteIntegral)
    rw [hf₁, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hlint₂ : ∫⁻ τ, f₂ τ ∂nu ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun τ => ?_) hint.hasFiniteIntegral)
    rw [hf₂, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
  haveI : IsFiniteMeasure (nu.withDensity f₁) := isFiniteMeasure_withDensity hlint₁
  haveI : IsFiniteMeasure (nu.withDensity f₂) := isFiniteMeasure_withDensity hlint₂
  have heqOn : EqOn (resolventTransform (nu.withDensity f₁))
      (resolventTransform (nu.withDensity f₂)) upperHalfPlaneSet := by
    intro w hw
    have hwim : w.im ≠ 0 := ne_of_gt hw
    have hint₁ : Integrable (fun τ : ℝ => ((f₁ τ).toReal : ℂ) * ((τ : ℂ) - w)⁻¹) nu :=
      integrable_density_mul_cauchyKernel nu
        (by fun_prop) hint (fun τ => by
          simpa [Complex.norm_real, Real.norm_eq_abs] using abs_toReal_ofReal_le (h τ)) hwim
    have hint₂ : Integrable (fun τ : ℝ => ((f₂ τ).toReal : ℂ) * ((τ : ℂ) - w)⁻¹) nu :=
      integrable_density_mul_cauchyKernel nu
        (by fun_prop) hint (fun τ => by
          simpa [Complex.norm_real, Real.norm_eq_abs, abs_neg] using
            abs_toReal_ofReal_le (-h τ)) hwim
    have hdiff : (∫ τ : ℝ, ((f₁ τ).toReal : ℂ) * ((τ : ℂ) - w)⁻¹ ∂nu) -
        (∫ τ : ℝ, ((f₂ τ).toReal : ℂ) * ((τ : ℂ) - w)⁻¹ ∂nu) =
        densityCauchyTransform nu (fun τ => (h τ : ℂ)) w := by
      rw [← integral_sub hint₁ hint₂]
      refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
      show ((f₁ τ).toReal : ℂ) * ((τ : ℂ) - w)⁻¹ - ((f₂ τ).toReal : ℂ) * ((τ : ℂ) - w)⁻¹ =
        (h τ : ℂ) * ((τ : ℂ) - w)⁻¹
      rw [← sub_mul]
      congr 1
      rw [← Complex.ofReal_sub, toReal_ofReal_sub_toReal_ofReal_neg]
    have hzeroW := hzero w hw
    rw [resolventTransform_withDensity_ofReal nu hmeas w,
      resolventTransform_withDensity_ofReal (h := fun τ => -h τ) nu (hmeas.neg) w]
    have hz0 := hdiff
    rw [hzeroW] at hz0
    exact sub_eq_zero.1 hz0
  have hmeasEq : nu.withDensity f₁ = nu.withDensity f₂ :=
    measure_eq_of_resolventTransform_eqOn_open _ _ isOpen_upperHalfPlaneSet
      (show Complex.I ∈ upperHalfPlaneSet by simp [upperHalfPlaneSet]) (subset_refl _) heqOn
  have hae := (withDensity_eq_iff hf₁meas.aemeasurable hf₂meas.aemeasurable hlint₁).1 hmeasEq
  filter_upwards [hae] with τ hτ
  have h1 : (f₁ τ).toReal - (f₂ τ).toReal = h τ := toReal_ofReal_sub_toReal_ofReal_neg (h τ)
  rw [hτ] at h1
  simpa using h1.symm

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex Filter Set Topology

open scoped ENNReal

noncomputable section

variable {nu : Measure ℝ}

/-- The four nonnegative truncations of an integrable complex density are integrable weights. -/
theorem lintegral_ofReal_component_ne_top [IsFiniteMeasure nu] {g : ℝ → ℂ}
    (hint : Integrable g nu) (c : ℝ → ℝ) (hc : ∀ τ, |c τ| ≤ ‖g τ‖) :
    ∫⁻ τ, ENNReal.ofReal (c τ) ∂nu ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun τ => ?_) hint.hasFiniteIntegral)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (le_trans (le_abs_self _) (hc τ))

/-- The Cauchy transform of an integrable complex density is a combination of four resolvent
transforms. -/
theorem densityCauchyTransform_eq_combination [IsFiniteMeasure nu] {g : ℝ → ℂ}
    (hmeas : Measurable g) (hint : Integrable g nu) {w : ℂ} (hw : w.im ≠ 0) :
    densityCauchyTransform nu g w =
      (resolventTransform (nu.withDensity fun τ => ENNReal.ofReal ((g τ).re)) w -
          resolventTransform (nu.withDensity fun τ => ENNReal.ofReal (-(g τ).re)) w) +
        Complex.I * (resolventTransform (nu.withDensity fun τ => ENNReal.ofReal ((g τ).im)) w -
          resolventTransform (nu.withDensity fun τ => ENNReal.ofReal (-(g τ).im)) w) := by
  have hre : Integrable (fun τ : ℝ => (g τ).re) nu := hint.re
  have him : Integrable (fun τ : ℝ => (g τ).im) nu := hint.im
  have hint₁ : Integrable (fun τ : ℝ =>
      ((ENNReal.ofReal ((g τ).re)).toReal : ℂ) * ((τ : ℂ) - w)⁻¹) nu :=
    integrable_density_mul_cauchyKernel nu (by fun_prop) hre
      (fun τ => by simpa [Complex.norm_real, Real.norm_eq_abs] using
        abs_toReal_ofReal_le ((g τ).re)) hw
  have hint₂ : Integrable (fun τ : ℝ =>
      ((ENNReal.ofReal (-(g τ).re)).toReal : ℂ) * ((τ : ℂ) - w)⁻¹) nu :=
    integrable_density_mul_cauchyKernel nu (by fun_prop) hre
      (fun τ => by simpa [Complex.norm_real, Real.norm_eq_abs, abs_neg] using
        abs_toReal_ofReal_le (-(g τ).re)) hw
  have hint₃ : Integrable (fun τ : ℝ =>
      ((ENNReal.ofReal ((g τ).im)).toReal : ℂ) * ((τ : ℂ) - w)⁻¹) nu :=
    integrable_density_mul_cauchyKernel nu (by fun_prop) him
      (fun τ => by simpa [Complex.norm_real, Real.norm_eq_abs] using
        abs_toReal_ofReal_le ((g τ).im)) hw
  have hint₄ : Integrable (fun τ : ℝ =>
      ((ENNReal.ofReal (-(g τ).im)).toReal : ℂ) * ((τ : ℂ) - w)⁻¹) nu :=
    integrable_density_mul_cauchyKernel nu (by fun_prop) him
      (fun τ => by simpa [Complex.norm_real, Real.norm_eq_abs, abs_neg] using
        abs_toReal_ofReal_le (-(g τ).im)) hw
  rw [resolventTransform_withDensity_ofReal (h := fun τ => (g τ).re) nu (by fun_prop) w,
    resolventTransform_withDensity_ofReal (h := fun τ => -(g τ).re) nu (by fun_prop) w,
    resolventTransform_withDensity_ofReal (h := fun τ => (g τ).im) nu (by fun_prop) w,
    resolventTransform_withDensity_ofReal (h := fun τ => -(g τ).im) nu (by fun_prop) w,
    ← integral_sub hint₁ hint₂, ← integral_sub hint₃ hint₄, ← integral_const_mul]
  have hAB : Integrable (fun τ : ℝ =>
      ((ENNReal.ofReal ((g τ).re)).toReal : ℂ) * ((τ : ℂ) - w)⁻¹ -
        ((ENNReal.ofReal (-(g τ).re)).toReal : ℂ) * ((τ : ℂ) - w)⁻¹) nu := hint₁.sub hint₂
  have hCD : Integrable (fun τ : ℝ => Complex.I *
      (((ENNReal.ofReal ((g τ).im)).toReal : ℂ) * ((τ : ℂ) - w)⁻¹ -
        ((ENNReal.ofReal (-(g τ).im)).toReal : ℂ) * ((τ : ℂ) - w)⁻¹)) nu :=
    (hint₃.sub hint₄).const_mul _
  rw [← integral_add hAB hCD]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  show g τ * ((τ : ℂ) - w)⁻¹ =
    (((ENNReal.ofReal ((g τ).re)).toReal : ℂ) * ((τ : ℂ) - w)⁻¹ -
        ((ENNReal.ofReal (-(g τ).re)).toReal : ℂ) * ((τ : ℂ) - w)⁻¹) +
      Complex.I * (((ENNReal.ofReal ((g τ).im)).toReal : ℂ) * ((τ : ℂ) - w)⁻¹ -
        ((ENNReal.ofReal (-(g τ).im)).toReal : ℂ) * ((τ : ℂ) - w)⁻¹)
  have hr : ((ENNReal.ofReal ((g τ).re)).toReal : ℂ) -
      ((ENNReal.ofReal (-(g τ).re)).toReal : ℂ) = ((g τ).re : ℂ) := by
    rw [← Complex.ofReal_sub, toReal_ofReal_sub_toReal_ofReal_neg]
  have hi : ((ENNReal.ofReal ((g τ).im)).toReal : ℂ) -
      ((ENNReal.ofReal (-(g τ).im)).toReal : ℂ) = ((g τ).im : ℂ) := by
    rw [← Complex.ofReal_sub, toReal_ofReal_sub_toReal_ofReal_neg]
  have hsplit : ((g τ).re : ℂ) + Complex.I * ((g τ).im : ℂ) = g τ := by
    rw [mul_comm]
    exact Complex.re_add_im (g τ)
  rw [← sub_mul, ← sub_mul, hr, hi]
  linear_combination (-(((τ : ℂ) - w)⁻¹)) * hsplit

/-- The Cauchy transform of an integrable complex density is analytic off the real axis. -/
theorem analyticOnNhd_densityCauchyTransform [IsFiniteMeasure nu] {g : ℝ → ℂ}
    (hmeas : Measurable g) (hint : Integrable g nu) {S : Set ℂ}
    (hSopen : IsOpen S) (hS : ∀ z ∈ S, z.im ≠ 0) :
    AnalyticOnNhd ℂ (densityCauchyTransform nu g) S := by
  haveI h₁ : IsFiniteMeasure (nu.withDensity fun τ => ENNReal.ofReal ((g τ).re)) :=
    isFiniteMeasure_withDensity (lintegral_ofReal_component_ne_top hint _
      fun τ => Complex.abs_re_le_norm _)
  haveI h₂ : IsFiniteMeasure (nu.withDensity fun τ => ENNReal.ofReal (-(g τ).re)) :=
    isFiniteMeasure_withDensity (lintegral_ofReal_component_ne_top hint _
      fun τ => by simpa [abs_neg] using Complex.abs_re_le_norm (g τ))
  haveI h₃ : IsFiniteMeasure (nu.withDensity fun τ => ENNReal.ofReal ((g τ).im)) :=
    isFiniteMeasure_withDensity (lintegral_ofReal_component_ne_top hint _
      fun τ => Complex.abs_im_le_norm _)
  haveI h₄ : IsFiniteMeasure (nu.withDensity fun τ => ENNReal.ofReal (-(g τ).im)) :=
    isFiniteMeasure_withDensity (lintegral_ofReal_component_ne_top hint _
      fun τ => by simpa [abs_neg] using Complex.abs_im_le_norm (g τ))
  have hcomb : AnalyticOnNhd ℂ (fun w =>
      (resolventTransform (nu.withDensity fun τ => ENNReal.ofReal ((g τ).re)) w -
          resolventTransform (nu.withDensity fun τ => ENNReal.ofReal (-(g τ).re)) w) +
        Complex.I * (resolventTransform (nu.withDensity fun τ => ENNReal.ofReal ((g τ).im)) w -
          resolventTransform (nu.withDensity fun τ => ENNReal.ofReal (-(g τ).im)) w)) S :=
    ((analyticOnNhd_resolventTransform_offReal _ hSopen hS).sub
        (analyticOnNhd_resolventTransform_offReal _ hSopen hS)).add
      (analyticOnNhd_const.mul
        ((analyticOnNhd_resolventTransform_offReal _ hSopen hS).sub
          (analyticOnNhd_resolventTransform_offReal _ hSopen hS)))
  refine hcomb.congr hSopen ?_
  intro w hw
  exact (densityCauchyTransform_eq_combination hmeas hint (hS w hw)).symm

/-- Conjugating the density conjugates the transform through the conjugate point. -/
theorem densityCauchyTransform_conj {g : ℝ → ℂ} (w : ℂ) :
    densityCauchyTransform nu (fun τ => (starRingEnd ℂ) (g τ)) w =
      (starRingEnd ℂ) (densityCauchyTransform nu g ((starRingEnd ℂ) w)) := by
  rw [densityCauchyTransform, densityCauchyTransform, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  show (starRingEnd ℂ) (g τ) * ((τ : ℂ) - w)⁻¹ =
    (starRingEnd ℂ) (g τ * ((τ : ℂ) - (starRingEnd ℂ) w)⁻¹)
  rw [map_mul, map_inv₀, map_sub, Complex.conj_ofReal, Complex.conj_conj]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex Filter Set Topology

open scoped ENNReal

noncomputable section

variable {nu : Measure ℝ}

/-- The transform of an integrable density is defined by an integrable integrand off the real
axis. -/
theorem integrable_density_kernel [IsFiniteMeasure nu] {g : ℝ → ℂ} (hmeas : Measurable g)
    (hint : Integrable g nu) {w : ℂ} (hw : w.im ≠ 0) :
    Integrable (fun τ : ℝ => g τ * ((τ : ℂ) - w)⁻¹) nu :=
  integrable_density_mul_cauchyKernel nu hmeas hint.norm
    (fun τ => by rw [abs_of_nonneg (norm_nonneg _)]) hw

/-- **Vanishing on both half-planes forces the density to vanish.** -/
theorem density_eq_zero_of_transform_eq_zero_both [IsFiniteMeasure nu] {g : ℝ → ℂ}
    (hmeas : Measurable g) (hint : Integrable g nu)
    {Vup Vlow : Set ℂ} (hVup : IsOpen Vup) (hVlow : IsOpen Vlow) {zup zlow : ℂ}
    (hzup : zup ∈ Vup) (hzlow : zlow ∈ Vlow)
    (hsubup : Vup ⊆ upperHalfPlaneSet) (hsublow : Vlow ⊆ lowerHalfPlaneSet)
    (hzeroup : ∀ w ∈ Vup, densityCauchyTransform nu g w = 0)
    (hzerolow : ∀ w ∈ Vlow, densityCauchyTransform nu g w = 0) :
    g =ᵐ[nu] 0 := by
  have hconjmeas : Measurable fun τ : ℝ => (starRingEnd ℂ) (g τ) := by fun_prop
  have hconjint : Integrable (fun τ : ℝ => (starRingEnd ℂ) (g τ)) nu := by
    refine Integrable.mono' hint.norm hconjmeas.aestronglyMeasurable ?_
    filter_upwards with τ
    simp
  have hupper : ∀ w ∈ upperHalfPlaneSet, densityCauchyTransform nu g w = 0 := by
    have hid := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_densityCauchyTransform hmeas hint isOpen_upperHalfPlaneSet
        (fun z hz => ne_of_gt hz))
      (analyticOnNhd_const (E := ℂ) (F := ℂ) (v := (0 : ℂ)) (s := upperHalfPlaneSet))
      isPreconnected_upperHalfPlaneSet (hsubup hzup)
      (by filter_upwards [hVup.mem_nhds hzup] with z hz using hzeroup z hz)
    exact fun w hw => hid hw
  have hlower : ∀ w ∈ lowerHalfPlaneSet, densityCauchyTransform nu g w = 0 := by
    have hid := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_densityCauchyTransform hmeas hint isOpen_lowerHalfPlaneSet
        (fun z hz => ne_of_lt hz))
      (analyticOnNhd_const (E := ℂ) (F := ℂ) (v := (0 : ℂ)) (s := lowerHalfPlaneSet))
      isPreconnected_lowerHalfPlaneSet (hsublow hzlow)
      (by filter_upwards [hVlow.mem_nhds hzlow] with z hz using hzerolow z hz)
    exact fun w hw => hid hw
  have hupperConj : ∀ w ∈ upperHalfPlaneSet,
      densityCauchyTransform nu (fun τ => (starRingEnd ℂ) (g τ)) w = 0 := by
    intro w hw
    have hpos : (0 : ℝ) < w.im := hw
    have hmem : (starRingEnd ℂ) w ∈ lowerHalfPlaneSet := by
      show ((starRingEnd ℂ) w).im < 0
      simpa using hpos
    rw [densityCauchyTransform_conj, hlower _ hmem, map_zero]
  have hsumzero : ∀ w ∈ upperHalfPlaneSet,
      ∫ τ : ℝ, (g τ * ((τ : ℂ) - w)⁻¹ + (starRingEnd ℂ) (g τ) * ((τ : ℂ) - w)⁻¹) ∂nu = 0 := by
    intro w hw
    have hwim : w.im ≠ 0 := ne_of_gt hw
    rw [integral_add (integrable_density_kernel hmeas hint hwim)
      (integrable_density_kernel hconjmeas hconjint hwim)]
    rw [show ∫ τ : ℝ, g τ * ((τ : ℂ) - w)⁻¹ ∂nu = densityCauchyTransform nu g w from rfl,
      show ∫ τ : ℝ, (starRingEnd ℂ) (g τ) * ((τ : ℂ) - w)⁻¹ ∂nu
        = densityCauchyTransform nu (fun τ => (starRingEnd ℂ) (g τ)) w from rfl,
      hupper w hw, hupperConj w hw, add_zero]
  have hdiffzero : ∀ w ∈ upperHalfPlaneSet,
      ∫ τ : ℝ, (g τ * ((τ : ℂ) - w)⁻¹ - (starRingEnd ℂ) (g τ) * ((τ : ℂ) - w)⁻¹) ∂nu = 0 := by
    intro w hw
    have hwim : w.im ≠ 0 := ne_of_gt hw
    rw [integral_sub (integrable_density_kernel hmeas hint hwim)
      (integrable_density_kernel hconjmeas hconjint hwim)]
    rw [show ∫ τ : ℝ, g τ * ((τ : ℂ) - w)⁻¹ ∂nu = densityCauchyTransform nu g w from rfl,
      show ∫ τ : ℝ, (starRingEnd ℂ) (g τ) * ((τ : ℂ) - w)⁻¹ ∂nu
        = densityCauchyTransform nu (fun τ => (starRingEnd ℂ) (g τ)) w from rfl,
      hupper w hw, hupperConj w hw, sub_zero]
  have hre : (fun τ : ℝ => (g τ).re) =ᵐ[nu] 0 := by
    refine real_density_eq_zero_of_transform_eq_zero_upper nu (by fun_prop) hint.re ?_
    intro w hw
    have hval : densityCauchyTransform nu (fun τ => ((g τ).re : ℂ)) w
        = (2 : ℂ)⁻¹ * ∫ τ : ℝ,
          (g τ * ((τ : ℂ) - w)⁻¹ + (starRingEnd ℂ) (g τ) * ((τ : ℂ) - w)⁻¹) ∂nu := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
      show ((g τ).re : ℂ) * ((τ : ℂ) - w)⁻¹ = (2 : ℂ)⁻¹ *
        (g τ * ((τ : ℂ) - w)⁻¹ + (starRingEnd ℂ) (g τ) * ((τ : ℂ) - w)⁻¹)
      have hcj : g τ + (starRingEnd ℂ) (g τ) = 2 * ((g τ).re : ℂ) := by
        rw [Complex.add_conj]
        push_cast
        ring
      linear_combination (-(2 : ℂ)⁻¹ * ((τ : ℂ) - w)⁻¹) * hcj
    rw [hval, hsumzero w hw, mul_zero]
  have him : (fun τ : ℝ => (g τ).im) =ᵐ[nu] 0 := by
    refine real_density_eq_zero_of_transform_eq_zero_upper nu (by fun_prop) hint.im ?_
    intro w hw
    have hval : densityCauchyTransform nu (fun τ => ((g τ).im : ℂ)) w
        = (-(2 : ℂ)⁻¹ * Complex.I) * ∫ τ : ℝ,
          (g τ * ((τ : ℂ) - w)⁻¹ - (starRingEnd ℂ) (g τ) * ((τ : ℂ) - w)⁻¹) ∂nu := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
      show ((g τ).im : ℂ) * ((τ : ℂ) - w)⁻¹ = (-(2 : ℂ)⁻¹ * Complex.I) *
        (g τ * ((τ : ℂ) - w)⁻¹ - (starRingEnd ℂ) (g τ) * ((τ : ℂ) - w)⁻¹)
      have hcj : g τ - (starRingEnd ℂ) (g τ) = 2 * ((g τ).im : ℂ) * Complex.I := by
        rw [Complex.sub_conj]
        push_cast
        ring
      linear_combination ((2 : ℂ)⁻¹ * Complex.I * ((τ : ℂ) - w)⁻¹) * hcj +
        (((g τ).im : ℂ) * ((τ : ℂ) - w)⁻¹) * Complex.I_sq
    rw [hval, hdiffzero w hw, mul_zero]
  filter_upwards [hre, him] with τ h1 h2
  have h1' : (g τ).re = 0 := h1
  have h2' : (g τ).im = 0 := h2
  show g τ = 0
  exact Complex.ext h1' h2'

end

end GaloisForLFunctions.HTGeometry
