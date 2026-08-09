import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralGammaScaling

/-!
# The rotated regularized Gamma integral

For `Re w > 0` and `−1 < a < 0` the regularized Gamma integral rotates:

`∫₀^∞ (e^{-wt} − 1) t^{a-1} dt = Γ(a) · w^{-a}`.

Both sides are holomorphic on the right half-plane and agree on the positive real axis, where the
identity is the real scaling of the regularized Gamma integral; the identity theorem propagates it
to the whole half-plane.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open MeasureTheory Set Filter Topology Complex

noncomputable section

variable {a : ℝ}

/-- The rotated regularized Gamma integrand. -/
def cgammaDefect (a : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  (Complex.exp (-(w * t)) - 1) * ((t ^ (a - 1) : ℝ) : ℂ)

/-- The rotated regularized Gamma integral. -/
def cgammaIntegral (a : ℝ) (w : ℂ) : ℂ := ∫ t in Ioi (0 : ℝ), cgammaDefect a w t

/-! ## Integrability -/

theorem norm_cexp_sub_one_le {w : ℂ} {t : ℝ} (ht : 0 ≤ t) (hwt : ‖w‖ * t ≤ 1) :
    ‖Complex.exp (-(w * t)) - 1‖ ≤ 2 * (‖w‖ * t) := by
  have hz : ‖-(w * (t : ℂ))‖ ≤ 1 := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    exact hwt
  have h := Complex.norm_exp_sub_one_le hz
  rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht] at h
  exact h

theorem norm_cexp_sub_one_le_two {w : ℂ} {t : ℝ} (hw : 0 < w.re) (ht : 0 ≤ t) :
    ‖Complex.exp (-(w * t)) - 1‖ ≤ 2 := by
  have hexp : ‖Complex.exp (-(w * (t : ℂ)))‖ ≤ 1 := by
    rw [Complex.norm_exp]
    refine Real.exp_le_one_iff.2 ?_
    have : (-(w * (t : ℂ))).re = -(w.re * t) := by simp
    rw [this]
    nlinarith
  calc ‖Complex.exp (-(w * t)) - 1‖ ≤ ‖Complex.exp (-(w * (t : ℂ)))‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
    _ ≤ 1 + 1 := by simpa using hexp
    _ = 2 := by norm_num

theorem measurable_cgammaDefect (a : ℝ) (w : ℂ) {S : Set ℝ} (hS : MeasurableSet S)
    (hS0 : ∀ t ∈ S, 0 < t) :
    AEStronglyMeasurable (cgammaDefect a w) (volume.restrict S) := by
  refine ContinuousOn.aestronglyMeasurable ?_ hS
  refine ContinuousOn.mul ?_ ?_
  · exact ((Complex.continuous_exp.comp (by fun_prop)).sub continuous_const).continuousOn
  · refine Complex.continuous_ofReal.continuousOn.comp ?_ (mapsTo_univ _ _)
    exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (hS0 x hx))

theorem integrableOn_cgammaDefect_near_zero (ha : -1 < a) (w : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hwδ : ‖w‖ * δ ≤ 1) : IntegrableOn (cgammaDefect a w) (Ioc 0 δ) := by
  have hIoo : IntegrableOn (fun t : ℝ => t ^ a) (Ioo 0 δ) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hδ).2 ha
  have hdom : IntegrableOn (fun t : ℝ => 2 * ‖w‖ * t ^ a) (Ioc 0 δ) :=
    (hIoo.congr_set_ae (Ioo_ae_eq_Ioc).symm).const_mul _
  refine Integrable.mono' hdom (measurable_cgammaDefect a w measurableSet_Ioc fun t ht => ht.1) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : (0 : ℝ) < t := ht.1
  have htδ : t ≤ δ := ht.2
  have hw : ‖w‖ * t ≤ 1 := le_trans (by nlinarith [norm_nonneg w]) hwδ
  have hsplit : t * t ^ (a - 1) = t ^ a := rpow_succ_split ht0 a
  have hwt : (0 : ℝ) < t ^ (a - 1) := Real.rpow_pos_of_pos ht0 _
  rw [cgammaDefect, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwt]
  calc ‖Complex.exp (-(w * t)) - 1‖ * t ^ (a - 1) ≤ 2 * (‖w‖ * t) * t ^ (a - 1) :=
        mul_le_mul_of_nonneg_right (norm_cexp_sub_one_le ht0.le hw) hwt.le
    _ = 2 * ‖w‖ * (t * t ^ (a - 1)) := by ring
    _ = 2 * ‖w‖ * t ^ a := by rw [hsplit]

theorem integrableOn_cgammaDefect_tail (ha0 : a < 0) {w : ℂ} (hw : 0 < w.re) {δ : ℝ}
    (hδ : 0 < δ) : IntegrableOn (cgammaDefect a w) (Ioi δ) := by
  have hdom : IntegrableOn (fun t : ℝ => 2 * t ^ (a - 1)) (Ioi δ) :=
    ((integrableOn_Ioi_rpow_iff hδ).2 (by linarith)).const_mul _
  refine Integrable.mono' hdom
    (measurable_cgammaDefect a w measurableSet_Ioi fun t ht => lt_trans hδ ht) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := lt_trans hδ ht
  have hwt : (0 : ℝ) < t ^ (a - 1) := Real.rpow_pos_of_pos ht0 _
  rw [cgammaDefect, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwt]
  calc ‖Complex.exp (-(w * t)) - 1‖ * t ^ (a - 1) ≤ 2 * t ^ (a - 1) :=
        mul_le_mul_of_nonneg_right (norm_cexp_sub_one_le_two hw ht0.le) hwt.le
    _ = 2 * t ^ (a - 1) := rfl

theorem integrableOn_cgammaDefect (ha : -1 < a) (ha0 : a < 0) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (cgammaDefect a w) (Ioi 0) := by
  set δ : ℝ := min 1 (1 / (‖w‖ + 1)) with hδdef
  have hnorm : (0 : ℝ) < ‖w‖ + 1 := by positivity
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hwδ : ‖w‖ * δ ≤ 1 := by
    have h1 : δ ≤ 1 / (‖w‖ + 1) := min_le_right _ _
    have h2 : ‖w‖ * δ ≤ ‖w‖ * (1 / (‖w‖ + 1)) :=
      mul_le_mul_of_nonneg_left h1 (norm_nonneg w)
    have h3 : ‖w‖ * (1 / (‖w‖ + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one hnorm]
      linarith
    linarith
  have hunion : Ioi (0 : ℝ) = Ioc 0 δ ∪ Ioi δ := by
    ext t
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro ht
      rcases le_or_gt t δ with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr h
    · rintro (⟨h, -⟩ | h)
      · exact h
      · linarith
  rw [hunion]
  exact (integrableOn_cgammaDefect_near_zero ha w hδ0 hwδ).union
    (integrableOn_cgammaDefect_tail ha0 hw hδ0)

/-! ## The value on the positive real axis -/

theorem cgammaDefect_ofReal (a x t : ℝ) :
    cgammaDefect a (x : ℂ) t = ((laplaceCochain x t * t ^ (a - 1) : ℝ) : ℂ) := by
  have h1 : -((x : ℂ) * (t : ℂ)) = ((-(x * t) : ℝ) : ℂ) := by push_cast; ring
  rw [cgammaDefect, h1, ← Complex.ofReal_exp, laplaceCochain, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_one]

theorem integrableOn_laplace_rpow (ha : -1 < a) (ha0 : a < 0) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => laplaceCochain x t * t ^ (a - 1)) (Ioi 0) := by
  have hc : IntegrableOn (cgammaDefect a (x : ℂ)) (Ioi 0) :=
    integrableOn_cgammaDefect ha ha0 (by simpa using hx)
  have hre : IntegrableOn (fun t : ℝ => RCLike.re (cgammaDefect a (x : ℂ) t)) (Ioi 0) := hc.re
  refine hre.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [cgammaDefect_ofReal]
  simp

/-- The real scaling of the regularized Gamma integral. -/
theorem integral_laplace_rpow (ha : -1 < a) (ha0 : a < 0) {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), laplaceCochain x t * t ^ (a - 1)) = x ^ (-a) * Real.Gamma a := by
  have hsc : EqOn (fun t : ℝ => laplaceCochain x t * t ^ (a - 1))
      (fun t : ℝ => x ^ (1 - a) * gammaDefect a (x * t)) (Ioi 0) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    show laplaceCochain x t * t ^ (a - 1) = x ^ (1 - a) * gammaDefect a (x * t)
    rw [gammaDefect_scaling hx ht0.le, ← mul_assoc, ← Real.rpow_add hx]
    norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi hsc, integral_const_mul,
    integral_comp_mul_left_Ioi (fun u => gammaDefect a u) 0 hx, mul_zero,
    integral_gammaDefect ha ha0, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← Real.rpow_neg_one x, ← Real.rpow_add hx]
  congr 1
  ring

/-- On the positive real axis the rotated integral is the real scaling law. -/
theorem cgammaIntegral_ofReal (ha : -1 < a) (ha0 : a < 0) {x : ℝ} (hx : 0 < x) :
    cgammaIntegral a (x : ℂ) = (Real.Gamma a : ℂ) * ((x : ℂ) ^ ((-a : ℝ) : ℂ)) := by
  have hint := integrableOn_laplace_rpow ha ha0 hx
  have hcast : (∫ t in Ioi (0 : ℝ), ((laplaceCochain x t * t ^ (a - 1) : ℝ) : ℂ)) =
      ((∫ t in Ioi (0 : ℝ), laplaceCochain x t * t ^ (a - 1) : ℝ) : ℂ) :=
    ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hint
  rw [cgammaIntegral, setIntegral_congr_fun measurableSet_Ioi
    (fun t _ => cgammaDefect_ofReal a x t), hcast, integral_laplace_rpow ha ha0 hx]
  rw [Complex.ofReal_mul, ← Complex.ofReal_cpow hx.le]
  ring

/-! ## Holomorphy in the rotation parameter -/

/-- The derivative of the rotated integrand in the rotation parameter. -/
def cgammaDeriv (a : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(w * t)) * (-(t : ℂ)) * ((t ^ (a - 1) : ℝ) : ℂ)

theorem hasDerivAt_cgammaDefect (a : ℝ) (w : ℂ) (t : ℝ) :
    HasDerivAt (fun v : ℂ => cgammaDefect a v t) (cgammaDeriv a w t) w := by
  have h0 : HasDerivAt (fun v : ℂ => v * (t : ℂ)) (t : ℂ) w := by
    simpa using (hasDerivAt_id w).mul_const (t : ℂ)
  have hinner : HasDerivAt (fun v : ℂ => -(v * (t : ℂ))) (-(t : ℂ)) w := h0.neg
  exact ((hinner.cexp.sub_const 1).mul_const _)

theorem measurable_cgammaDeriv (a : ℝ) (w : ℂ) {S : Set ℝ} (hS : MeasurableSet S)
    (hS0 : ∀ t ∈ S, 0 < t) : AEStronglyMeasurable (cgammaDeriv a w) (volume.restrict S) := by
  refine ContinuousOn.aestronglyMeasurable ?_ hS
  refine ContinuousOn.mul (ContinuousOn.mul ?_ (by fun_prop)) ?_
  · exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
  · refine Complex.continuous_ofReal.continuousOn.comp ?_ (mapsTo_univ _ _)
    exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (hS0 x hx))

theorem norm_cgammaDeriv (a : ℝ) (w : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖cgammaDeriv a w t‖ = Real.exp (-(w.re * t)) * t ^ a := by
  have hre : (-(w * (t : ℂ))).re = -(w.re * t) := by simp
  have hpos : (0 : ℝ) < t ^ (a - 1) := Real.rpow_pos_of_pos ht _
  rw [cgammaDeriv, norm_mul, norm_mul, Complex.norm_exp, hre, norm_neg, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht, abs_of_pos hpos,
    mul_assoc, rpow_succ_split ht a]

/-- **The rotated integral is holomorphic on the right half-plane.** -/
theorem hasDerivAt_cgammaIntegral (ha : -1 < a) (ha0 : a < 0) {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (cgammaIntegral a) (∫ t in Ioi (0 : ℝ), cgammaDeriv a w t) w := by
  set δ : ℝ := w.re / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hball : ∀ v ∈ Metric.ball w δ, δ ≤ v.re := by
    intro v hv
    have hlt : ‖v - w‖ < δ := by simpa [Complex.dist_eq] using hv
    have hre : |(v - w).re| ≤ ‖v - w‖ := Complex.abs_re_le_norm _
    have : |v.re - w.re| < δ := by
      simpa [Complex.sub_re] using lt_of_le_of_lt hre hlt
    have h2 := (abs_lt.1 this).1
    simp only [hδdef] at h2 ⊢
    linarith
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ v ∈ Metric.ball w δ,
      ‖cgammaDeriv a v t‖ ≤ Real.exp (-(δ * t)) * t ^ a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht v hv
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_cgammaDeriv a v ht0]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_pos_of_pos ht0 a).le
    refine Real.exp_le_exp.2 ?_
    have := hball v hv
    nlinarith
  have hdiff : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ v ∈ Metric.ball w δ,
      HasDerivAt (fun u : ℂ => cgammaDefect a u t) (cgammaDeriv a v t) v :=
    Filter.Eventually.of_forall fun t v _ => hasDerivAt_cgammaDefect a v t
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun v : ℂ => cgammaDefect a v) (x₀ := w) (s := Metric.ball w δ)
    (bound := fun t : ℝ => Real.exp (-(δ * t)) * t ^ a)
    (Metric.ball_mem_nhds w hδ)
    (Filter.Eventually.of_forall fun v =>
      measurable_cgammaDefect a v measurableSet_Ioi fun t ht => ht)
    (integrableOn_cgammaDefect ha ha0 hw)
    (measurable_cgammaDeriv a w measurableSet_Ioi fun t ht => ht)
    hbound (integrableOn_expScaled ha hδ) hdiff
  exact hres.2

theorem differentiableOn_cgammaIntegral (ha : -1 < a) (ha0 : a < 0) :
    DifferentiableOn ℂ (cgammaIntegral a) {w : ℂ | 0 < w.re} := fun _ hw =>
  ((hasDerivAt_cgammaIntegral ha ha0 hw).differentiableAt).differentiableWithinAt

/-! ## The rotation law -/

/-- The closed form of the rotated regularized Gamma integral. -/
def cgammaValue (a : ℝ) (w : ℂ) : ℂ := (Real.Gamma a : ℂ) * w ^ ((-a : ℝ) : ℂ)

theorem differentiableOn_cgammaValue (a : ℝ) :
    DifferentiableOn ℂ (cgammaValue a) {w : ℂ | 0 < w.re} := by
  intro w hw
  have hslit : w ∈ Complex.slitPlane := Or.inl hw
  exact (((Complex.hasStrictDerivAt_cpow_const
    (c := ((-a : ℝ) : ℂ)) hslit).hasDerivAt).differentiableAt.const_mul
      (Real.Gamma a : ℂ)).differentiableWithinAt

theorem tendsto_ofReal_nhdsWithin :
    Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝 (1 : ℝ)) (𝓝 (1 : ℂ)) := by
      simpa using (Complex.continuous_ofReal.tendsto (1 : ℝ))
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx1 : (1 : ℝ) < x := hx
    simp only [mem_compl_iff, mem_singleton_iff]
    intro hcon
    have : x = 1 := by exact_mod_cast hcon
    exact absurd this (ne_of_gt hx1)

/-- **The regularized Gamma integral rotates into the right half-plane.** -/
theorem cgammaIntegral_eq (ha : -1 < a) (ha0 : a < 0) {w : ℂ} (hw : 0 < w.re) :
    cgammaIntegral a w = (Real.Gamma a : ℂ) * w ^ ((-a : ℝ) : ℂ) := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (cgammaIntegral a) {w : ℂ | 0 < w.re} :=
    (differentiableOn_cgammaIntegral ha ha0).analyticOnNhd hopen
  have hg : AnalyticOnNhd ℂ (cgammaValue a) {w : ℂ | 0 < w.re} :=
    (differentiableOn_cgammaValue a).analyticOnNhd hopen
  have hconn : IsPreconnected {w : ℂ | 0 < w.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hone : (1 : ℂ) ∈ {w : ℂ | 0 < w.re} := by simp
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), cgammaIntegral a z = cgammaValue a z := by
    refine tendsto_ofReal_nhdsWithin.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    exact cgammaIntegral_ofReal ha ha0 hx0
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hconn hone hfreq hw

theorem continuousOn_cgammaDefect {a : ℝ} (w : ℂ) {S : Set ℝ} (hS : ∀ t ∈ S, 0 < t) :
    ContinuousOn (cgammaDefect a w) S := by
  refine ContinuousOn.mul ?_ ?_
  · exact ((Complex.continuous_exp.comp (by fun_prop)).sub continuous_const).continuousOn
  · refine Complex.continuous_ofReal.continuousOn.comp ?_ (mapsTo_univ _ _)
    exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (hS x hx))

theorem integrableOn_cgammaDefect_Ioo_one {a : ℝ} (ha : -1 < a) (w : ℂ) :
    IntegrableOn (cgammaDefect a w) (Ioo 0 1) := by
  set δ : ℝ := min (1 / 2) (1 / (‖w‖ + 1)) with hδdef
  have hnorm : (0 : ℝ) < ‖w‖ + 1 := by positivity
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hwδ : ‖w‖ * δ ≤ 1 := by
    have h1 : δ ≤ 1 / (‖w‖ + 1) := min_le_right _ _
    have h2 : ‖w‖ * δ ≤ ‖w‖ * (1 / (‖w‖ + 1)) :=
      mul_le_mul_of_nonneg_left h1 (norm_nonneg w)
    have h3 : ‖w‖ * (1 / (‖w‖ + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one hnorm]
      linarith
    linarith
  have hunion : Ioo (0 : ℝ) 1 = Ioc 0 δ ∪ Ioo δ 1 := by
    ext t
    simp only [mem_Ioo, mem_union, mem_Ioc]
    constructor
    · rintro ⟨ht0, ht1⟩
      rcases le_or_gt t δ with h | h
      · exact Or.inl ⟨ht0, h⟩
      · exact Or.inr ⟨h, ht1⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, lt_of_le_of_lt h2 hδ1⟩
      · exact ⟨lt_trans hδ0 h1, h2⟩
  have hfar : IntegrableOn (cgammaDefect a w) (Ioo δ 1) := by
    have hcont : ContinuousOn (cgammaDefect a w) (Icc δ 1) :=
      continuousOn_cgammaDefect w fun t ht => lt_of_lt_of_le hδ0 ht.1
    exact (hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [hunion]
  exact (integrableOn_cgammaDefect_near_zero ha w hδ0 hwδ).union hfar


/-! ## The ordinary rotated Gamma integral -/

/-- The ordinary rotated Gamma integrand. -/
def cgammaOrd (a : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(w * t)) * ((t ^ (a - 1) : ℝ) : ℂ)

/-- The ordinary rotated Gamma integral. -/
def cgammaOrdIntegral (a : ℝ) (w : ℂ) : ℂ := ∫ t in Ioi (0 : ℝ), cgammaOrd a w t

/-- The derivative of the ordinary rotated integrand in the rotation parameter. -/
def cgammaOrdDeriv (a : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(w * t)) * (-(t : ℂ)) * ((t ^ (a - 1) : ℝ) : ℂ)

theorem norm_cgammaOrd (a : ℝ) (w : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖cgammaOrd a w t‖ = Real.exp (-(w.re * t)) * t ^ (a - 1) := by
  have hre : (-(w * (t : ℂ))).re = -(w.re * t) := by simp
  have hpos : (0 : ℝ) < t ^ (a - 1) := Real.rpow_pos_of_pos ht _
  rw [cgammaOrd, norm_mul, Complex.norm_exp, hre, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpos]

theorem norm_cgammaOrdDeriv (a : ℝ) (w : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖cgammaOrdDeriv a w t‖ = Real.exp (-(w.re * t)) * t ^ a := by
  have hre : (-(w * (t : ℂ))).re = -(w.re * t) := by simp
  have hpos : (0 : ℝ) < t ^ (a - 1) := Real.rpow_pos_of_pos ht _
  rw [cgammaOrdDeriv, norm_mul, norm_mul, Complex.norm_exp, hre, norm_neg, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht, abs_of_pos hpos,
    mul_assoc, rpow_succ_split ht a]

theorem measurable_cgammaOrd (a : ℝ) (w : ℂ) {S : Set ℝ} (hS : MeasurableSet S)
    (hS0 : ∀ t ∈ S, 0 < t) : AEStronglyMeasurable (cgammaOrd a w) (volume.restrict S) := by
  refine ContinuousOn.aestronglyMeasurable ?_ hS
  refine ContinuousOn.mul ?_ ?_
  · exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
  · refine Complex.continuous_ofReal.continuousOn.comp ?_ (mapsTo_univ _ _)
    exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (hS0 x hx))

theorem measurable_cgammaOrdDeriv (a : ℝ) (w : ℂ) {S : Set ℝ} (hS : MeasurableSet S)
    (hS0 : ∀ t ∈ S, 0 < t) : AEStronglyMeasurable (cgammaOrdDeriv a w) (volume.restrict S) := by
  refine ContinuousOn.aestronglyMeasurable ?_ hS
  refine ContinuousOn.mul (ContinuousOn.mul ?_ (by fun_prop)) ?_
  · exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
  · refine Complex.continuous_ofReal.continuousOn.comp ?_ (mapsTo_univ _ _)
    exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (hS0 x hx))

theorem integrableOn_cgammaOrd (ha : 0 < a) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (cgammaOrd a w) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_expScaled (a := a - 1) (V := w.re) (by linarith) hw)
    (measurable_cgammaOrd a w measurableSet_Ioi fun t ht => ht) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact le_of_eq (norm_cgammaOrd a w ht)

theorem hasDerivAt_cgammaOrd (a : ℝ) (w : ℂ) (t : ℝ) :
    HasDerivAt (fun v : ℂ => cgammaOrd a v t) (cgammaOrdDeriv a w t) w := by
  have h0 : HasDerivAt (fun v : ℂ => v * (t : ℂ)) (t : ℂ) w := by
    simpa using (hasDerivAt_id w).mul_const (t : ℂ)
  exact (h0.neg.cexp.mul_const _)

/-- **The ordinary rotated integral is holomorphic on the right half-plane.** -/
theorem hasDerivAt_cgammaOrdIntegral (ha : 0 < a) {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (cgammaOrdIntegral a) (∫ t in Ioi (0 : ℝ), cgammaOrdDeriv a w t) w := by
  set δ : ℝ := w.re / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hball : ∀ v ∈ Metric.ball w δ, δ ≤ v.re := by
    intro v hv
    have hlt : ‖v - w‖ < δ := by simpa [Complex.dist_eq] using hv
    have hre : |(v - w).re| ≤ ‖v - w‖ := Complex.abs_re_le_norm _
    have hlt2 : |v.re - w.re| < δ := by
      simpa [Complex.sub_re] using lt_of_le_of_lt hre hlt
    have h2 := (abs_lt.1 hlt2).1
    simp only [hδdef] at h2 ⊢
    linarith
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ v ∈ Metric.ball w δ,
      ‖cgammaOrdDeriv a v t‖ ≤ Real.exp (-(δ * t)) * t ^ a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht v hv
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_cgammaOrdDeriv a v ht0]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_pos_of_pos ht0 a).le
    refine Real.exp_le_exp.2 ?_
    have := hball v hv
    nlinarith
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun v : ℂ => cgammaOrd a v) (x₀ := w) (s := Metric.ball w δ)
    (bound := fun t : ℝ => Real.exp (-(δ * t)) * t ^ a)
    (Metric.ball_mem_nhds w hδ)
    (Filter.Eventually.of_forall fun v =>
      measurable_cgammaOrd a v measurableSet_Ioi fun t ht => ht)
    (integrableOn_cgammaOrd ha hw)
    (measurable_cgammaOrdDeriv a w measurableSet_Ioi fun t ht => ht)
    hbound (integrableOn_expScaled (by linarith) hδ)
    (Filter.Eventually.of_forall fun t v _ => hasDerivAt_cgammaOrd a v t)
  exact hres.2

theorem cgammaOrd_ofReal (a x t : ℝ) :
    cgammaOrd a (x : ℂ) t = ((Real.exp (-(x * t)) * t ^ (a - 1) : ℝ) : ℂ) := by
  have h1 : -((x : ℂ) * (t : ℂ)) = ((-(x * t) : ℝ) : ℂ) := by push_cast; ring
  rw [cgammaOrd, h1, ← Complex.ofReal_exp, Complex.ofReal_mul]

theorem cgammaOrdIntegral_ofReal (ha : 0 < a) {x : ℝ} (hx : 0 < x) :
    cgammaOrdIntegral a (x : ℂ) = (Real.Gamma a : ℂ) * ((x : ℂ) ^ ((-a : ℝ) : ℂ)) := by
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(x * t)) * t ^ (a - 1)) (Ioi 0) :=
    integrableOn_expScaled (by linarith) hx
  have hcast : (∫ t in Ioi (0 : ℝ), ((Real.exp (-(x * t)) * t ^ (a - 1) : ℝ) : ℂ)) =
      ((∫ t in Ioi (0 : ℝ), Real.exp (-(x * t)) * t ^ (a - 1) : ℝ) : ℂ) :=
    ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hint
  have hval : (∫ t in Ioi (0 : ℝ), Real.exp (-(x * t)) * t ^ (a - 1)) = x ^ (-a) * Real.Gamma a := by
    have h := integral_expScaled (a := a - 1) (V := x) (by linarith) hx
    rw [sub_add_cancel] at h
    rw [h]
  rw [cgammaOrdIntegral, setIntegral_congr_fun measurableSet_Ioi
    (fun t _ => cgammaOrd_ofReal a x t), hcast, hval]
  rw [Complex.ofReal_mul, ← Complex.ofReal_cpow hx.le]
  ring

/-- **The ordinary Gamma integral rotates into the right half-plane.** -/
theorem cgammaOrdIntegral_eq (ha : 0 < a) {w : ℂ} (hw : 0 < w.re) :
    cgammaOrdIntegral a w = (Real.Gamma a : ℂ) * w ^ ((-a : ℝ) : ℂ) := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ (cgammaOrdIntegral a) {w : ℂ | 0 < w.re} := fun _ hv =>
    ((hasDerivAt_cgammaOrdIntegral ha hv).differentiableAt).differentiableWithinAt
  have hf : AnalyticOnNhd ℂ (cgammaOrdIntegral a) {w : ℂ | 0 < w.re} := hdiff.analyticOnNhd hopen
  have hg : AnalyticOnNhd ℂ (cgammaValue a) {w : ℂ | 0 < w.re} :=
    (differentiableOn_cgammaValue a).analyticOnNhd hopen
  have hconn : IsPreconnected {w : ℂ | 0 < w.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hone : (1 : ℂ) ∈ {w : ℂ | 0 < w.re} := by simp
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), cgammaOrdIntegral a z = cgammaValue a z := by
    refine tendsto_ofReal_nhdsWithin.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    exact cgammaOrdIntegral_ofReal ha hx0
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hconn hone hfreq hw

end

end GaloisForLFunctions.HTGeometry.Interfinity
