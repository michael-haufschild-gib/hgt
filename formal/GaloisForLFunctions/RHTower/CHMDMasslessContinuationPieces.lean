import GaloisForLFunctions.RHTower.CHMDArchimedeanLevyTranslateForm
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy

/-!
# CHMD: the pieces of the massless continuation

The translate form of the massless Weil side (`masslessWeilSide_eq_levy`) is a sum of pieces built
from the d'Alembert kernel `D(w) = 2w/sinh(πw)` and the Lévy density `ω`.  Away from the imaginary
axis every piece is holomorphic in `v`, except one: `∫_{1/2}^∞ ω(x) D(v − x) dx` has the moving poles
`x = v ∓ i` crossing the integration path when `Im v` crosses `±1`.  This module

* bounds `D` uniformly on strips `|Im w| ≤ η < 1` (`exists_norm_dAlembertKernel_le`) and on the
  half-planes `Re w ≥ δ` (`norm_dAlembertKernel_le_of_re_ge`);
* proves holomorphy of the pieces near every point with `Re v > 1/2`
  (`differentiableAt_archNearC`, `differentiableAt_archFarC`, `differentiableAt_contourVerticalC`)
  and of the shifted contour on the whole strip `−1/2 < Im v < 3/2`
  (`differentiableAt_contourHorizontalC`);
* deforms the real path `[1/2, ∞)` to the path `[1/2, 1/2 + i/2] ∪ [1/2 + i/2, ∞ + i/2)` by Cauchy's
  theorem on rectangles (`integral_levy_mul_dAlembert_eq_contour`): for real `v`,
  `∫_{1/2}^∞ ω(x) D(v − x) dx = i ∫_0^{1/2} ω(1/2 + iy) D(v − 1/2 − iy) dy + ∫_{1/2}^∞ ω(x + i/2) D(v − x − i/2) dx`;
* proves holomorphy of the complex prime wave `Σ_n (Λ(n)/√n)(D(log n + v) + D(log n − v))` with any
  single term removed, away from the remaining points `log n + i` (`differentiableAt_primeTailC`).
-/

open Complex MeasureTheory Set Filter Topology Metric Zeta23
open scoped Real Interval
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.CHMDLightCone

open RHTower.EvenSector

/-! ## Uniform bounds for the complex d'Alembert kernel -/

theorem norm_sinh_pi_mul_ge {w : ℂ} (hw : 0 < w.re) :
    Real.sinh (π * w.re) ≤ ‖Complex.sinh (π * w)‖ := by
  have h := sinh_re_sq_le_norm_sinh_sq (π * w)
  have hre : ((π : ℂ) * w).re = π * w.re := by simp
  rw [hre] at h
  exact (pow_le_pow_iff_left₀ (Real.sinh_nonneg_iff.mpr (by positivity)) (norm_nonneg _)
    two_ne_zero).mp h

/-- On `Re w ≥ δ > 0`, `|Im w| ≤ B`: `‖D(w)‖ ≤ (2/π)(1 + B/δ)`. -/
theorem norm_dAlembertKernel_le_of_re_ge {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) {w : ℂ}
    (hw : δ ≤ w.re) (him : |w.im| ≤ B) : ‖dAlembertKernel w‖ ≤ 2 / π * (1 + B / δ) := by
  have hpi := Real.pi_pos
  have hre : 0 < w.re := lt_of_lt_of_le hδ hw
  have hw0 : w ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have hs1 : π * w.re ≤ Real.sinh (π * w.re) := Real.self_le_sinh_iff.mpr (by positivity)
  have hs2 := norm_sinh_pi_mul_ge hre
  have hpos : 0 < ‖Complex.sinh (π * w)‖ := lt_of_lt_of_le (by positivity) (hs1.trans hs2)
  have hnorm : ‖w‖ ≤ w.re + B :=
    (Complex.norm_le_abs_re_add_abs_im w).trans (by rw [abs_of_pos hre]; linarith)
  rw [dAlembertKernel_of_ne hw0, norm_div, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num,
    div_le_iff₀ hpos]
  have h2 : 2 * (w.re + B) ≤ 2 / π * (1 + B / δ) * (π * w.re) := by
    rw [show 2 / π * (1 + B / δ) * (π * w.re) = 2 * (w.re + B * w.re / δ) by field_simp]
    have : B ≤ B * w.re / δ := by rw [le_div_iff₀ hδ]; nlinarith
    linarith
  have h3 : 2 / π * (1 + B / δ) * (π * w.re) ≤ 2 / π * (1 + B / δ) * ‖Complex.sinh (π * w)‖ :=
    mul_le_mul_of_nonneg_left (hs1.trans hs2) (by positivity)
  linarith

theorem one_add_mul_exp_neg_pi_le (t : ℝ) (ht : 0 ≤ t) : (1 + t) * Real.exp (-(π * t)) ≤ 1 := by
  have h1 : 1 + t ≤ Real.exp (π * t) := by
    have := Real.add_one_le_exp (π * t)
    nlinarith [Real.pi_gt_three]
  have hE : Real.exp (-(π * t)) * Real.exp (π * t) = 1 := by rw [← Real.exp_add]; simp
  have := Real.exp_pos (-(π * t))
  nlinarith

/-- `D` is bounded on every closed substrip `|Im w| ≤ η < 1`. -/
theorem exists_norm_dAlembertKernel_le {η : ℝ} (hη : η < 1) :
    ∃ M, ∀ w : ℂ, |w.im| ≤ η → ‖dAlembertKernel w‖ ≤ M := by
  set η' := max η 0
  have hη' : η' < 1 := max_lt hη one_pos
  set K := Icc (-1 : ℝ) 1 ×ℂ Icc (-η') η'
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hc : ContinuousOn dAlembertKernel K := fun w hw => by
    have hw' := (Complex.mem_reProdIm.mp hw).2
    have : |w.im| < 1 := lt_of_le_of_lt (abs_le.mpr ⟨hw'.1, hw'.2⟩) hη'
    exact (differentiableAt_dAlembertKernel (sinhSlope_ne_zero_of_abs_im_lt this)).continuousAt
      |>.continuousWithinAt
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max M₁ 8, fun w hw => ?_⟩
  by_cases hre : |w.re| ≤ 1
  · refine (hM₁ w (Complex.mem_reProdIm.mpr ⟨abs_le.mp hre, ?_⟩)).trans (le_max_left _ _)
    have := abs_le.mp (hw.trans (le_max_left η 0))
    exact ⟨this.1, this.2⟩
  · have hre' : 1 < |w.re| := not_le.mp hre
    have hpi := Real.pi_gt_three
    have h1 : 1 ≤ π * |w.re| := by nlinarith
    have hnorm : ‖w‖ ≤ |w.re| + 1 :=
      (Complex.norm_le_abs_re_add_abs_im w).trans (by linarith [hw.trans hη.le])
    refine (norm_dAlembertKernel_le h1).trans ((?_ : _ ≤ (8 : ℝ)).trans (le_max_right _ _))
    have h2 := one_add_mul_exp_neg_pi_le |w.re| (abs_nonneg _)
    have hE := Real.exp_pos (-(π * |w.re|))
    calc 8 * ‖w‖ * Real.exp (-(π * |w.re|)) ≤ 8 * (|w.re| + 1) * Real.exp (-(π * |w.re|)) := by
          gcongr
      _ = 8 * ((1 + |w.re|) * Real.exp (-(π * |w.re|))) := by ring
      _ ≤ 8 * 1 := by gcongr
      _ = 8 := by ring

/-! ## Bounds for the Lévy density -/

theorem one_sub_exp_neg_two_mul_ge (x : ℝ) :
    2 * x ≤ (1 - Real.exp (-2 * x)) * (1 + 2 * x) := by
  have h1 : 1 + 2 * x ≤ Real.exp (2 * x) := by linarith [Real.add_one_le_exp (2 * x)]
  have h2 : Real.exp (-2 * x) * Real.exp (2 * x) = 1 := by rw [← Real.exp_add]; simp
  have hE := Real.exp_pos (-2 * x)
  nlinarith

theorem archLevyDensity_mul_self_le {x : ℝ} (hx : 0 < x) :
    archLevyDensity x * x ≤ (1 + 2 * x) / 2 := by
  have hlt : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpos : 0 < 1 - Real.exp (-2 * x) := by linarith
  have h := one_sub_exp_neg_two_mul_ge x
  have he : Real.exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  unfold archLevyDensity
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  have := Real.exp_pos (-x / 2)
  nlinarith

theorem one_sub_exp_neg_two_mul_pos {a : ℝ} (ha : 0 < a) : 0 < 1 - Real.exp (-2 * a) := by
  have := Real.exp_lt_one_iff.mpr (by linarith : -2 * a < 0); linarith

theorem archLevyDensity_le_of_ge {a x : ℝ} (ha : 0 < a) (hx : a ≤ x) :
    archLevyDensity x ≤ Real.exp (-(1 / 2) * x) / (1 - Real.exp (-2 * a)) := by
  have h1 : Real.exp (-2 * x) ≤ Real.exp (-2 * a) := Real.exp_le_exp.mpr (by linarith)
  have h2 := one_sub_exp_neg_two_mul_pos ha
  unfold archLevyDensity
  rw [show -x / 2 = -(1 / 2) * x by ring]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le h2 (by linarith)

theorem integrableOn_archLevyDensity_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn archLevyDensity (Ioi a) := by
  refine ((exp_neg_integrableOn_Ioi a (by norm_num : (0 : ℝ) < 1 / 2)).div_const
    (1 - Real.exp (-2 * a))).mono' measurable_archLevyDensity.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : a < x := hx
  rw [Real.norm_eq_abs, abs_of_pos (archLevyDensity_pos (by linarith))]
  exact archLevyDensity_le_of_ge ha hx'.le

theorem norm_levyDensityC_le_of_re_ge {a : ℝ} (ha : 0 < a) {u : ℂ} (hu : a ≤ u.re) :
    ‖levyDensityC u‖ ≤ Real.exp (-(1 / 2) * u.re) / (1 - Real.exp (-2 * a)) := by
  refine (norm_levyDensityC_le (by linarith)).trans ?_
  have h1 : Real.exp (-2 * u.re) ≤ Real.exp (-2 * a) := Real.exp_le_exp.mpr (by linarith)
  rw [show -u.re / 2 = -(1 / 2) * u.re by ring]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (one_sub_exp_neg_two_mul_pos ha)
    (by linarith)

/-! ## The archimedean pieces -/

/-- The near archimedean piece `∫_{(0,a]} ω(x)(2D(v) − D(v+x) − D(v−x)) dx`. -/
def archNearC (a : ℝ) (v : ℂ) : ℂ :=
  ∫ x in Ioc (0 : ℝ) a, (archLevyDensity x : ℂ) *
    (2 * dAlembertKernel v - dAlembertKernel (v + x) - dAlembertKernel (v - x))

/-- The far archimedean piece `∫_{(a,∞)} ω(x)(2D(v) − D(v+x)) dx`. -/
def archFarC (a : ℝ) (v : ℂ) : ℂ :=
  ∫ x in Ioi a, (archLevyDensity x : ℂ) * (2 * dAlembertKernel v - dAlembertKernel (v + x))

theorem differentiableAt_dAlembertKernel_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ dAlembertKernel w :=
  differentiableAt_dAlembertKernel (sinhSlope_ne_zero_of_re_ne hw.ne')

theorem differentiableAt_archNearC {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 2) {v₁ : ℂ}
    (hv₁ : a < v₁.re) : DifferentiableAt ℂ (archNearC a) v₁ := by
  set r := (v₁.re - a) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  set c : ℝ → ℝ := fun x => max 0 (min x a) with hc
  have hc0 : ∀ x, 0 ≤ c x := fun x => le_max_left _ _
  have hc1 : ∀ x, c x ≤ a := fun x => max_le ha.le (min_le_right _ _)
  have hcc : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  -- the derivative bound on a compact ball in the right half-plane
  set K := closedBall v₁ (r + a)
  have hKre : ∀ w ∈ K, r ≤ w.re := by
    intro w hw
    have hn : ‖w - v₁‖ ≤ r + a := by rw [← dist_eq_norm]; exact mem_closedBall.mp hw
    have h := (Complex.abs_re_le_norm (w - v₁)).trans hn
    rw [Complex.sub_re] at h
    have := (abs_le.mp h).1
    rw [hr] at this ⊢
    linarith
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
  have hdiffU : DifferentiableOn ℂ dAlembertKernel {w : ℂ | 0 < w.re} :=
    fun w hw => (differentiableAt_dAlembertKernel_of_re_pos hw).differentiableWithinAt
  obtain ⟨M', hM'⟩ := (isCompact_closedBall v₁ (r + a)).exists_bound_of_continuousOn
    ((hdiffU.deriv hU).continuousOn.mono fun w hw => (lt_of_lt_of_le hr0 (hKre w hw) : _))
  have hmvt : ∀ x y, x ∈ K → y ∈ K → ‖dAlembertKernel y - dAlembertKernel x‖ ≤ M' * ‖y - x‖ :=
    fun x y hx hy => (convex_closedBall v₁ (r + a)).norm_image_sub_le_of_norm_deriv_le
      (fun w hw => differentiableAt_dAlembertKernel_of_re_pos (lt_of_lt_of_le hr0 (hKre w hw)))
      hM' hx hy
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hM' v₁ (mem_closedBall_self (by linarith)))
  set F : ℂ → ℝ → ℂ := fun v x => (archLevyDensity (c x) : ℂ) *
    (2 * dAlembertKernel v - dAlembertKernel (v + c x) - dAlembertKernel (v - c x)) with hF
  have hmemK : ∀ v ∈ ball v₁ r, ∀ s : ℝ, |s| ≤ a → v + s ∈ K := by
    intro v hv s hs
    rw [mem_closedBall, dist_eq_norm, show v + s - v₁ = (v - v₁) + s by ring]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith [(mem_ball.mp hv).le, show dist v v₁ = ‖v - v₁‖ from dist_eq_norm _ _]
  have hbound : ∀ x, ∀ v ∈ ball v₁ r, ‖F v x‖ ≤ 2 * M' := by
    intro x v hv
    have hvK : v ∈ K := by simpa using hmemK v hv 0 (by simp; exact ha.le)
    have h1 : ‖dAlembertKernel (v + c x) - dAlembertKernel v‖ ≤ M' * c x := by
      have := hmvt v (v + c x) hvK (hmemK v hv (c x) (by rw [abs_of_nonneg (hc0 x)]; exact hc1 x))
      rwa [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 x)] at this
    have h2 : ‖dAlembertKernel (v - c x) - dAlembertKernel v‖ ≤ M' * c x := by
      have := hmvt v (v + ((-c x : ℝ) : ℂ)) hvK (hmemK v hv (-c x) (by
        rw [abs_neg, abs_of_nonneg (hc0 x)]; exact hc1 x))
      rwa [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (hc0 x), ofReal_neg, ← sub_eq_add_neg] at this
    have hΔ : ‖2 * dAlembertKernel v - dAlembertKernel (v + c x) - dAlembertKernel (v - c x)‖ ≤
        2 * M' * c x := by
      rw [show 2 * dAlembertKernel v - dAlembertKernel (v + c x) - dAlembertKernel (v - c x) =
        -((dAlembertKernel (v + c x) - dAlembertKernel v) +
          (dAlembertKernel (v - c x) - dAlembertKernel v)) by ring, norm_neg]
      linarith [norm_add_le (dAlembertKernel (v + c x) - dAlembertKernel v)
        (dAlembertKernel (v - c x) - dAlembertKernel v)]
    simp only [hF]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rcases (hc0 x).eq_or_lt with h0 | hpos
    · rw [← h0]; simp [archLevyDensity]; positivity
    · rw [abs_of_pos (archLevyDensity_pos hpos)]
      have hω := archLevyDensity_mul_self_le hpos
      calc archLevyDensity (c x) * ‖2 * dAlembertKernel v - dAlembertKernel (v + c x) -
            dAlembertKernel (v - c x)‖ ≤ archLevyDensity (c x) * (2 * M' * c x) :=
            mul_le_mul_of_nonneg_left hΔ (archLevyDensity_pos hpos).le
        _ = 2 * M' * (archLevyDensity (c x) * c x) := by ring
        _ ≤ 2 * M' * ((1 + 2 * c x) / 2) := mul_le_mul_of_nonneg_left hω (by positivity)
        _ ≤ 2 * M' * 1 := by gcongr; linarith [hc1 x, ha']
        _ = 2 * M' := by ring
  have hdiff : ∀ x, DifferentiableOn ℂ (fun v => F v x) (ball v₁ r) := by
    intro x v hv
    have hre : r + a < v.re := by
      have h := (Complex.abs_re_le_norm (v - v₁)).trans_lt (by rw [← dist_eq_norm]; exact hv)
      rw [Complex.sub_re] at h
      have := (abs_lt.mp h).1
      rw [hr] at this ⊢
      linarith
    have h1 : 0 < v.re := by linarith
    have h2 : 0 < (v + c x).re := by simp; linarith [hc0 x]
    have h3 : 0 < (v - c x).re := by simp; linarith [hc1 x]
    exact (((differentiableAt_dAlembertKernel_of_re_pos h1).const_mul 2).sub
      ((differentiableAt_dAlembertKernel_of_re_pos h2).comp v (differentiableAt_id.add_const _))
      |>.sub ((differentiableAt_dAlembertKernel_of_re_pos h3).comp v
        (differentiableAt_id.sub_const _))).const_mul _ |>.differentiableWithinAt
  have hmeas : ∀ v ∈ ball v₁ r, AEStronglyMeasurable (F v) (volume.restrict (Ioc 0 a)) := by
    intro v hv
    refine (Measurable.aestronglyMeasurable ?_)
    have hre : r + a < v.re := by
      have h := (Complex.abs_re_le_norm (v - v₁)).trans_lt (by rw [← dist_eq_norm]; exact hv)
      rw [Complex.sub_re] at h
      have := (abs_lt.mp h).1
      rw [hr] at this ⊢
      linarith
    have hcontD : ∀ s : ℝ → ℝ, Continuous s → (∀ x, 0 < (v + s x).re) →
        Continuous fun x => dAlembertKernel (v + s x) := fun s hs hpos => by
      have hf : Continuous fun x => v + ((s x : ℝ) : ℂ) := continuous_const.add
        (continuous_ofReal.comp hs)
      exact continuous_iff_continuousAt.mpr fun x =>
        ContinuousAt.comp (f := fun x => v + ((s x : ℝ) : ℂ)) (g := dAlembertKernel)
          (differentiableAt_dAlembertKernel_of_re_pos (hpos x)).continuousAt hf.continuousAt
    have hp := hcontD c hcc fun x => by simp; linarith [hc0 x]
    have hm := hcontD (fun x => -c x) hcc.neg fun x => by simp; linarith [hc1 x]
    simp only [ofReal_neg, ← sub_eq_add_neg] at hm
    exact (continuous_ofReal.measurable.comp (measurable_archLevyDensity.comp hcc.measurable)).mul
      ((continuous_const.sub hp).sub hm).measurable
  have hD := differentiableAt_integral_of_cauchy_dominated (μ := volume.restrict (Ioc 0 a))
    hr0 hmeas hdiff hbound (integrableOn_const (by simp) )
  refine hD.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  have : c x = x := by
    simp only [hc]
    rw [min_eq_left hx.2, max_eq_right hx.1.le]
  simp only [hF, this]

theorem abs_re_sub_lt_of_mem_ball {v v₁ : ℂ} {r : ℝ} (hv : v ∈ ball v₁ r) : |v.re - v₁.re| < r := by
  have h := (Complex.abs_re_le_norm (v - v₁)).trans_lt (by rw [← dist_eq_norm]; exact hv)
  rwa [Complex.sub_re] at h

theorem abs_im_sub_lt_of_mem_ball {v v₁ : ℂ} {r : ℝ} (hv : v ∈ ball v₁ r) : |v.im - v₁.im| < r := by
  have h := (Complex.abs_im_le_norm (v - v₁)).trans_lt (by rw [← dist_eq_norm]; exact hv)
  rwa [Complex.sub_im] at h

theorem continuous_dAlembertKernel_comp {g : ℝ → ℂ} (hg : Continuous g)
    (hpos : ∀ x, sinhSlope (g x) ≠ 0) : Continuous fun x => dAlembertKernel (g x) :=
  continuous_iff_continuousAt.mpr fun x =>
    ContinuousAt.comp (f := g) (g := dAlembertKernel)
      (differentiableAt_dAlembertKernel (hpos x)).continuousAt hg.continuousAt

theorem differentiableAt_archFarC {a : ℝ} (ha : 0 < a) {v₁ : ℂ} (hv₁ : 0 < v₁.re)
    (him : |v₁.im| < 3 / 2) : DifferentiableAt ℂ (archFarC a) v₁ := by
  set r := min (v₁.re / 2) (1 / 2) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
  have hball : ∀ v ∈ ball v₁ r, v₁.re / 2 ≤ v.re ∧ |v.im| ≤ 2 := by
    intro v hv
    have h1 := abs_re_sub_lt_of_mem_ball hv
    have h2 := abs_im_sub_lt_of_mem_ball hv
    have hr1 : r ≤ v₁.re / 2 := min_le_left _ _
    have hr2 : r ≤ 1 / 2 := min_le_right _ _
    constructor
    · linarith [(abs_lt.mp h1).1]
    · rw [abs_le]; constructor <;> linarith [(abs_lt.mp h2).1, (abs_lt.mp h2).2, abs_lt.mp him]
  set M₁ := 2 / π * (1 + 2 / (v₁.re / 2))
  set c : ℝ → ℝ := fun x => max a x with hc
  have hc1 : ∀ x, a ≤ c x := fun x => le_max_left _ _
  set F : ℂ → ℝ → ℂ := fun v x =>
    (archLevyDensity (c x) : ℂ) * (2 * dAlembertKernel v - dAlembertKernel (v + c x)) with hF
  have hD : ∀ v ∈ ball v₁ r, ∀ t : ℝ, 0 ≤ t → ‖dAlembertKernel (v + t)‖ ≤ M₁ := by
    intro v hv t ht
    obtain ⟨h1, h2⟩ := hball v hv
    exact norm_dAlembertKernel_le_of_re_ge (by linarith) (by norm_num) (by simp; linarith)
      (by simpa using h2)
  have hbound : ∀ x, ∀ v ∈ ball v₁ r, ‖F v x‖ ≤ |archLevyDensity (c x)| * (3 * M₁) := by
    intro x v hv
    simp only [hF]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h0 := hD v hv 0 le_rfl
    simp only [ofReal_zero, add_zero] at h0
    have h1 := hD v hv (c x) (by linarith [hc1 x])
    calc ‖2 * dAlembertKernel v - dAlembertKernel (v + c x)‖
        ≤ ‖2 * dAlembertKernel v‖ + ‖dAlembertKernel (v + c x)‖ := norm_sub_le _ _
      _ ≤ 2 * M₁ + M₁ := by
          rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]; linarith
      _ = 3 * M₁ := by ring
  have hdiff : ∀ x, DifferentiableOn ℂ (fun v => F v x) (ball v₁ r) := by
    intro x v hv
    obtain ⟨h1, -⟩ := hball v hv
    have hp1 : 0 < v.re := by linarith
    have hp2 : 0 < (v + c x).re := by simp; linarith [hc1 x]
    exact ((((differentiableAt_dAlembertKernel_of_re_pos hp1).const_mul 2).sub
      ((differentiableAt_dAlembertKernel_of_re_pos hp2).comp v
        (differentiableAt_id.add_const _))).const_mul _).differentiableWithinAt
  have hmeas : ∀ v ∈ ball v₁ r, AEStronglyMeasurable (F v) (volume.restrict (Ioi a)) := by
    intro v hv
    obtain ⟨h1, -⟩ := hball v hv
    have hcc : Continuous c := continuous_const.max continuous_id
    have hp : Continuous fun x => dAlembertKernel (v + c x) :=
      continuous_dAlembertKernel_comp (continuous_const.add (continuous_ofReal.comp hcc))
        fun x => sinhSlope_ne_zero_of_re_ne (by simp; linarith [hc1 x])
    exact (Measurable.aestronglyMeasurable
      ((continuous_ofReal.measurable.comp (measurable_archLevyDensity.comp hcc.measurable)).mul
        (continuous_const.sub hp).measurable))
  have hint : IntegrableOn (fun x => |archLevyDensity (c x)| * (3 * M₁)) (Ioi a) := by
    refine MeasureTheory.IntegrableOn.congr_fun
      ((integrableOn_archLevyDensity_Ioi ha).mul_const (3 * M₁)) (fun x hx => ?_) measurableSet_Ioi
    have hx' : a < x := hx
    simp only [hc, max_eq_right hx'.le, abs_of_pos (archLevyDensity_pos (by linarith : (0 : ℝ) < x))]
  have hDiff := differentiableAt_integral_of_cauchy_dominated
    (μ := volume.restrict (Ioi a)) hr0 hmeas hdiff hbound hint
  refine hDiff.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx' : a < x := hx
  simp only [hF, hc, max_eq_right hx'.le]

/-! ## The deformed contour -/

/-- The vertical part `∫_0^{1/2} ω(a + iy) D(v − a − iy) dy` of the deformed contour. -/
def contourVerticalC (a : ℝ) (v : ℂ) : ℂ :=
  ∫ y in Ioc (0 : ℝ) (1 / 2), levyDensityC (a + y * I) * dAlembertKernel (v - (a + y * I))

/-- The horizontal part `∫_a^∞ ω(x + i/2) D(v − x − i/2) dx` of the deformed contour. -/
def contourHorizontalC (a : ℝ) (v : ℂ) : ℂ :=
  ∫ x in Ioi a, levyDensityC (x + I / 2) * dAlembertKernel (v - (x + I / 2))

theorem norm_levyDensityC_vertical_le {a : ℝ} (ha : 0 < a) (y : ℝ) :
    ‖levyDensityC (a + y * I)‖ ≤ 1 / (1 - Real.exp (-2 * a)) := by
  have hre : ((a : ℂ) + (y : ℂ) * I).re = a := by simp
  refine (norm_levyDensityC_le_of_re_ge ha (by rw [hre])).trans ?_
  rw [hre]
  exact div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr (by linarith))
    (one_sub_exp_neg_two_mul_pos ha).le

theorem continuous_levyDensityC_comp {g : ℝ → ℂ} (hg : Continuous g) (hpos : ∀ x, 0 < (g x).re) :
    Continuous fun x => levyDensityC (g x) :=
  continuous_iff_continuousAt.mpr fun x =>
    ContinuousAt.comp (f := g) (g := levyDensityC)
      (differentiableAt_levyDensityC (hpos x)).continuousAt hg.continuousAt

theorem differentiableAt_contourVerticalC {a : ℝ} (ha : 0 < a) {v₁ : ℂ} (hv₁ : a < v₁.re)
    (him : |v₁.im| < 3 / 2) : DifferentiableAt ℂ (contourVerticalC a) v₁ := by
  set r := min ((v₁.re - a) / 2) (1 / 4) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
  set δ := (v₁.re - a) / 2 with hδdef
  have hball : ∀ v ∈ ball v₁ r, δ ≤ v.re - a ∧ |v.im| ≤ 2 := by
    intro v hv
    have h1 := abs_re_sub_lt_of_mem_ball hv
    have h2 := abs_im_sub_lt_of_mem_ball hv
    have hr1 : r ≤ δ := min_le_left _ _
    have hr2 : r ≤ 1 / 4 := min_le_right _ _
    constructor
    · linarith [(abs_lt.mp h1).1, hδdef]
    · rw [abs_le]; constructor <;> linarith [(abs_lt.mp h2).1, (abs_lt.mp h2).2, abs_lt.mp him]
  set M₁ := 2 / π * (1 + (5 / 2) / δ)
  set c : ℝ → ℝ := fun x => max 0 (min x (1 / 2)) with hc
  have hc0 : ∀ x, 0 ≤ c x := fun x => le_max_left _ _
  have hc1 : ∀ x, c x ≤ 1 / 2 := fun x => max_le (by norm_num) (min_le_right _ _)
  have hcc : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  set F : ℂ → ℝ → ℂ := fun v y =>
    levyDensityC (a + c y * I) * dAlembertKernel (v - (a + c y * I)) with hF
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hbound : ∀ y, ∀ v ∈ ball v₁ r, ‖F v y‖ ≤ 1 / (1 - Real.exp (-2 * a)) * M₁ := by
    intro y v hv
    obtain ⟨h1, h2⟩ := hball v hv
    simp only [hF]
    rw [norm_mul]
    refine mul_le_mul (norm_levyDensityC_vertical_le ha _) ?_ (norm_nonneg _)
      (div_nonneg zero_le_one (one_sub_exp_neg_two_mul_pos ha).le)
    refine norm_dAlembertKernel_le_of_re_ge hδ (by norm_num) (by simp; linarith) ?_
    simp only [sub_im, add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, mul_one,
      add_zero]
    rw [abs_le] at h2 ⊢
    constructor <;> linarith [hc0 y, hc1 y]
  have hdiff : ∀ y, DifferentiableOn ℂ (fun v => F v y) (ball v₁ r) := by
    intro y v hv
    obtain ⟨h1, -⟩ := hball v hv
    have hp : 0 < (v - (a + c y * I)).re := by simp; linarith
    exact ((differentiableAt_dAlembertKernel_of_re_pos hp).comp v
      (differentiableAt_id.sub_const _)).const_mul _ |>.differentiableWithinAt
  have hmeas : ∀ v ∈ ball v₁ r, AEStronglyMeasurable (F v) (volume.restrict (Ioc 0 (1 / 2))) := by
    intro v hv
    obtain ⟨h1, -⟩ := hball v hv
    have hg : Continuous fun y => (a : ℂ) + (c y : ℂ) * I :=
      continuous_const.add ((continuous_ofReal.comp hcc).mul continuous_const)
    have hL := continuous_levyDensityC_comp hg fun y => by simp; exact ha
    have hDc : Continuous fun y => dAlembertKernel (v - (a + c y * I)) :=
      continuous_dAlembertKernel_comp (continuous_const.sub hg)
        fun y => sinhSlope_ne_zero_of_re_ne (by simp; linarith)
    exact (hL.mul hDc).aestronglyMeasurable
  have hDiff := differentiableAt_integral_of_cauchy_dominated
    (μ := volume.restrict (Ioc 0 (1 / 2))) hr0 hmeas hdiff hbound (integrableOn_const (by simp))
  refine hDiff.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
  refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
  have : c y = y := by simp only [hc]; rw [min_eq_left hy.2, max_eq_right hy.1.le]
  simp only [hF, this]

theorem differentiableAt_contourHorizontalC {a : ℝ} (ha : 0 < a) {v₁ : ℂ} (h1 : -1 / 2 < v₁.im)
    (h2 : v₁.im < 3 / 2) : DifferentiableAt ℂ (contourHorizontalC a) v₁ := by
  set η₁ := |v₁.im - 1 / 2|
  have hη₁ : η₁ < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  set r := (1 - η₁) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  obtain ⟨M, hM⟩ := exists_norm_dAlembertKernel_le (η := η₁ + r) (by rw [hr]; linarith)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp; positivity))
  have hball : ∀ v ∈ ball v₁ r, |v.im - 1 / 2| ≤ η₁ + r := by
    intro v hv
    have h := abs_im_sub_lt_of_mem_ball hv
    calc |v.im - 1 / 2| = |(v.im - v₁.im) + (v₁.im - 1 / 2)| := by ring_nf
      _ ≤ |v.im - v₁.im| + η₁ := abs_add_le _ _
      _ ≤ η₁ + r := by linarith
  set c : ℝ → ℝ := fun x => max a x with hc
  have hc1 : ∀ x, a ≤ c x := fun x => le_max_left _ _
  have hcc : Continuous c := continuous_const.max continuous_id
  set F : ℂ → ℝ → ℂ := fun v x =>
    levyDensityC (c x + I / 2) * dAlembertKernel (v - (c x + I / 2)) with hF
  have himw : ∀ v x, (v - ((c x : ℂ) + I / 2)).im = v.im - 1 / 2 := by intro v x; simp
  have hbound : ∀ x, ∀ v ∈ ball v₁ r, ‖F v x‖ ≤
      Real.exp (-(1 / 2) * c x) / (1 - Real.exp (-2 * a)) * M := by
    intro x v hv
    simp only [hF]
    rw [norm_mul]
    have hre : ((c x : ℂ) + I / 2).re = c x := by simp
    refine mul_le_mul ?_ (hM _ (by rw [himw]; exact hball v hv)) (norm_nonneg _)
      (div_nonneg (Real.exp_pos _).le (one_sub_exp_neg_two_mul_pos ha).le)
    have := norm_levyDensityC_le_of_re_ge ha (u := (c x : ℂ) + I / 2) (by rw [hre]; exact hc1 x)
    rwa [hre] at this
  have hdiff : ∀ x, DifferentiableOn ℂ (fun v => F v x) (ball v₁ r) := by
    intro x v hv
    have hs : sinhSlope (v - (c x + I / 2)) ≠ 0 :=
      sinhSlope_ne_zero_of_abs_im_lt (by rw [himw]; linarith [hball v hv])
    exact ((differentiableAt_dAlembertKernel hs).comp v
      (differentiableAt_id.sub_const _)).const_mul _ |>.differentiableWithinAt
  have hmeas : ∀ v ∈ ball v₁ r, AEStronglyMeasurable (F v) (volume.restrict (Ioi a)) := by
    intro v hv
    have hg : Continuous fun x => (c x : ℂ) + I / 2 :=
      (continuous_ofReal.comp hcc).add continuous_const
    have hL := continuous_levyDensityC_comp hg fun x => by simp; linarith [hc1 x]
    have hDc : Continuous fun x => dAlembertKernel (v - (c x + I / 2)) :=
      continuous_dAlembertKernel_comp (continuous_const.sub hg)
        fun x => sinhSlope_ne_zero_of_abs_im_lt (by rw [himw]; linarith [hball v hv])
    exact (hL.mul hDc).aestronglyMeasurable
  have hint : IntegrableOn (fun x => Real.exp (-(1 / 2) * c x) / (1 - Real.exp (-2 * a)) * M)
      (Ioi a) := by
    refine MeasureTheory.IntegrableOn.congr_fun
      (((exp_neg_integrableOn_Ioi a (by norm_num : (0 : ℝ) < 1 / 2)).div_const
        (1 - Real.exp (-2 * a))).mul_const M) (fun x hx => ?_) measurableSet_Ioi
    have hx' : a < x := hx
    simp only [hc, max_eq_right hx'.le]
  have hDiff := differentiableAt_integral_of_cauchy_dominated
    (μ := volume.restrict (Ioi a)) hr0 hmeas hdiff hbound hint
  refine hDiff.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx' : a < x := hx
  simp only [hF, hc, max_eq_right hx'.le]

/-! ## Cauchy's theorem: deforming the real path -/

/-- **Deforming the path of the archimedean translate integral.**  For real `v`,
`∫_a^∞ ω(x) D(v − x) dx = i ∫_0^{1/2} ω(a + iy) D(v − a − iy) dy + ∫_a^∞ ω(x + i/2) D(v − x − i/2) dx`. -/
theorem integral_levy_mul_dAlembert_eq_contour {a : ℝ} (ha : 0 < a) (v : ℝ) :
    (∫ x in Ioi a, (archLevyDensity x : ℂ) * dAlembertKernel ((v : ℂ) - x)) =
      I * contourVerticalC a v + contourHorizontalC a v := by
  set f : ℂ → ℂ := fun u => levyDensityC u * dAlembertKernel ((v : ℂ) - u) with hf
  obtain ⟨M, hM⟩ := exists_norm_dAlembertKernel_le (η := 1 / 2) (by norm_num)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have hE1 : 0 < 1 - Real.exp (-2 * a) := one_sub_exp_neg_two_mul_pos ha
  have hfd : ∀ u : ℂ, a ≤ u.re → 0 ≤ u.im → u.im ≤ 1 / 2 → DifferentiableAt ℂ f u := by
    intro u hre h0 h1
    have hs : sinhSlope ((v : ℂ) - u) ≠ 0 := sinhSlope_ne_zero_of_abs_im_lt (by
      simp only [sub_im, ofReal_im, zero_sub, abs_neg]; rw [abs_of_nonneg h0]; linarith)
    exact (differentiableAt_levyDensityC (by linarith)).mul
      ((differentiableAt_dAlembertKernel hs).comp u ((differentiableAt_const _).sub differentiableAt_id))
  have hfb : ∀ u : ℂ, a ≤ u.re → 0 ≤ u.im → u.im ≤ 1 / 2 →
      ‖f u‖ ≤ Real.exp (-(1 / 2) * u.re) / (1 - Real.exp (-2 * a)) * M := by
    intro u hre h0 h1
    simp only [hf]
    rw [norm_mul]
    exact mul_le_mul (norm_levyDensityC_le_of_re_ge ha hre) (hM _ (by
      simp only [sub_im, ofReal_im, zero_sub, abs_neg]; rw [abs_of_nonneg h0]; exact h1))
      (norm_nonneg _) (div_nonneg (Real.exp_pos _).le hE1.le)
  -- the rectangle identity
  have hrect : ∀ R : ℝ, a ≤ R →
      (((∫ x in a..R, f x) - ∫ x in a..R, f (x + ((1 / 2 : ℝ) : ℂ) * I)) +
        I • ∫ y in (0 : ℝ)..(1 / 2), f (R + y * I)) -
        I • ∫ y in (0 : ℝ)..(1 / 2), f ((a : ℂ) + y * I) = 0 := by
    intro R hR
    have hz1 : ((a : ℂ)).re = a := by simp
    have hz2 : ((a : ℂ)).im = 0 := by simp
    have hw1 : ((R : ℂ) + ((1 / 2 : ℝ) : ℂ) * I).re = R := by simp
    have hw2 : ((R : ℂ) + ((1 / 2 : ℝ) : ℂ) * I).im = 1 / 2 := by simp
    have hd : DifferentiableOn ℂ f ([[((a : ℂ)).re, ((R : ℂ) + ((1 / 2 : ℝ) : ℂ) * I).re]] ×ℂ
        [[((a : ℂ)).im, ((R : ℂ) + ((1 / 2 : ℝ) : ℂ) * I).im]]) := by
      intro u hu
      rw [hz1, hz2, hw1, hw2, Complex.mem_reProdIm, Set.uIcc_of_le hR,
        Set.uIcc_of_le (by norm_num)] at hu
      exact (hfd u hu.1.1 hu.2.1 hu.2.2).differentiableWithinAt
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f _ _ hd
    rw [hz1, hz2, hw1, hw2] at h
    simpa only [ofReal_zero, zero_mul, add_zero] using h
  -- integrability along the two horizontal lines
  have hint : ∀ b : ℝ, 0 ≤ b → b ≤ 1 / 2 →
      IntegrableOn (fun x : ℝ => f (x + (b : ℂ) * I)) (Ioi a) := by
    intro b hb0 hb1
    have hre : ∀ x : ℝ, ((x : ℂ) + (b : ℂ) * I).re = x := by intro x; simp
    have him : ∀ x : ℝ, ((x : ℂ) + (b : ℂ) * I).im = b := by intro x; simp
    refine (((exp_neg_integrableOn_Ioi a (by norm_num : (0 : ℝ) < 1 / 2)).div_const
      (1 - Real.exp (-2 * a))).mul_const M).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
      have hx' : a < x := hx
      exact (ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + (b : ℂ) * I) (g := f)
        (hfd ((x : ℂ) + (b : ℂ) * I) (by rw [hre]; exact hx'.le) (by rw [him]; exact hb0)
          (by rw [him]; exact hb1)).continuousAt
        (continuous_ofReal.add continuous_const).continuousAt).continuousWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx' : a < x := hx
      have := hfb ((x : ℂ) + (b : ℂ) * I) (by rw [hre]; exact hx'.le) (by rw [him]; exact hb0)
        (by rw [him]; exact hb1)
      rwa [hre] at this
  have hbot := intervalIntegral_tendsto_integral_Ioi a (by
    simpa using hint 0 le_rfl (by norm_num)) tendsto_id
  have htop := intervalIntegral_tendsto_integral_Ioi a (hint (1 / 2) (by norm_num) le_rfl)
    tendsto_id
  have hright : Tendsto (fun R : ℝ => ∫ y in (0 : ℝ)..(1 / 2), f (R + y * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun R => Real.exp (-(1 / 2) * R) / (1 - Real.exp (-2 * a)) * M *
      |(1 / 2 : ℝ) - 0|) ?_ ?_
    · filter_upwards [eventually_ge_atTop a] with R hR
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
      rw [Set.uIoc_of_le (by norm_num)] at hy
      have := hfb ((R : ℂ) + (y : ℂ) * I) (by simp; linarith) (by simp; linarith [hy.1])
        (by simp; linarith [hy.2])
      simpa using this
    · have h1 : Tendsto (fun R : ℝ => Real.exp (-(1 / 2) * R)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))
      simpa using ((h1.div_const (1 - Real.exp (-2 * a))).mul_const M).mul_const |(1 / 2 : ℝ) - 0|
  have hlim := ((hbot.sub htop).add (hright.const_smul I)).sub_const
    (I • ∫ y in (0 : ℝ)..(1 / 2), f ((a : ℂ) + y * I))
  have hzero : Tendsto (fun R : ℝ => (((∫ x in a..R, f x) -
      ∫ x in a..R, f (x + ((1 / 2 : ℝ) : ℂ) * I)) +
        I • ∫ y in (0 : ℝ)..(1 / 2), f (R + y * I)) -
        I • ∫ y in (0 : ℝ)..(1 / 2), f ((a : ℂ) + y * I)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop a] with R hR
      exact (hrect R hR).symm)
  have heq := tendsto_nhds_unique hlim hzero
  simp only [smul_eq_mul] at heq
  have hL : (∫ x in Ioi a, f x) =
      ∫ x in Ioi a, (archLevyDensity x : ℂ) * dAlembertKernel ((v : ℂ) - x) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [hf, levyDensityC_ofReal]
  have hT : (∫ x in Ioi a, f (x + ((1 / 2 : ℝ) : ℂ) * I)) = contourHorizontalC a v := by
    unfold contourHorizontalC
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [hf]
    rw [show ((x : ℂ) + ((1 / 2 : ℝ) : ℂ) * I) = x + I / 2 by push_cast; ring]
  have hV : (∫ y in (0 : ℝ)..(1 / 2), f ((a : ℂ) + y * I)) = contourVerticalC a v := by
    unfold contourVerticalC
    rw [intervalIntegral.integral_of_le (by norm_num)]
  rw [← hL, ← hT, ← hV]
  linear_combination heq

/-! ## The complex prime wave -/

/-- One prime term `(Λ(n)/√n)(D(log n + v) + D(log n − v))` of complex argument. -/
def primeTermC (n : ℕ) (v : ℂ) : ℂ :=
  chmdPrimeWeight n * (dAlembertKernel (Real.log n + v) + dAlembertKernel (Real.log n - v))

/-- The complex d'Alembert prime wave. -/
def primeWaveC (v : ℂ) : ℂ := ∑' n : ℕ, primeTermC n v

theorem primeTermC_ofReal (n : ℕ) (v : ℝ) :
    primeTermC n v = ((chmdPrimeWeight n *
      (dAlembertReal (Real.log n + v) + dAlembertReal (Real.log n - v)) : ℝ) : ℂ) := by
  unfold primeTermC
  rw [show ((Real.log n : ℝ) : ℂ) + (v : ℂ) = ((Real.log n + v : ℝ) : ℂ) by push_cast; ring,
    show ((Real.log n : ℝ) : ℂ) - (v : ℂ) = ((Real.log n - v : ℝ) : ℂ) by push_cast; ring,
    dAlembertKernel_ofReal, dAlembertKernel_ofReal]
  push_cast
  ring

theorem primeWaveC_ofReal (v : ℝ) : primeWaveC v = (masslessPrimeWave v : ℂ) := by
  unfold primeWaveC masslessPrimeWave
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n => primeTermC_ofReal n v

theorem primeTermC_eq_zero_of_weight {n : ℕ} (hn : chmdPrimeWeight n = 0) :
    primeTermC n = fun _ => 0 := by
  funext v; simp [primeTermC, hn]

theorem sinhSlope_log_sub_ne_zero {n : ℕ} {v : ℂ} (hre : v.re ≠ Real.log n ∨ v.im ≠ 1)
    (h1 : -1 / 2 < v.im) (h2 : v.im < 3 / 2) :
    sinhSlope ((Real.log n : ℂ) - v) ≠ 0 := by
  rw [Ne, sinhSlope_eq_zero_iff]
  rintro ⟨k, hk, hkv⟩
  have hre' : v.re = Real.log n := by
    have := congrArg Complex.re hkv
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.intCast_re,
      Complex.intCast_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero] at this
    linarith
  have him' : v.im = -k := by
    have := congrArg Complex.im hkv
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
      zero_sub] at this
    linarith
  have hk1 : (k : ℝ) = -1 := by
    rw [him'] at h1 h2
    have hlt : -(3 / 2 : ℝ) < k := by linarith
    have hgt : (k : ℝ) < 1 / 2 := by linarith
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have : k = -1 := by
      have a1 : -2 < k := by exact_mod_cast (show ((-2 : ℤ) : ℝ) < k by push_cast; linarith)
      have a2 : k < 1 := by exact_mod_cast (show (k : ℝ) < ((1 : ℤ) : ℝ) by push_cast; linarith)
      omega
    exact_mod_cast this
  rcases hre with h | h
  · exact h hre'
  · exact h (by rw [him', hk1]; norm_num)

/-- **Decay of the far prime terms**: for `Re v ≥ 0`, `Re v + 3/4 < log n` and `‖v‖ ≤ R`,
`‖(Λ(n)/√n)(D(log n + v) + D(log n − v))‖ ≤ 2 (Λ(n)/√n) · 8(1 + log n + R) e^{πR} n^{−π}`. -/
theorem norm_primeTermC_le {n : ℕ} {v : ℂ} (hre : 0 ≤ v.re) (hn : v.re + 3 / 4 < Real.log n)
    {R : ℝ} (hR : ‖v‖ ≤ R) :
    ‖primeTermC n v‖ ≤ 2 * (chmdPrimeWeight n *
      (8 * (1 + Real.log n + R) * Real.exp (π * R) * (n : ℝ) ^ (-π))) := by
  have hpi := Real.pi_gt_three
  have hn0 : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hn; linarith
    · exact_mod_cast h
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  have hvre : v.re ≤ R := (Complex.re_le_norm v).trans hR
  have hexp : Real.exp (-(π * Real.log n)) = (n : ℝ) ^ (-π) := by
    rw [Real.rpow_def_of_pos hn0]; ring_nf
  unfold primeTermC
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (chmdPrimeWeight_nonneg n)]
  have hA : ‖dAlembertKernel ((Real.log n : ℂ) + v)‖ ≤
      8 * (1 + Real.log n + R) * Real.exp (π * R) * (n : ℝ) ^ (-π) := by
    have hre1 : ((Real.log n : ℂ) + v).re = Real.log n + v.re := by
      rw [Complex.add_re, Complex.ofReal_re]
    have hge : 1 ≤ π * |((Real.log n : ℂ) + v).re| := by
      rw [hre1, abs_of_pos (by linarith)]; nlinarith
    refine (norm_dAlembertKernel_le hge).trans ?_
    rw [hre1, abs_of_pos (by linarith)]
    have hn1 : ‖(Real.log n : ℂ) + v‖ ≤ 1 + Real.log n + R := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
    have he : Real.exp (-(π * (Real.log n + v.re))) ≤ Real.exp (π * R) * (n : ℝ) ^ (-π) := by
      rw [← hexp, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith)
    calc 8 * ‖(Real.log n : ℂ) + v‖ * Real.exp (-(π * (Real.log n + v.re)))
        ≤ 8 * (1 + Real.log n + R) * (Real.exp (π * R) * (n : ℝ) ^ (-π)) := by
          gcongr
      _ = _ := by ring
  have hB : ‖dAlembertKernel ((Real.log n : ℂ) - v)‖ ≤
      8 * (1 + Real.log n + R) * Real.exp (π * R) * (n : ℝ) ^ (-π) := by
    have hre1 : ((Real.log n : ℂ) - v).re = Real.log n - v.re := by
      rw [Complex.sub_re, Complex.ofReal_re]
    have hge : 1 ≤ π * |((Real.log n : ℂ) - v).re| := by
      rw [hre1, abs_of_pos (by linarith)]; nlinarith
    refine (norm_dAlembertKernel_le hge).trans ?_
    rw [hre1, abs_of_pos (by linarith)]
    have hn1 : ‖(Real.log n : ℂ) - v‖ ≤ 1 + Real.log n + R := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
    have he : Real.exp (-(π * (Real.log n - v.re))) ≤ Real.exp (π * R) * (n : ℝ) ^ (-π) := by
      rw [← hexp, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith)
    calc 8 * ‖(Real.log n : ℂ) - v‖ * Real.exp (-(π * (Real.log n - v.re)))
        ≤ 8 * (1 + Real.log n + R) * (Real.exp (π * R) * (n : ℝ) ^ (-π)) := by
          gcongr
      _ = _ := by ring
  calc chmdPrimeWeight n * ‖dAlembertKernel ((Real.log n : ℂ) + v) +
        dAlembertKernel ((Real.log n : ℂ) - v)‖
      ≤ chmdPrimeWeight n * (8 * (1 + Real.log n + R) * Real.exp (π * R) * (n : ℝ) ^ (-π) +
          8 * (1 + Real.log n + R) * Real.exp (π * R) * (n : ℝ) ^ (-π)) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hA hB))
          (chmdPrimeWeight_nonneg n)
    _ = _ := by ring

theorem summable_primeTermC {v : ℂ} (hre : 0 ≤ v.re) : Summable fun n : ℕ => primeTermC n v := by
  refine Summable.of_norm_bounded_eventually
    ((summable_chmdPrimeWeight_mul_rpow ‖v‖ (norm_nonneg _)).mul_left 2) ?_
  have hev : ∀ᶠ n : ℕ in atTop, v.re + 3 / 4 < Real.log n := by
    filter_upwards [eventually_gt_atTop ⌈Real.exp (v.re + 3 / 4)⌉₊] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hn)
    rw [Real.lt_log_iff_exp_lt hn0]
    exact lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hn)
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hev] with n hn
  exact norm_primeTermC_le hre hn le_rfl

theorem primeDecay_nonneg (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ 8 * (1 + Real.log n + R) * Real.exp (π * R) * (n : ℝ) ^ (-π) :=
  mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (by linarith [Real.log_natCast_nonneg n])) (Real.exp_pos _).le)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- **Holomorphy of the prime wave with one term removed**, away from the other points `log n + i`. -/
theorem differentiableAt_primeTailC (n₀ : ℕ) {v₁ : ℂ} (hre : 0 < v₁.re) (him1 : -1 / 2 < v₁.im)
    (him2 : v₁.im < 3 / 2)
    (hpole : ∀ n, n ≠ n₀ → chmdPrimeWeight n ≠ 0 → v₁ ≠ (Real.log n : ℂ) + I) :
    DifferentiableAt ℂ (fun v => ∑' n : ℕ, if n = n₀ then 0 else primeTermC n v) v₁ := by
  set N := ⌈Real.exp (v₁.re + 1)⌉₊ with hN
  have hlogN : ∀ n : ℕ, N < n → v₁.re + 1 < Real.log n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hn)
    rw [Real.lt_log_iff_exp_lt hn0]
    exact lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hn)
  set S : Set ℂ := (fun n : ℕ => (Real.log n : ℂ) + I) ''
    {n | n ≤ N ∧ n ≠ n₀ ∧ chmdPrimeWeight n ≠ 0} with hS
  have hSfin : S.Finite := ((Set.finite_Iic N).subset fun n hn => hn.1).image _
  have hv₁S : v₁ ∉ S := by
    rintro ⟨n, ⟨-, hn0, hw⟩, hn⟩
    exact hpole n hn0 hw hn.symm
  obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.mp hSfin.isClosed.isOpen_compl v₁ hv₁S
  set r := min (min (ε / 2) (1 / 4)) (min (v₁.re / 2) (min ((v₁.im + 1 / 2) / 2) ((3 / 2 - v₁.im) / 2)))
    with hr
  have hr0 : 0 < r := lt_min (lt_min (by linarith) (by norm_num))
    (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have hcb : ∀ v ∈ closedBall v₁ r, v₁.re / 2 ≤ v.re ∧ v.re ≤ v₁.re + 1 / 4 ∧
      -1 / 2 < v.im ∧ v.im < 3 / 2 ∧ v ∉ S ∧ ‖v‖ ≤ ‖v₁‖ + 1 := by
    intro v hv
    have hn : ‖v - v₁‖ ≤ r := by rw [← dist_eq_norm]; exact mem_closedBall.mp hv
    have h1 := (Complex.abs_re_le_norm (v - v₁)).trans hn
    have h2 := (Complex.abs_im_le_norm (v - v₁)).trans hn
    rw [Complex.sub_re] at h1
    rw [Complex.sub_im] at h2
    have r1 : r ≤ ε / 2 := (min_le_left _ _).trans (min_le_left _ _)
    have r2 : r ≤ 1 / 4 := (min_le_left _ _).trans (min_le_right _ _)
    have r3 : r ≤ v₁.re / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have r4 : r ≤ (v₁.im + 1 / 2) / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _))
    have r5 : r ≤ (3 / 2 - v₁.im) / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _))
    refine ⟨by linarith [(abs_le.mp h1).1], by linarith [(abs_le.mp h1).2],
      by linarith [(abs_le.mp h2).1], by linarith [(abs_le.mp h2).2], fun hvS => ?_, ?_⟩
    · exact hεS (mem_ball.mpr (by rw [dist_eq_norm]; linarith)) hvS
    · have := norm_sub_norm_le v v₁
      linarith
  set F : ℕ → ℂ → ℂ := fun n v => if n = n₀ then 0 else primeTermC n v with hF
  have htermDiff : ∀ n, ∀ v ∈ closedBall v₁ r, DifferentiableAt ℂ (F n) v := by
    intro n v hv
    obtain ⟨hv1, hv2, hv3, hv4, hv5, -⟩ := hcb v hv
    by_cases hn : n = n₀
    · simp only [hF, hn, if_true]; exact differentiableAt_const _
    by_cases hw : chmdPrimeWeight n = 0
    · simp only [hF, hn, if_false, primeTermC_eq_zero_of_weight hw]
      exact differentiableAt_const _
    simp only [hF, hn, if_false]
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hd1 : DifferentiableAt ℂ dAlembertKernel ((Real.log n : ℂ) + v) :=
      differentiableAt_dAlembertKernel_of_re_pos (by rw [Complex.add_re, Complex.ofReal_re]; linarith)
    have hd2 : DifferentiableAt ℂ dAlembertKernel ((Real.log n : ℂ) - v) := by
      refine differentiableAt_dAlembertKernel (sinhSlope_log_sub_ne_zero ?_ hv3 hv4)
      by_cases hcon : v.re = Real.log n ∧ v.im = 1
      · exfalso
        obtain ⟨hre', him'⟩ := hcon
        have hvlog : v = (Real.log n : ℂ) + I := Complex.ext
          (by rw [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero, hre'])
          (by rw [Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add, him'])
        rcases Nat.lt_or_ge N n with hnN | hnN
        · have := hlogN n hnN; linarith
        · exact hv5 ⟨n, ⟨hnN, hn, hw⟩, hvlog.symm⟩
      · exact not_and_or.mp hcon
    exact (hd1.comp v (differentiableAt_id.const_add _)).add
      (hd2.comp v ((differentiableAt_const _).sub differentiableAt_id)) |>.const_mul _
  -- compactness bounds for every term, decay for the far terms
  have hcomp : ∀ n, ∃ M : ℝ, ∀ v ∈ closedBall v₁ r, ‖F n v‖ ≤ M := fun n =>
    (isCompact_closedBall v₁ r).exists_bound_of_continuousOn
      fun v hv => (htermDiff n v hv).continuousAt.continuousWithinAt
  choose M hM using hcomp
  set R₁ := ‖v₁‖ + 1
  have hdecay : ∀ n, N < n → ∀ v ∈ closedBall v₁ r, ‖F n v‖ ≤
      2 * (chmdPrimeWeight n * (8 * (1 + Real.log n + R₁) * Real.exp (π * R₁) * (n : ℝ) ^ (-π))) := by
    intro n hn v hv
    obtain ⟨hv1, hv2, -, -, -, hvn⟩ := hcb v hv
    have hlogn := hlogN n hn
    have hR1 : 0 ≤ R₁ := by positivity
    by_cases hn₀ : n = n₀
    · simp only [hF, hn₀, if_true, norm_zero]
      exact mul_nonneg zero_le_two (mul_nonneg (chmdPrimeWeight_nonneg _) (primeDecay_nonneg _ hR1))
    simp only [hF, hn₀, if_false]
    exact norm_primeTermC_le (by linarith) (by linarith) hvn
  set u : ℕ → ℝ := fun n => (if n ≤ N then M n else 0) +
    2 * (chmdPrimeWeight n * (8 * (1 + Real.log n + R₁) * Real.exp (π * R₁) * (n : ℝ) ^ (-π)))
    with hu
  have husum : Summable u := by
    refine Summable.add (summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => ?_)
      ((summable_chmdPrimeWeight_mul_rpow R₁ (by positivity)).mul_left 2)
    rw [Finset.mem_range, not_lt] at hn
    rw [if_neg (by omega)]
  have hub : ∀ n, ∀ v ∈ ball v₁ r, ‖F n v‖ ≤ u n := by
    intro n v hv
    have hvc := ball_subset_closedBall hv
    have hdec0 : 0 ≤ 2 * (chmdPrimeWeight n * (8 * (1 + Real.log n + R₁) * Real.exp (π * R₁) *
        (n : ℝ) ^ (-π))) :=
      mul_nonneg zero_le_two (mul_nonneg (chmdPrimeWeight_nonneg n)
        (primeDecay_nonneg n (by positivity)))
    by_cases hnN : n ≤ N
    · simp only [hu, if_pos hnN]
      linarith [hM n v hvc]
    · simp only [hu, if_neg hnN, zero_add]
      exact hdecay n (not_le.mp hnN) v hvc
  have hd := differentiableOn_tsum_of_summable_norm husum
    (fun n v hv => (htermDiff n v (ball_subset_closedBall hv)).differentiableWithinAt) isOpen_ball hub
  exact hd.differentiableAt (ball_mem_nhds v₁ hr0)

end RHTower.CHMDLightCone
