import GaloisForLFunctions.HTGeometry.ExponentialLagrangeContour
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import Mathlib.Analysis.Calculus.MeanValue

/-! # Entire contour projectors for groups of multiple zeros

The divided difference fills the moving diagonal before integration. Thus a
contour selects a whole divisor group without separating its zeros or choosing
individual residues. This file supplies the entire kernel and its Cauchy laws.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Interval

namespace HTGeometry
noncomputable section

theorem dslope_symm (f : ℂ → ℂ) (a b : ℂ) :
    dslope f a b = dslope f b a := by
  by_cases h : b = a
  · subst b; rfl
  · rw [dslope_of_ne _ h, dslope_of_ne _ (Ne.symm h), slope_comm]

theorem differentiable_entire_dslope {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (a : ℂ) : Differentiable ℂ (dslope f a) := by
  rw [← differentiableOn_univ]
  exact (differentiableOn_dslope (s := univ) univ_mem).mpr hf.differentiableOn

theorem norm_dslope_le_on_convex {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {S : Set ℂ} (hS : Convex ℝ S) {C : ℝ}
    (hC : ∀ z ∈ S, ‖deriv f z‖ ≤ C) {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) :
    ‖dslope f a b‖ ≤ C := by
  by_cases h : b = a
  · subst b; simpa using hC a ha
  · rw [dslope_of_ne _ h, slope_def_field, norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr h))).mpr
    exact hS.norm_image_sub_le_of_norm_deriv_le (fun z _ => hf z) hC ha hb

/-- Local holomorphic dependence under a compact interval integral. -/
theorem differentiableAt_intervalIntegral_of_bound
    {F : ℂ → ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) {z₀ : ℂ} {R C : ℝ}
    (hR : 0 < R) (hc : ∀ z ∈ ball z₀ R, ContinuousOn (F z) (Icc a b))
    (hd : ∀ t ∈ Icc a b, DifferentiableOn ℂ (fun z => F z t) (ball z₀ R))
    (hC : ∀ t ∈ Icc a b, ∀ z ∈ ball z₀ R, ‖F z t‖ ≤ C) :
    DifferentiableAt ℂ (fun z => ∫ t in a..b, F z t) z₀ := by
  classical
  have hi := GaloisForLFunctions.HTGeometry.differentiableAt_integral_of_cauchy_dominated
    (μ := volume)
    (F := fun z => (Ioc a b).indicator (F z))
    (bound := (Ioc a b).indicator (fun _ => C)) hR
    (fun z hz => (aestronglyMeasurable_indicator_iff measurableSet_Ioc).mpr
      (((hc z hz).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc))
    (fun t => by
      by_cases ht : t ∈ Ioc a b
      · simpa only [indicator_of_mem ht] using
          (hd t (Ioc_subset_Icc_self ht))
      · simpa only [indicator_of_notMem ht] using
          (differentiable_const (c := (0 : ℂ))).differentiableOn)
    (fun t z hz => by
      by_cases ht : t ∈ Ioc a b
      · simpa only [indicator_of_mem ht] using hC t (Ioc_subset_Icc_self ht) z hz
      · simp only [indicator_of_notMem ht, norm_zero, le_refl])
    ((integrable_indicator_iff measurableSet_Ioc).mpr
      (integrableOn_const (by simp [Real.volume_Ioc])))
  simpa only [integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le hab] using hi

/-- Domination may depend on a neighbourhood of the complex parameter. -/
theorem differentiable_intervalIntegral_of_local_bound
    {F : ℂ → ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ z, ContinuousOn (F z) (Icc a b))
    (hd : ∀ t ∈ Icc a b, Differentiable ℂ (fun z => F z t))
    (hb : ∀ z₀ : ℂ, ∃ R C : ℝ, 0 < R ∧
      ∀ t ∈ Icc a b, ∀ z ∈ ball z₀ R, ‖F z t‖ ≤ C) :
    Differentiable ℂ (fun z => ∫ t in a..b, F z t) := by
  intro z₀
  obtain ⟨R, C, hR, hC⟩ := hb z₀
  exact differentiableAt_intervalIntegral_of_bound hab hR (fun z _ => hc z)
    (fun t ht => (hd t ht).differentiableOn) hC

/-- Integration of the entire divided difference along any compact continuous
arc preserves entireness, including points lying on the arc. -/
theorem differentiable_intervalIntegral_dslope
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {A γ : ℝ → ℂ}
    {a b : ℝ} (hab : a ≤ b) (hA : ContinuousOn A (Icc a b))
    (hγ : ContinuousOn γ (Icc a b)) :
    Differentiable ℂ (fun z => ∫ t in a..b, A t * dslope f (γ t) z) := by
  apply differentiable_intervalIntegral_of_local_bound hab
  · intro z
    simp_rw [dslope_symm f _ z]
    exact hA.mul ((differentiable_entire_dslope hf z).continuous.comp_continuousOn hγ)
  · intro t _
    exact (differentiable_entire_dslope hf (γ t)).const_mul (A t)
  · intro z₀
    obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hγ
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
    let R := max D (‖z₀‖ + 1)
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
      hf.deriv.continuous.continuousOn
    refine ⟨1, |M| * |C|, zero_lt_one, fun t ht z hz => ?_⟩
    have hγR : γ t ∈ closedBall (0 : ℂ) R := by
      rw [mem_closedBall, dist_zero_right]
      exact (hD t ht).trans (le_max_left _ _)
    have hzR : z ∈ closedBall (0 : ℂ) R := by
      rw [mem_closedBall, dist_zero_right]
      have hz' : ‖z - z₀‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hz
      have hn := norm_add_le (z - z₀) z₀
      simp only [sub_add_cancel] at hn
      have : ‖z‖ ≤ ‖z₀‖ + 1 := by linarith
      exact this.trans (le_max_right _ _)
    rw [norm_mul]
    exact mul_le_mul ((hM t ht).trans (le_abs_self _))
      ((norm_dslope_le_on_convex hf (convex_closedBall _ _) hC hγR hzR).trans
        (le_abs_self _)) (norm_nonneg _) (abs_nonneg _)

/-- Entire spectral selection kernel. No zero enumeration is used. -/
def entireDividedDifferenceContour (f A : ℂ → ℂ) (a b z : ℂ) : ℂ :=
  RectangleIntegral' (fun w => A w * dslope f w z) a b

theorem differentiable_entireDividedDifferenceContour
    {f A : ℂ → ℂ} (hf : Differentiable ℂ f) {a b : ℂ}
    (hab : a.re ≤ b.re) (hab' : a.im ≤ b.im)
    (hA : ContinuousOn A (RectangleBorder a b)) :
    Differentiable ℂ (entireDividedDifferenceContour f A a b) := by
  have hbottom : MapsTo (fun t : ℝ => (t : ℂ) + a.im * I)
      (Icc a.re b.re) (RectangleBorder a b) := by
    simpa only [uIcc_of_le hab] using mapsTo_rectangleBorder_left_im a b
  have htop : MapsTo (fun t : ℝ => (t : ℂ) + b.im * I)
      (Icc a.re b.re) (RectangleBorder a b) := by
    simpa only [uIcc_of_le hab] using mapsTo_rectangleBorder_right_im a b
  have hleft : MapsTo (fun t : ℝ => (a.re : ℂ) + t * I)
      (Icc a.im b.im) (RectangleBorder a b) := by
    simpa only [uIcc_of_le hab'] using mapsTo_rectangleBorder_left_re a b
  have hright : MapsTo (fun t : ℝ => (b.re : ℂ) + t * I)
      (Icc a.im b.im) (RectangleBorder a b) := by
    simpa only [uIcc_of_le hab'] using mapsTo_rectangleBorder_right_re a b
  have hB := differentiable_intervalIntegral_dslope hf
    (γ := fun t : ℝ => (t : ℂ) + a.im * I)
    (A := fun t : ℝ => A ((t : ℂ) + a.im * I)) hab
    (hA.comp (by fun_prop) hbottom) (by fun_prop)
  have hT := differentiable_intervalIntegral_dslope hf
    (γ := fun t : ℝ => (t : ℂ) + b.im * I)
    (A := fun t : ℝ => A ((t : ℂ) + b.im * I)) hab
    (hA.comp (by fun_prop) htop) (by fun_prop)
  have hL := differentiable_intervalIntegral_dslope hf
    (γ := fun t : ℝ => (a.re : ℂ) + t * I)
    (A := fun t : ℝ => A ((a.re : ℂ) + t * I)) hab'
    (hA.comp (by fun_prop) hleft) (by fun_prop)
  have hR := differentiable_intervalIntegral_dslope hf
    (γ := fun t : ℝ => (b.re : ℂ) + t * I)
    (A := fun t : ℝ => A ((b.re : ℂ) + t * I)) hab'
    (hA.comp (by fun_prop) hright) (by fun_prop)
  exact ((hB.sub hT).add (hR.const_mul I) |>.sub (hL.const_mul I)).const_mul _

end
end HTGeometry
