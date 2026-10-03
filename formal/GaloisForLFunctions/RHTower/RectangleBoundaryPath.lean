import GaloisForLFunctions.HTGeometry.RectangleResidue
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# The boundary of a rectangle as a periodic piecewise linear loop

For corners `z₁` (lower left) and `z₂` (upper right) the positively oriented boundary of the
axis-parallel rectangle is traversed in four quarter-times: bottom edge left to right, right edge
upwards, top edge right to left, left edge downwards.  Extending by `1`-periodicity gives a
continuous loop `γ : ℝ → ℂ`, affine off the corner times `ℤ/4`, with piecewise constant velocity.
Its line integral is the corpus rectangle contour integral:

`∫₀¹ g(γ t) γ'(t) dt = rectIntegral g z₁ z₂`.
-/

noncomputable section

open Complex MeasureTheory intervalIntegral Set Filter Topology
open scoped Real

namespace RHTower

/-- The four edges of the rectangle boundary on the fundamental interval. -/
def rectangleEdgePath (z₁ z₂ : ℂ) (τ : ℝ) : ℂ :=
  if τ ≤ 1 / 4 then ((z₁.re + 4 * τ * (z₂.re - z₁.re) : ℝ) : ℂ) + z₁.im * I
  else if τ ≤ 1 / 2 then (z₂.re : ℂ) + ((z₁.im + (4 * τ - 1) * (z₂.im - z₁.im) : ℝ) : ℂ) * I
  else if τ ≤ 3 / 4 then ((z₂.re - (4 * τ - 2) * (z₂.re - z₁.re) : ℝ) : ℂ) + z₂.im * I
  else (z₁.re : ℂ) + ((z₂.im - (4 * τ - 3) * (z₂.im - z₁.im) : ℝ) : ℂ) * I

/-- The edge velocities on the fundamental interval. -/
def rectangleEdgeVelocity (z₁ z₂ : ℂ) (τ : ℝ) : ℂ :=
  if τ ≤ 1 / 4 then ((4 * (z₂.re - z₁.re) : ℝ) : ℂ)
  else if τ ≤ 1 / 2 then ((4 * (z₂.im - z₁.im) : ℝ) : ℂ) * I
  else if τ ≤ 3 / 4 then -((4 * (z₂.re - z₁.re) : ℝ) : ℂ)
  else -((4 * (z₂.im - z₁.im) : ℝ) : ℂ) * I

/-- The periodic rectangle boundary loop. -/
def rectangleBoundaryPath (z₁ z₂ : ℂ) (t : ℝ) : ℂ := rectangleEdgePath z₁ z₂ (Int.fract t)

/-- The periodic boundary velocity. -/
def rectangleBoundaryVelocity (z₁ z₂ : ℂ) (t : ℝ) : ℂ :=
  rectangleEdgeVelocity z₁ z₂ (Int.fract t)

/-- Corner times `ℤ / 4`. -/
def rectangleCornerTimes : Set ℝ := Set.range fun k : ℤ => (k : ℝ) / 4

theorem countable_rectangleCornerTimes : rectangleCornerTimes.Countable :=
  Set.countable_range _

variable (z₁ z₂ : ℂ)

theorem continuous_rectangleEdgePath : Continuous (rectangleEdgePath z₁ z₂) := by
  unfold rectangleEdgePath
  refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const ?_
  · refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const ?_
    · refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const ?_
      intro x hx
      rw [hx]
      apply Complex.ext <;> simp <;> ring
    · intro x hx
      rw [hx, if_pos (by norm_num)]
      apply Complex.ext <;> simp <;> ring
  · intro x hx
    rw [hx, if_pos (by norm_num)]
    apply Complex.ext <;> simp

theorem rectangleEdgePath_zero : rectangleEdgePath z₁ z₂ 0 = z₁ := by
  apply Complex.ext <;> simp [rectangleEdgePath]

theorem rectangleEdgePath_one : rectangleEdgePath z₁ z₂ 1 = z₁ := by
  apply Complex.ext <;> norm_num [rectangleEdgePath]

theorem continuous_rectangleBoundaryPath : Continuous (rectangleBoundaryPath z₁ z₂) := by
  have h := ContinuousOn.comp_fract (s := fun t : ℝ => t) (f := fun _ : ℝ => rectangleEdgePath z₁ z₂)
    ((continuous_rectangleEdgePath z₁ z₂).comp continuous_snd).continuousOn continuous_id
    (fun _ => by rw [rectangleEdgePath_zero, rectangleEdgePath_one])
  exact h

theorem periodic_rectangleBoundaryPath : Function.Periodic (rectangleBoundaryPath z₁ z₂) 1 := by
  intro t
  simp [rectangleBoundaryPath, Int.fract_add_one]

theorem periodic_rectangleBoundaryVelocity :
    Function.Periodic (rectangleBoundaryVelocity z₁ z₂) 1 := by
  intro t
  simp [rectangleBoundaryVelocity, Int.fract_add_one]

theorem measurable_rectangleBoundaryVelocity :
    Measurable (rectangleBoundaryVelocity z₁ z₂) := by
  unfold rectangleBoundaryVelocity rectangleEdgeVelocity
  refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const
    (Measurable.ite ?_ measurable_const measurable_const))
  all_goals exact measurableSet_le measurable_fract measurable_const

/-- The velocity is bounded by `4 (|Δx| + |Δy|)`. -/
theorem norm_rectangleBoundaryVelocity_le (t : ℝ) :
    ‖rectangleBoundaryVelocity z₁ z₂ t‖ ≤ 4 * (|z₂.re - z₁.re| + |z₂.im - z₁.im|) := by
  unfold rectangleBoundaryVelocity rectangleEdgeVelocity
  have h1 : 0 ≤ |z₂.re - z₁.re| := abs_nonneg _
  have h2 : 0 ≤ |z₂.im - z₁.im| := abs_nonneg _
  split_ifs <;>
    simp only [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 4)] <;> nlinarith

theorem rectangleCornerTimes_of_fract {t : ℝ} (ht : t ∉ rectangleCornerTimes) :
    0 < Int.fract t ∧ Int.fract t ≠ 1 / 4 ∧ Int.fract t ≠ 1 / 2 ∧ Int.fract t ≠ 3 / 4 := by
  have hfr := Int.floor_add_fract t
  refine ⟨lt_of_le_of_ne (Int.fract_nonneg t) fun h => ht ⟨4 * ⌊t⌋, ?_⟩, fun h => ht ⟨4 * ⌊t⌋ + 1, ?_⟩,
    fun h => ht ⟨4 * ⌊t⌋ + 2, ?_⟩, fun h => ht ⟨4 * ⌊t⌋ + 3, ?_⟩⟩
  all_goals push_cast; linarith

/-- Off the corner times the boundary loop is differentiable with the edge velocity. -/
theorem hasDerivAt_rectangleBoundaryPath {t : ℝ} (ht : t ∉ rectangleCornerTimes) :
    HasDerivAt (rectangleBoundaryPath z₁ z₂) (rectangleBoundaryVelocity z₁ z₂ t) t := by
  obtain ⟨h0, h1, h2, h3⟩ := rectangleCornerTimes_of_fract ht
  have hlt : Int.fract t < 1 := Int.fract_lt_one t
  set k : ℤ := ⌊t⌋
  have hloc : ∀ᶠ y : ℝ in 𝓝 t, Int.fract y = y - (k : ℝ) := by
    have hmem : Ioo (k : ℝ) (k + 1) ∈ 𝓝 t := by
      refine Ioo_mem_nhds ?_ ?_
      · have := Int.floor_add_fract t; linarith
      · have := Int.floor_add_fract t; linarith
    filter_upwards [hmem] with y hy
    rw [Int.fract, Int.floor_eq_iff.2 ⟨hy.1.le, hy.2⟩]
  have hft : Int.fract t = t - k := by rw [Int.fract]
  have hshift : HasDerivAt (fun y : ℝ => y - k) 1 t := (hasDerivAt_id t).sub_const _
  -- The edge path is affine near `fract t`.
  have hedge : HasDerivAt (rectangleEdgePath z₁ z₂) (rectangleEdgeVelocity z₁ z₂ (Int.fract t))
      (Int.fract t) := by
    rcases lt_or_gt_of_ne h1 with hq | hq
    · have hev : rectangleEdgePath z₁ z₂ =ᶠ[𝓝 (Int.fract t)]
          fun τ => ((z₁.re + 4 * τ * (z₂.re - z₁.re) : ℝ) : ℂ) + z₁.im * I := by
        filter_upwards [Iio_mem_nhds hq] with τ hτ
        rw [rectangleEdgePath, if_pos (le_of_lt hτ)]
      have hv : rectangleEdgeVelocity z₁ z₂ (Int.fract t) = ((4 * (z₂.re - z₁.re) : ℝ) : ℂ) := by
        rw [rectangleEdgeVelocity, if_pos hq.le]
      rw [hv]
      refine HasDerivAt.congr_of_eventuallyEq ?_ hev
      have hlin : HasDerivAt (fun τ : ℝ => z₁.re + 4 * τ * (z₂.re - z₁.re))
          (4 * (z₂.re - z₁.re)) (Int.fract t) := by
        have := ((hasDerivAt_id (Int.fract t)).const_mul 4).mul_const (z₂.re - z₁.re)
        simpa using this.const_add z₁.re
      exact hlin.ofReal_comp.add_const ((z₁.im : ℂ) * I)
    rcases lt_or_gt_of_ne h2 with hq2 | hq2
    · have hev : rectangleEdgePath z₁ z₂ =ᶠ[𝓝 (Int.fract t)]
          fun τ => (z₂.re : ℂ) + ((z₁.im + (4 * τ - 1) * (z₂.im - z₁.im) : ℝ) : ℂ) * I := by
        filter_upwards [Ioo_mem_nhds hq hq2] with τ hτ
        rw [rectangleEdgePath, if_neg (not_le.2 hτ.1), if_pos (le_of_lt hτ.2)]
      have hv : rectangleEdgeVelocity z₁ z₂ (Int.fract t) =
          ((4 * (z₂.im - z₁.im) : ℝ) : ℂ) * I := by
        rw [rectangleEdgeVelocity, if_neg (not_le.2 hq), if_pos hq2.le]
      rw [hv]
      refine HasDerivAt.congr_of_eventuallyEq ?_ hev
      have hlin : HasDerivAt (fun τ : ℝ => z₁.im + (4 * τ - 1) * (z₂.im - z₁.im))
          (4 * (z₂.im - z₁.im)) (Int.fract t) := by
        have := (((hasDerivAt_id (Int.fract t)).const_mul 4).sub_const 1).mul_const
          (z₂.im - z₁.im)
        simpa using this.const_add z₁.im
      have := (hlin.ofReal_comp.mul_const I).const_add (z₂.re : ℂ)
      simpa using this
    rcases lt_or_gt_of_ne h3 with hq3 | hq3
    · have hev : rectangleEdgePath z₁ z₂ =ᶠ[𝓝 (Int.fract t)]
          fun τ => ((z₂.re - (4 * τ - 2) * (z₂.re - z₁.re) : ℝ) : ℂ) + z₂.im * I := by
        filter_upwards [Ioo_mem_nhds hq2 hq3] with τ hτ
        rw [rectangleEdgePath, if_neg (by linarith [hτ.1]), if_neg (not_le.2 hτ.1),
          if_pos (le_of_lt hτ.2)]
      have hv : rectangleEdgeVelocity z₁ z₂ (Int.fract t) =
          -((4 * (z₂.re - z₁.re) : ℝ) : ℂ) := by
        rw [rectangleEdgeVelocity, if_neg (by linarith), if_neg (not_le.2 hq2), if_pos hq3.le]
      rw [hv]
      refine HasDerivAt.congr_of_eventuallyEq ?_ hev
      have hlin : HasDerivAt (fun τ : ℝ => z₂.re - (4 * τ - 2) * (z₂.re - z₁.re))
          (-(4 * (z₂.re - z₁.re))) (Int.fract t) := by
        have := (((hasDerivAt_id (Int.fract t)).const_mul 4).sub_const 2).mul_const
          (z₂.re - z₁.re)
        simpa using this.const_sub z₂.re
      have := hlin.ofReal_comp.add_const ((z₂.im : ℂ) * I)
      simpa using this
    · have hev : rectangleEdgePath z₁ z₂ =ᶠ[𝓝 (Int.fract t)]
          fun τ => (z₁.re : ℂ) + ((z₂.im - (4 * τ - 3) * (z₂.im - z₁.im) : ℝ) : ℂ) * I := by
        filter_upwards [Ioi_mem_nhds hq3] with τ hτ
        have hτ' : 3 / 4 < τ := hτ
        rw [rectangleEdgePath, if_neg (by linarith), if_neg (by linarith),
          if_neg (not_le.2 hτ')]
      have hv : rectangleEdgeVelocity z₁ z₂ (Int.fract t) =
          -((4 * (z₂.im - z₁.im) : ℝ) : ℂ) * I := by
        rw [rectangleEdgeVelocity, if_neg (by linarith), if_neg (by linarith),
          if_neg (not_le.2 hq3)]
      rw [hv]
      refine HasDerivAt.congr_of_eventuallyEq ?_ hev
      have hlin : HasDerivAt (fun τ : ℝ => z₂.im - (4 * τ - 3) * (z₂.im - z₁.im))
          (-(4 * (z₂.im - z₁.im))) (Int.fract t) := by
        have := (((hasDerivAt_id (Int.fract t)).const_mul 4).sub_const 3).mul_const
          (z₂.im - z₁.im)
        simpa using this.const_sub z₂.im
      have := (hlin.ofReal_comp.mul_const I).const_add (z₁.re : ℂ)
      convert this using 1
      push_cast; ring
  have hcomp : HasDerivAt (fun y => rectangleEdgePath z₁ z₂ (y - k))
      (rectangleEdgeVelocity z₁ z₂ (Int.fract t)) t := by
    have := HasDerivAt.scomp_of_eq t hedge hshift hft.symm
    rw [one_smul] at this
    exact this
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hloc] with y hy
  rw [rectangleBoundaryPath, hy]

/-! ## The line integral along the loop -/

theorem intervalIntegrable_mul_rectangleBoundaryVelocity {h : ℝ → ℂ} (hh : Continuous h)
    (a b : ℝ) :
    IntervalIntegrable (fun t => h t * rectangleBoundaryVelocity z₁ z₂ t) volume a b := by
  have key : ∀ {a b : ℝ}, a ≤ b →
      IntervalIntegrable (fun t => h t * rectangleBoundaryVelocity z₁ z₂ t) volume a b := by
    intro a b hab
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
      hh.continuousOn
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 ?_
    refine Measure.integrableOn_of_bounded
      (M := M * (4 * (|z₂.re - z₁.re| + |z₂.im - z₁.im|))) (by simp)
      (hh.measurable.mul (measurable_rectangleBoundaryVelocity z₁ z₂)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [norm_mul]
    exact mul_le_mul (hM x hx) (norm_rectangleBoundaryVelocity_le z₁ z₂ x) (norm_nonneg _)
      ((norm_nonneg _).trans (hM x hx))
  rcases le_total a b with hab | hab
  · exact key hab
  · exact (key hab).symm

private theorem fract_eq_of_mem {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : Int.fract t = t :=
  Int.fract_eq_self.2 ⟨h0, h1⟩

/-- **The loop computes the rectangle contour integral**:
`∫₀¹ g(γ t) γ'(t) dt = rectIntegral g z₁ z₂`. -/
theorem integral_rectangleBoundary_eq_rectIntegral (g : ℂ → ℂ)
    (hg : Continuous fun t => g (rectangleBoundaryPath z₁ z₂ t)) :
    ∫ t in (0 : ℝ)..1, g (rectangleBoundaryPath z₁ z₂ t) * rectangleBoundaryVelocity z₁ z₂ t =
      rectIntegral g z₁ z₂ := by
  set F : ℝ → ℂ := fun t => g (rectangleBoundaryPath z₁ z₂ t) * rectangleBoundaryVelocity z₁ z₂ t
  have hF : ∀ a b, IntervalIntegrable F volume a b :=
    intervalIntegrable_mul_rectangleBoundaryVelocity z₁ z₂ hg
  have hsplit : ∫ t in (0 : ℝ)..1, F t = (∫ t in (0 : ℝ)..1 / 4, F t) +
      (∫ t in (1 / 4 : ℝ)..1 / 2, F t) + (∫ t in (1 / 2 : ℝ)..3 / 4, F t) +
        ∫ t in (3 / 4 : ℝ)..1, F t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hF _ _) (hF _ _),
      intervalIntegral.integral_add_adjacent_intervals (hF _ _) (hF _ _),
      intervalIntegral.integral_add_adjacent_intervals (hF _ _) (hF _ _)]
  -- bottom edge
  have hq1 : ∫ t in (0 : ℝ)..1 / 4, F t = ∫ x in z₁.re..z₂.re, g ((x : ℂ) + z₁.im * I) := by
    have hpt : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) (1 / 4) →
        F t = (4 * (z₂.re - z₁.re) : ℝ) • g (((4 * (z₂.re - z₁.re) * t + z₁.re : ℝ) : ℂ) + z₁.im * I) := by
      refine Eventually.of_forall fun t ht => ?_
      rw [uIoc_of_le (by norm_num)] at ht
      have hfr := fract_eq_of_mem ht.1.le (by linarith [ht.2])
      simp only [F, rectangleBoundaryPath, rectangleBoundaryVelocity, rectangleEdgePath,
        rectangleEdgeVelocity, hfr, if_pos ht.2, Complex.real_smul]
      rw [mul_comm]
      congr 3
      ring
    rw [intervalIntegral.integral_congr_ae hpt, intervalIntegral.integral_smul,
      intervalIntegral.smul_integral_comp_mul_add (fun x : ℝ => g ((x : ℂ) + z₁.im * I))]
    congr 1 <;> ring
  -- right edge
  have hq2 : ∫ t in (1 / 4 : ℝ)..1 / 2, F t =
      I • ∫ y in z₁.im..z₂.im, g ((z₂.re : ℂ) + y * I) := by
    have hpt : ∀ᵐ t ∂volume, t ∈ uIoc (1 / 4 : ℝ) (1 / 2) →
        F t = I • ((4 * (z₂.im - z₁.im) : ℝ) • g ((z₂.re : ℂ) + ((4 * (z₂.im - z₁.im) * t + (z₁.im - (z₂.im - z₁.im)) : ℝ) : ℂ) * I)) := by
      refine Eventually.of_forall fun t ht => ?_
      rw [uIoc_of_le (by norm_num)] at ht
      have hfr := fract_eq_of_mem (by linarith [ht.1]) (by linarith [ht.2])
      simp only [F, rectangleBoundaryPath, rectangleBoundaryVelocity, rectangleEdgePath,
        rectangleEdgeVelocity, hfr, if_neg (not_le.2 ht.1), if_pos ht.2, Complex.real_smul,
        smul_eq_mul]
      have : ((z₁.im + (4 * t - 1) * (z₂.im - z₁.im) : ℝ) : ℂ) =
          ((4 * (z₂.im - z₁.im) * t + (z₁.im - (z₂.im - z₁.im)) : ℝ) : ℂ) := by congr 1; ring
      rw [this]
      ring
    rw [intervalIntegral.integral_congr_ae hpt, intervalIntegral.integral_smul,
      intervalIntegral.integral_smul,
      intervalIntegral.smul_integral_comp_mul_add (fun y : ℝ => g ((z₂.re : ℂ) + y * I))]
    congr 2 <;> ring
  -- top edge
  have hq3 : ∫ t in (1 / 2 : ℝ)..3 / 4, F t = -∫ x in z₁.re..z₂.re, g ((x : ℂ) + z₂.im * I) := by
    have hpt : ∀ᵐ t ∂volume, t ∈ uIoc (1 / 2 : ℝ) (3 / 4) →
        F t = (-(4 * (z₂.re - z₁.re)) : ℝ) • g (((-(4 * (z₂.re - z₁.re)) * t + (z₂.re + 2 * (z₂.re - z₁.re)) : ℝ) : ℂ) + z₂.im * I) := by
      refine Eventually.of_forall fun t ht => ?_
      rw [uIoc_of_le (by norm_num)] at ht
      have hfr := fract_eq_of_mem (by linarith [ht.1]) (by linarith [ht.2])
      simp only [F, rectangleBoundaryPath, rectangleBoundaryVelocity, rectangleEdgePath,
        rectangleEdgeVelocity, hfr, if_neg (show ¬ t ≤ 1 / 4 by linarith [ht.1]),
        if_neg (not_le.2 ht.1), if_pos ht.2, Complex.real_smul]
      have : ((z₂.re - (4 * t - 2) * (z₂.re - z₁.re) : ℝ) : ℂ) =
          ((-(4 * (z₂.re - z₁.re)) * t + (z₂.re + 2 * (z₂.re - z₁.re)) : ℝ) : ℂ) := by congr 1; ring
      rw [this]
      push_cast
      ring
    rw [intervalIntegral.integral_congr_ae hpt, intervalIntegral.integral_smul,
      intervalIntegral.smul_integral_comp_mul_add (fun x : ℝ => g ((x : ℂ) + z₂.im * I)),
      ← intervalIntegral.integral_symm]
    congr 1 <;> ring
  -- left edge
  have hq4 : ∫ t in (3 / 4 : ℝ)..1, F t =
      -(I • ∫ y in z₁.im..z₂.im, g ((z₁.re : ℂ) + y * I)) := by
    have hpt : ∀ᵐ t ∂volume, t ∈ uIoc (3 / 4 : ℝ) 1 →
        F t = I • ((-(4 * (z₂.im - z₁.im)) : ℝ) • g ((z₁.re : ℂ) +
          ((-(4 * (z₂.im - z₁.im)) * t + (z₂.im + 3 * (z₂.im - z₁.im)) : ℝ) : ℂ) * I)) := by
      have hnull : volume ({1} : Set ℝ) = 0 := measure_singleton 1
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with t hne ht
      rw [uIoc_of_le (by norm_num)] at ht
      have ht1 : t < 1 := lt_of_le_of_ne ht.2 hne
      have hfr := fract_eq_of_mem (by linarith [ht.1]) ht1
      simp only [F, rectangleBoundaryPath, rectangleBoundaryVelocity, rectangleEdgePath,
        rectangleEdgeVelocity, hfr, if_neg (show ¬ t ≤ 1 / 4 by linarith [ht.1]),
        if_neg (show ¬ t ≤ 1 / 2 by linarith [ht.1]), if_neg (not_le.2 ht.1),
        Complex.real_smul, smul_eq_mul]
      have : ((z₂.im - (4 * t - 3) * (z₂.im - z₁.im) : ℝ) : ℂ) =
          ((-(4 * (z₂.im - z₁.im)) * t + (z₂.im + 3 * (z₂.im - z₁.im)) : ℝ) : ℂ) := by congr 1; ring
      rw [this]
      push_cast
      ring
    rw [intervalIntegral.integral_congr_ae hpt, intervalIntegral.integral_smul,
      intervalIntegral.integral_smul,
      intervalIntegral.smul_integral_comp_mul_add (fun y : ℝ => g ((z₁.re : ℂ) + y * I)),
      ← smul_neg, ← intervalIntegral.integral_symm]
    congr 2 <;> ring
  rw [hsplit, hq1, hq2, hq3, hq4, rectIntegral]
  abel

end RHTower
