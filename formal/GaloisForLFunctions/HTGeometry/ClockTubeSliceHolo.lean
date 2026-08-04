import GaloisForLFunctions.HTGeometry.ClockTubeRetract
import GaloisForLFunctions.HTGeometry.ClockSeriesDerivative

/-!
# Slice holomorphy of the transverse Laplacian

The iteration integrates the step operator, and slice holomorphy passes through the integral; so what
remains is that the step operator itself is slice holomorphic. Its potential term is, being a product
of slice holomorphic functions. Its transverse Laplacian is the point of this file.

Along the coordinate being differentiated the statement is one-variable: the second partial
derivative restricted to that slice is the second derivative of the slice, and the derivative of a
holomorphic function is holomorphic.

Along a *different* coordinate the two variables are genuinely separate, and the argument is the
Cauchy representation: the second derivative in one coordinate is a contour integral of the function,
the integrand is holomorphic in the other coordinate, and holomorphy passes through the contour
integral by the one-variable statement already available.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-- Along the coordinate being differentiated, the second partial derivative is the second
derivative of the slice. -/
theorem cpartial_cpartial_update_same (i : Fin k) (w : (Fin k → ℂ) → ℂ) (z : Fin k → ℂ)
    (ζ : ℂ) :
    cpartial i (cpartial i w) (Function.update z i ζ)
      = deriv (deriv fun ξ : ℂ => w (Function.update z i ξ)) ζ := by
  have hfun : (fun ξ : ℂ => w (Function.update (Function.update z i ζ) i ξ))
      = fun ξ : ℂ => w (Function.update z i ξ) := by
    funext ξ
    rw [Function.update_idem]
  rw [cpartial_cpartial_eq, Function.update_self, hfun]

/-- Along a different coordinate, the second partial derivative is the second derivative of the
slice at the shifted point. -/
theorem cpartial_cpartial_update_other {i j : Fin k} (hij : i ≠ j) (w : (Fin k → ℂ) → ℂ)
    (z : Fin k → ℂ) (ζ : ℂ) :
    cpartial i (cpartial i w) (Function.update z j ζ)
      = deriv (deriv fun ξ : ℂ => w (Function.update (Function.update z i ξ) j ζ)) (z i) := by
  have hfun : (fun ξ : ℂ => w (Function.update (Function.update z j ζ) i ξ))
      = fun ξ : ℂ => w (Function.update (Function.update z i ξ) j ζ) := by
    funext ξ
    rw [Function.update_comm (Ne.symm hij)]
  rw [cpartial_cpartial_eq, Function.update_of_ne hij, hfun]

/-- **Slice holomorphy of the second partial derivative along the same coordinate**, on the same
tube: in one variable the derivative of a holomorphic function is holomorphic on the same open set. -/
theorem sliceHolo_cpartial_cpartial_same {ρ' : ℝ} {w : (Fin k → ℂ) → ℂ}
    (hwh : SliceHolo w ρ') (i : Fin k) {z : Fin k → ℂ} (hz : z ∈ tube k ρ') :
    DifferentiableOn ℂ (fun ζ : ℂ => cpartial i (cpartial i w) (Function.update z i ζ))
      (imStrip ρ') := by
  have hopen := isOpen_imStrip ρ'
  have hslice : DifferentiableOn ℂ (fun ξ : ℂ => w (Function.update z i ξ)) (imStrip ρ') :=
    hwh z hz i
  have hana : AnalyticOnNhd ℂ (fun ξ : ℂ => w (Function.update z i ξ)) (imStrip ρ') :=
    hslice.analyticOnNhd hopen
  have hd2 : DifferentiableOn ℂ (deriv (deriv fun ξ : ℂ => w (Function.update z i ξ)))
      (imStrip ρ') :=
    ((hana.deriv_of_isOpen hopen).deriv_of_isOpen hopen).differentiableOn
  refine hd2.congr fun ζ _ => ?_
  exact cpartial_cpartial_update_same i w z ζ

/-! ## The cross case -/

theorem continuous_update_update_fst (z : Fin k → ℂ) (i j : Fin k) (ζ : ℂ) :
    Continuous fun ξ : ℂ => Function.update (Function.update z i ξ) j ζ := by
  refine continuous_pi fun l => ?_
  by_cases hl : l = j
  · subst hl
    simp only [Function.update_self]
    exact continuous_const
  · simp only [Function.update_of_ne hl]
    by_cases hl' : l = i
    · subst hl'
      simp only [Function.update_self]
      exact continuous_id
    · simp only [Function.update_of_ne hl']
      exact continuous_const

theorem continuous_update_update_snd (z : Fin k → ℂ) (i j : Fin k) (ξ : ℂ) :
    Continuous fun ζ : ℂ => Function.update (Function.update z i ξ) j ζ :=
  (differentiable_updateSlice (Function.update z i ξ) j).continuous

/-- **Slice holomorphy of the second partial derivative along a different coordinate.**

The second derivative in the coordinate `i` is a contour integral of the function; the integrand is
holomorphic in the coordinate `j`, and holomorphy passes through the contour integral. -/
theorem sliceHolo_cpartial_cpartial_other {ρ' : ℝ}
    {w : (Fin k → ℂ) → ℂ} (hwc : ContinuousOn w (tube k ρ')) (hwh : SliceHolo w ρ')
    {i j : Fin k} (hij : i ≠ j) {z : Fin k → ℂ} (hz : z ∈ tube k ρ') :
    DifferentiableOn ℂ (fun ζ : ℂ => cpartial i (cpartial i w) (Function.update z j ζ))
      (imStrip ρ') := by
  classical
  set ρ : ℝ := |(z i).im| with hρdef
  have hρ : ρ < ρ' := by rw [hρdef]; exact hz i
  set R : ℝ := (ρ' - ρ) / 2 with hRdef
  have hRpos : (0 : ℝ) < R := by rw [hRdef]; linarith
  have hzi : |(z i).im| ≤ ρ := by rw [hρdef]
  have hdisc : closedBall (z i) R ⊆ imStrip ρ' := closedBall_subset_imStrip hρ hzi
  -- points obtained by updating two coordinates stay in the larger tube
  have hmem : ∀ ξ ∈ closedBall (z i) R, ∀ ζ ∈ imStrip ρ',
      Function.update (Function.update z i ξ) j ζ ∈ tube k ρ' := by
    intro ξ hξ ζ hζ l
    by_cases hl : l = j
    · subst hl
      rw [Function.update_self]
      exact mem_imStrip.mp hζ
    · rw [Function.update_of_ne hl]
      by_cases hl' : l = i
      · subst hl'
        rw [Function.update_self]
        exact mem_imStrip.mp (hdisc hξ)
      · rw [Function.update_of_ne hl']
        exact hz l
  -- the Cauchy representation of the second derivative, for each value of the other coordinate
  have hform : ∀ ζ ∈ imStrip ρ',
      cpartial i (cpartial i w) (Function.update z j ζ)
        = (2 * Real.pi * Complex.I / ((Nat.factorial 2 : ℕ) : ℂ))⁻¹
          • ∮ ξ in C(z i, R), (1 / (ξ - z i) ^ (2 + 1))
            • w (Function.update (Function.update z i ξ) j ζ) := by
    intro ζ hζ
    have hslice : ContinuousOn (fun ξ : ℂ => w (Function.update (Function.update z i ξ) j ζ))
        (closedBall (z i) R) :=
      hwc.comp (continuous_update_update_fst z i j ζ).continuousOn
        fun ξ hξ => hmem ξ hξ ζ hζ
    have hd : ∀ ξ ∈ ball (z i) R,
        DifferentiableAt ℂ (fun ξ' : ℂ => w (Function.update (Function.update z i ξ') j ζ)) ξ := by
      intro ξ hξ
      have hpt : Function.update z j ζ ∈ tube k ρ' := by
        intro l
        by_cases hl : l = j
        · subst hl
          rw [Function.update_self]
          exact mem_imStrip.mp hζ
        · rw [Function.update_of_ne hl]
          exact hz l
      have hslice' := hwh (Function.update z j ζ) hpt i
      have hξ' : ξ ∈ imStrip ρ' := hdisc (ball_subset_closedBall hξ)
      have hda := hslice'.differentiableAt ((isOpen_imStrip ρ').mem_nhds hξ')
      refine hda.congr_of_eventuallyEq ?_
      refine Filter.Eventually.of_forall fun ξ' => ?_
      show w (Function.update (Function.update z i ξ') j ζ)
        = w (Function.update (Function.update z j ζ) i ξ')
      rw [Function.update_comm hij]
    have hrep := iteratedDeriv_eq_circleIntegral hRpos 2 hslice hd
    rw [iteratedDeriv_two] at hrep
    rw [cpartial_cpartial_update_other hij w z ζ]
    exact hrep
  -- the contour integral is holomorphic in the other coordinate
  have hint : DifferentiableOn ℂ (fun ζ : ℂ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), (circleMap 0 R θ * Complex.I)
        • ((1 / (circleMap 0 R θ) ^ (2 + 1))
          • w (Function.update (Function.update z i (z i + circleMap 0 R θ)) j ζ)))
      (imStrip ρ') := by
    refine differentiableOn_intervalIntegral_of_holomorphic_on
      (F := fun θ ζ => (circleMap 0 R θ * Complex.I)
        • ((1 / (circleMap 0 R θ) ^ (2 + 1))
          • w (Function.update (Function.update z i (z i + circleMap 0 R θ)) j ζ))) ?_ ?_
    · intro q hq
      have hmemq : Function.update
          (Function.update z i (z i + circleMap 0 R q.1)) j q.2 ∈ tube k ρ' := by
        refine hmem (z i + circleMap 0 R q.1) ?_ q.2 hq.2
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_circleMap_zero,
          abs_of_pos hRpos]
      have hbase : ContinuousAt w
          (Function.update (Function.update z i (z i + circleMap 0 R q.1)) j q.2) :=
        hwc.continuousAt ((isOpen_tube k ρ').mem_nhds hmemq)
      have hmap : Continuous fun q' : ℝ × ℂ =>
          Function.update (Function.update z i (z i + circleMap 0 R q'.1)) j q'.2 := by
        refine continuous_pi fun l => ?_
        by_cases hl : l = j
        · subst hl
          simpa using continuous_snd
        · simp only [Function.update_of_ne hl]
          by_cases hl' : l = i
          · subst hl'
            simp only [Function.update_self]
            exact continuous_const.add ((continuous_circleMap 0 R).comp continuous_fst)
          · simpa [Function.update_of_ne hl'] using continuous_const
      have hcont : ContinuousAt (fun q' : ℝ × ℂ =>
          w (Function.update (Function.update z i (z i + circleMap 0 R q'.1)) j q'.2)) q :=
        hbase.comp (x := q) hmap.continuousAt
      have hc0 : ContinuousAt (fun q' : ℝ × ℂ => circleMap 0 R q'.1) q :=
        ((continuous_circleMap 0 R).comp continuous_fst).continuousAt
      have hden : ContinuousAt
          (fun q' : ℝ × ℂ => 1 / (circleMap 0 R q'.1) ^ (2 + 1)) q := by
        refine ContinuousAt.div continuousAt_const (hc0.pow (2 + 1)) ?_
        exact pow_ne_zero _ (circleMap_ne_center hRpos.ne')
      exact (((hc0.mul continuousAt_const).smul (hden.smul hcont))).continuousWithinAt
    · intro θ
      have hpt : Function.update z i (z i + circleMap 0 R θ) ∈ tube k ρ' := by
        intro l
        by_cases hl : l = i
        · subst hl
          rw [Function.update_self]
          refine mem_imStrip.mp (hdisc ?_)
          rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_circleMap_zero,
            abs_of_pos hRpos]
        · rw [Function.update_of_ne hl]
          exact hz l
      have hslice := hwh (Function.update z i (z i + circleMap 0 R θ)) hpt j
      exact (hslice.const_smul ((1 : ℂ) / (circleMap 0 R θ) ^ (2 + 1))).const_smul
        (circleMap 0 R θ * Complex.I)
  -- transport the representation
  have hEq : ∀ ζ ∈ imStrip ρ',
      (2 * Real.pi * Complex.I / ((Nat.factorial 2 : ℕ) : ℂ))⁻¹
        • ∮ ξ in C(z i, R), (1 / (ξ - z i) ^ (2 + 1))
          • w (Function.update (Function.update z i ξ) j ζ)
      = (2 * Real.pi * Complex.I / ((Nat.factorial 2 : ℕ) : ℂ))⁻¹
        • ∫ θ in (0 : ℝ)..(2 * Real.pi), (circleMap 0 R θ * Complex.I)
          • ((1 / (circleMap 0 R θ) ^ (2 + 1))
            • w (Function.update (Function.update z i (z i + circleMap 0 R θ)) j ζ)) := by
    intro ζ _
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    show deriv (circleMap (z i) R) θ
        • ((1 / (circleMap (z i) R θ - z i) ^ (2 + 1))
          • w (Function.update (Function.update z i (circleMap (z i) R θ)) j ζ))
      = (circleMap 0 R θ * Complex.I)
        • ((1 / (circleMap 0 R θ) ^ (2 + 1))
          • w (Function.update (Function.update z i (z i + circleMap 0 R θ)) j ζ))
    rw [deriv_circleMap, circleMap_sub_center, circleMap_eq_add (z i) R θ]
  refine DifferentiableOn.congr (hint.const_smul
    ((2 * Real.pi * Complex.I / ((Nat.factorial 2 : ℕ) : ℂ))⁻¹)) fun ζ hζ => ?_
  rw [hform ζ hζ, hEq ζ hζ]
  rfl

/-- **The step operator is slice holomorphic.** -/
theorem sliceHolo_tubeStep {ρ : ℝ} {V w : (Fin k → ℂ) → ℂ}
    (hVh : SliceHolo V ρ) (hwc : ContinuousOn w (tube k ρ)) (hwh : SliceHolo w ρ) :
    SliceHolo (tubeStep V w) ρ := by
  intro z hz j
  have hbase : DifferentiableOn ℂ
      (∑ i : Fin k, fun ζ : ℂ => cpartial i (cpartial i w) (Function.update z j ζ))
      (imStrip ρ) := by
    refine DifferentiableOn.sum (A := fun (i : Fin k) (ζ : ℂ) =>
      cpartial i (cpartial i w) (Function.update z j ζ)) fun i _ => ?_
    by_cases hij : i = j
    · subst hij
      exact sliceHolo_cpartial_cpartial_same hwh i hz
    · exact sliceHolo_cpartial_cpartial_other hwc hwh hij hz
  have hsum : DifferentiableOn ℂ
      (fun ζ : ℂ => ∑ i, cpartial i (cpartial i w) (Function.update z j ζ)) (imStrip ρ) := by
    have heq : (∑ i : Fin k, fun ζ : ℂ => cpartial i (cpartial i w) (Function.update z j ζ))
        = fun ζ : ℂ => ∑ i, cpartial i (cpartial i w) (Function.update z j ζ) := by
      funext ζ
      simp [Finset.sum_apply]
    rwa [heq] at hbase
  exact ((hsum.add ((hVh z hz j).mul (hwh z hz j))).div_const 4)

end GaloisForLFunctions.HTGeometry
