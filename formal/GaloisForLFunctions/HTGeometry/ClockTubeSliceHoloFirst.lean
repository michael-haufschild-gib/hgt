import GaloisForLFunctions.HTGeometry.ClockTubeSliceHolo

/-!
# Slice holomorphy of a single transverse partial derivative

The Laplacian of the tube is slice holomorphic; so is each first partial derivative separately, by
the same two arguments. Along the coordinate being differentiated the statement is one-variable —
the derivative of a holomorphic function is holomorphic on the same open set. Along a different
coordinate it is the Cauchy representation of the first derivative, whose integrand is holomorphic in
the other coordinate.

This is what the real chart needs: it reads the partial derivatives of the field one at a time, and
each of them must again be slice holomorphic for the next derivative to exist.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-- Along the coordinate being differentiated, the partial derivative is the derivative of the
slice. -/
theorem cpartial_update_same (i : Fin k) (w : (Fin k → ℂ) → ℂ) (z : Fin k → ℂ) (ζ : ℂ) :
    cpartial i w (Function.update z i ζ) = deriv (fun ξ : ℂ => w (Function.update z i ξ)) ζ := by
  have hfun : (fun ξ : ℂ => w (Function.update (Function.update z i ζ) i ξ))
      = fun ξ : ℂ => w (Function.update z i ξ) := by
    funext ξ
    rw [Function.update_idem]
  rw [cpartial, Function.update_self, hfun]

/-- Along a different coordinate, the partial derivative is the derivative of the slice at the
shifted point. -/
theorem cpartial_update_other {i j : Fin k} (hij : i ≠ j) (w : (Fin k → ℂ) → ℂ)
    (z : Fin k → ℂ) (ζ : ℂ) :
    cpartial i w (Function.update z j ζ)
      = deriv (fun ξ : ℂ => w (Function.update (Function.update z i ξ) j ζ)) (z i) := by
  have hfun : (fun ξ : ℂ => w (Function.update (Function.update z j ζ) i ξ))
      = fun ξ : ℂ => w (Function.update (Function.update z i ξ) j ζ) := by
    funext ξ
    rw [Function.update_comm (Ne.symm hij)]
  rw [cpartial, Function.update_of_ne hij, hfun]

/-- **Slice holomorphy of the partial derivative along the same coordinate.** -/
theorem sliceHolo_cpartial_same {ρ' : ℝ} {w : (Fin k → ℂ) → ℂ}
    (hwh : SliceHolo w ρ') (i : Fin k) {z : Fin k → ℂ} (hz : z ∈ tube k ρ') :
    DifferentiableOn ℂ (fun ζ : ℂ => cpartial i w (Function.update z i ζ)) (imStrip ρ') := by
  have hopen := isOpen_imStrip ρ'
  have hana : AnalyticOnNhd ℂ (fun ξ : ℂ => w (Function.update z i ξ)) (imStrip ρ') :=
    (hwh z hz i).analyticOnNhd hopen
  have hd : DifferentiableOn ℂ (deriv fun ξ : ℂ => w (Function.update z i ξ)) (imStrip ρ') :=
    (hana.deriv_of_isOpen hopen).differentiableOn
  refine hd.congr fun ζ _ => ?_
  exact cpartial_update_same i w z ζ

/-- **Slice holomorphy of the partial derivative along a different coordinate.**

The derivative in the coordinate `i` is a contour integral of the function; the integrand is
holomorphic in the coordinate `j`, and holomorphy passes through the contour integral. -/
theorem sliceHolo_cpartial_other {ρ' : ℝ}
    {w : (Fin k → ℂ) → ℂ} (hwc : ContinuousOn w (tube k ρ')) (hwh : SliceHolo w ρ')
    {i j : Fin k} (hij : i ≠ j) {z : Fin k → ℂ} (hz : z ∈ tube k ρ') :
    DifferentiableOn ℂ (fun ζ : ℂ => cpartial i w (Function.update z j ζ)) (imStrip ρ') := by
  classical
  set ρ : ℝ := |(z i).im| with hρdef
  have hρ : ρ < ρ' := by rw [hρdef]; exact hz i
  set R : ℝ := (ρ' - ρ) / 2 with hRdef
  have hRpos : (0 : ℝ) < R := by rw [hRdef]; linarith
  have hzi : |(z i).im| ≤ ρ := by rw [hρdef]
  have hdisc : closedBall (z i) R ⊆ imStrip ρ' := closedBall_subset_imStrip hρ hzi
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
  have hform : ∀ ζ ∈ imStrip ρ',
      cpartial i w (Function.update z j ζ)
        = (2 * Real.pi * Complex.I / ((Nat.factorial 1 : ℕ) : ℂ))⁻¹
          • ∮ ξ in C(z i, R), (1 / (ξ - z i) ^ (1 + 1))
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
    have hrep := iteratedDeriv_eq_circleIntegral hRpos 1 hslice hd
    rw [iteratedDeriv_one] at hrep
    rw [cpartial_update_other hij w z ζ]
    exact hrep
  have hint : DifferentiableOn ℂ (fun ζ : ℂ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), (circleMap 0 R θ * Complex.I)
        • ((1 / (circleMap 0 R θ) ^ (1 + 1))
          • w (Function.update (Function.update z i (z i + circleMap 0 R θ)) j ζ)))
      (imStrip ρ') := by
    refine differentiableOn_intervalIntegral_of_holomorphic_on
      (F := fun θ ζ => (circleMap 0 R θ * Complex.I)
        • ((1 / (circleMap 0 R θ) ^ (1 + 1))
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
          (fun q' : ℝ × ℂ => 1 / (circleMap 0 R q'.1) ^ (1 + 1)) q := by
        refine ContinuousAt.div continuousAt_const (hc0.pow (1 + 1)) ?_
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
      exact (hslice.const_smul ((1 : ℂ) / (circleMap 0 R θ) ^ (1 + 1))).const_smul
        (circleMap 0 R θ * Complex.I)
  have hEq : ∀ ζ ∈ imStrip ρ',
      (2 * Real.pi * Complex.I / ((Nat.factorial 1 : ℕ) : ℂ))⁻¹
        • ∮ ξ in C(z i, R), (1 / (ξ - z i) ^ (1 + 1))
          • w (Function.update (Function.update z i ξ) j ζ)
      = (2 * Real.pi * Complex.I / ((Nat.factorial 1 : ℕ) : ℂ))⁻¹
        • ∫ θ in (0 : ℝ)..(2 * Real.pi), (circleMap 0 R θ * Complex.I)
          • ((1 / (circleMap 0 R θ) ^ (1 + 1))
            • w (Function.update (Function.update z i (z i + circleMap 0 R θ)) j ζ)) := by
    intro ζ _
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    show deriv (circleMap (z i) R) θ
        • ((1 / (circleMap (z i) R θ - z i) ^ (1 + 1))
          • w (Function.update (Function.update z i (circleMap (z i) R θ)) j ζ))
      = (circleMap 0 R θ * Complex.I)
        • ((1 / (circleMap 0 R θ) ^ (1 + 1))
          • w (Function.update (Function.update z i (z i + circleMap 0 R θ)) j ζ))
    rw [deriv_circleMap, circleMap_sub_center, circleMap_eq_add (z i) R θ]
  refine DifferentiableOn.congr (hint.const_smul
    ((2 * Real.pi * Complex.I / ((Nat.factorial 1 : ℕ) : ℂ))⁻¹)) fun ζ hζ => ?_
  rw [hform ζ hζ, hEq ζ hζ]
  rfl

/-- **A transverse partial derivative of a slice holomorphic function is slice holomorphic.** -/
theorem sliceHolo_cpartial {ρ : ℝ} {w : (Fin k → ℂ) → ℂ} (hwc : ContinuousOn w (tube k ρ))
    (hwh : SliceHolo w ρ) (i : Fin k) : SliceHolo (cpartial i w) ρ := by
  intro z hz j
  by_cases hij : i = j
  · subst hij
    exact sliceHolo_cpartial_same hwh i hz
  · exact sliceHolo_cpartial_other hwc hwh hij hz

end GaloisForLFunctions.HTGeometry
