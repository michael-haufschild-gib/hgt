import GaloisForLFunctions.RHTower.XiLogDerivSymmetry
import GaloisForLFunctions.RHTower.XiVerticalPhaseTwo

/-!
# Folding a symmetric rectangle onto one quarter path

The rectangle `[1−a, a] × [−T, T]` is invariant under both `s ↦ s̄` and `s ↦ 1−s`, and `ξ'/ξ` is
equivariant for them: the real part on the two vertical sides differs by a sign, and the imaginary
part on the two horizontal sides differs by a sign.  Taking imaginary parts of the four side
integrals therefore collapses them to

`Im ∮ = 4 ∫₀^T Re (ξ'/ξ)(a+iy) dy − 4 ∫_{1/2}^{a} Im (ξ'/ξ)(x+iT) dx`.

Since the contour integral is `2πi` times the enclosed divisor mass, this is the classical quarter
path formula.
-/

open Complex Set MeasureTheory intervalIntegral

noncomputable section

namespace RHTower

/-! ## Continuity along lines -/

theorem continuousOn_logDeriv_xi {S : Set ℂ} (h : ∀ s ∈ S, xi s ≠ 0) :
    ContinuousOn (logDeriv xi) S := by
  intro s hs
  have hxi : AnalyticAt ℂ xi s := xi_analyticOnNhd_univ s (Set.mem_univ s)
  have hquot : AnalyticAt ℂ (fun z => deriv xi z / xi z) s := hxi.deriv.div hxi (h s hs)
  have heq : logDeriv xi = fun z => deriv xi z / xi z := by
    funext z
    rw [logDeriv_apply]
  rw [heq]
  exact hquot.continuousAt.continuousWithinAt

theorem xi_vertical_ne_zero_of_one_lt {a : ℝ} (ha : 1 ≤ a) (y : ℝ) :
    xi ((a : ℂ) + (y : ℂ) * I) ≠ 0 := by
  refine xi_ne_zero_of_one_le_re ?_
  simpa using ha

theorem xi_vertical_ne_zero_of_reflect {a : ℝ} (ha : 1 ≤ a) (y : ℝ) :
    xi (((1 - a : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
  have hrw : (((1 - a : ℝ) : ℂ) + (y : ℂ) * I)
      = 1 - ((a : ℂ) + ((-y : ℝ) : ℂ) * I) := by
    simp [Complex.ext_iff]
  rw [hrw, xi_one_sub]
  exact xi_vertical_ne_zero_of_one_lt ha (-y)

theorem continuous_logDeriv_xi_line {a : ℝ} (h : ∀ y : ℝ, xi ((a : ℂ) + (y : ℂ) * I) ≠ 0) :
    Continuous fun y : ℝ => logDeriv xi ((a : ℂ) + (y : ℂ) * I) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  have hxi : AnalyticAt ℂ xi ((a : ℂ) + (y : ℂ) * I) :=
    xi_analyticOnNhd_univ _ (Set.mem_univ _)
  have hquot : AnalyticAt ℂ (fun z => deriv xi z / xi z) ((a : ℂ) + (y : ℂ) * I) :=
    hxi.deriv.div hxi (h y)
  have heq : logDeriv xi = fun z => deriv xi z / xi z := by
    funext z
    rw [logDeriv_apply]
  have hpath : ContinuousAt (fun u : ℝ => (a : ℂ) + (u : ℂ) * I) y := by fun_prop
  rw [heq]
  exact ContinuousAt.comp (f := fun u : ℝ => (a : ℂ) + (u : ℂ) * I) hquot.continuousAt hpath

/-! ## Imaginary parts of the side integrals -/

theorem im_vIntegral {f : ℂ → ℂ} {x y₁ y₂ : ℝ}
    (hint : IntervalIntegrable (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) volume y₁ y₂) :
    (VIntegral f x y₁ y₂).im = ∫ y in y₁..y₂, (f ((x : ℂ) + (y : ℂ) * I)).re := by
  rw [VIntegral, smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im, one_mul, zero_mul,
    zero_add]
  have h := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint
  simpa using h.symm

theorem im_hIntegral {f : ℂ → ℂ} {x₁ x₂ y : ℝ}
    (hint : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) volume x₁ x₂) :
    (HIntegral f x₁ x₂ y).im = ∫ x in x₁..x₂, (f ((x : ℂ) + (y : ℂ) * I)).im := by
  rw [HIntegral]
  have h := ContinuousLinearMap.intervalIntegral_comp_comm Complex.imCLM hint
  simpa using h.symm

/-! ## The two vertical folds -/

theorem integral_re_vertical_symm {a : ℝ} (h : ∀ y : ℝ, xi ((a : ℂ) + (y : ℂ) * I) ≠ 0) (T : ℝ) :
    (∫ y in (-T)..T, (logDeriv xi ((a : ℂ) + (y : ℂ) * I)).re)
      = 2 * ∫ y in (0 : ℝ)..T, (logDeriv xi ((a : ℂ) + (y : ℂ) * I)).re := by
  have hc : Continuous fun y : ℝ => (logDeriv xi ((a : ℂ) + (y : ℂ) * I)).re :=
    Complex.continuous_re.comp (continuous_logDeriv_xi_line h)
  have hsplit : (∫ y in (-T)..T, (logDeriv xi ((a : ℂ) + (y : ℂ) * I)).re)
      = (∫ y in (-T)..(0 : ℝ), (logDeriv xi ((a : ℂ) + (y : ℂ) * I)).re)
        + ∫ y in (0 : ℝ)..T, (logDeriv xi ((a : ℂ) + (y : ℂ) * I)).re :=
    (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)).symm
  have hneg : (∫ y in (-T)..(0 : ℝ), (logDeriv xi ((a : ℂ) + (y : ℂ) * I)).re)
      = ∫ y in (0 : ℝ)..T, (logDeriv xi ((a : ℂ) + (y : ℂ) * I)).re := by
    have hcomp := intervalIntegral.integral_comp_neg
      (fun y : ℝ => (logDeriv xi ((a : ℂ) + (y : ℂ) * I)).re) (a := 0) (b := T)
    norm_num at hcomp
    rw [← hcomp]
    refine intervalIntegral.integral_congr fun y _ => ?_
    have hrw : ((a : ℂ) + -((y : ℂ) * I)) = (a : ℂ) - (y : ℂ) * I := by ring
    rw [hrw, re_logDeriv_xi_conj_line]
  rw [hsplit, hneg]
  ring

theorem integral_re_vertical_reflect {a : ℝ} (ha : 1 ≤ a) (T : ℝ) :
    (∫ y in (-T)..T, (logDeriv xi (((1 - a : ℝ) : ℂ) + (y : ℂ) * I)).re)
      = -∫ y in (-T)..T, (logDeriv xi ((a : ℂ) + (y : ℂ) * I)).re := by
  have hc : Continuous fun y : ℝ => (logDeriv xi ((a : ℂ) + (y : ℂ) * I)).re :=
    Complex.continuous_re.comp
      (continuous_logDeriv_xi_line (xi_vertical_ne_zero_of_one_lt ha))
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun y _ => ?_
  exact re_logDeriv_xi_reflect_line a y

/-! ## The horizontal fold -/

theorem integral_im_horizontal_fold {a T : ℝ}
    (hc : Continuous fun x : ℝ => (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im) :
    (∫ x in (1 - a)..a, (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im)
      = 2 * ∫ x in (1 / 2 : ℝ)..a, (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im := by
  have hsplit : (∫ x in (1 - a)..a, (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im)
      = (∫ x in (1 - a)..(1 / 2 : ℝ), (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im)
        + ∫ x in (1 / 2 : ℝ)..a, (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im :=
    (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)).symm
  have hrefl : (∫ x in (1 - a)..(1 / 2 : ℝ), (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im)
      = ∫ x in (1 / 2 : ℝ)..a, (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (fun x : ℝ => (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im) (1 : ℝ)
      (a := 1 / 2) (b := a)
    norm_num at hcomp
    rw [← hcomp]
    refine intervalIntegral.integral_congr fun x _ => ?_
    have hrw : ((1 : ℂ) - (x : ℂ) + (T : ℂ) * I) = (((1 - x : ℝ)) : ℂ) + (T : ℂ) * I := by
      push_cast
      ring
    rw [hrw]
    exact im_logDeriv_xi_reflect_segment x T
  rw [hsplit, hrefl]
  ring

/-! ## The full fold -/

theorem continuous_logDeriv_xi_horizontal {T : ℝ}
    (h : ∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0) :
    Continuous fun x : ℝ => logDeriv xi ((x : ℂ) + (T : ℂ) * I) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hxi : AnalyticAt ℂ xi ((x : ℂ) + (T : ℂ) * I) :=
    xi_analyticOnNhd_univ _ (Set.mem_univ _)
  have hquot : AnalyticAt ℂ (fun z => deriv xi z / xi z) ((x : ℂ) + (T : ℂ) * I) :=
    hxi.deriv.div hxi (h x)
  have heq : logDeriv xi = fun z => deriv xi z / xi z := by
    funext z
    rw [logDeriv_apply]
  have hpath : ContinuousAt (fun u : ℝ => (u : ℂ) + (T : ℂ) * I) x := by fun_prop
  rw [heq]
  exact ContinuousAt.comp (f := fun u : ℝ => (u : ℂ) + (T : ℂ) * I) hquot.continuousAt hpath

/-- **The four sides of a symmetric rectangle fold onto one quarter path.** -/
theorem im_rectangleIntegral_logDeriv_xi {a T : ℝ} (ha : 1 ≤ a)
    (hne : ∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0) :
    (RectangleIntegral (logDeriv xi) (((1 - a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
        ((a : ℂ) + (T : ℂ) * I)).im
      = 4 * (∫ y in (0 : ℝ)..T, (logDeriv xi ((a : ℂ) + (y : ℂ) * I)).re)
        - 4 * ∫ x in (1 / 2 : ℝ)..a, (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im := by
  have hzre : (((1 - a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).re = 1 - a := by simp
  have hzim : (((1 - a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).im = -T := by simp
  have hwre : ((a : ℂ) + (T : ℂ) * I).re = a := by simp
  have hwim : ((a : ℂ) + (T : ℂ) * I).im = T := by simp
  have hha : Continuous fun x : ℝ => logDeriv xi ((x : ℂ) + (T : ℂ) * I) :=
    continuous_logDeriv_xi_horizontal hne
  have hneneg : ∀ x : ℝ, xi ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0 := by
    intro x
    have hcast : ((x : ℂ) + ((-T : ℝ) : ℂ) * I)
        = (starRingEnd ℂ) ((x : ℂ) + (T : ℂ) * I) := by
      simp
    rw [hcast, xi_conj]
    simpa using hne x
  have hhneg : Continuous fun x : ℝ => logDeriv xi ((x : ℂ) + ((-T : ℝ) : ℂ) * I) :=
    continuous_logDeriv_xi_horizontal hneneg
  have hva : Continuous fun y : ℝ => logDeriv xi ((a : ℂ) + (y : ℂ) * I) :=
    continuous_logDeriv_xi_line (xi_vertical_ne_zero_of_one_lt ha)
  have hvb : Continuous fun y : ℝ => logDeriv xi (((1 - a : ℝ) : ℂ) + (y : ℂ) * I) :=
    continuous_logDeriv_xi_line (xi_vertical_ne_zero_of_reflect ha)
  have hH1 : (∫ x in (1 - a)..a, (logDeriv xi ((x : ℂ) + ((-T : ℝ) : ℂ) * I)).im)
      = -∫ x in (1 - a)..a, (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x _ => ?_
    have hcast : ((x : ℂ) + ((-T : ℝ) : ℂ) * I) = (x : ℂ) - (T : ℂ) * I := by
      push_cast
      ring
    rw [hcast, im_logDeriv_xi_conj_line]
  have hH2 := integral_im_horizontal_fold (a := a) (T := T)
    (Complex.continuous_im.comp hha)
  have hV1 := integral_re_vertical_symm (xi_vertical_ne_zero_of_one_lt ha) T
  have hV2 := integral_re_vertical_reflect ha T
  rw [RectangleIntegral, hzre, hzim, hwre, hwim, Complex.sub_im, Complex.add_im,
    Complex.sub_im,
    im_hIntegral (hhneg.intervalIntegrable _ _), im_hIntegral (hha.intervalIntegrable _ _),
    im_vIntegral (hva.intervalIntegrable _ _), im_vIntegral (hvb.intervalIntegrable _ _),
    hH1, hH2, hV2, hV1]
  ring

/-! ## The quarter-path counting formula -/

theorem xi_ne_zero_on_rectangleBorder {a T : ℝ} (ha : 1 ≤ a)
    (hne : ∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0) :
    ∀ s ∈ RectangleBorder (((1 - a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) ((a : ℂ) + (T : ℂ) * I),
      xi s ≠ 0 := by
  have hneneg : ∀ x : ℝ, xi ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0 := by
    intro x
    have hcast : ((x : ℂ) + ((-T : ℝ) : ℂ) * I)
        = (starRingEnd ℂ) ((x : ℂ) + (T : ℂ) * I) := by simp
    rw [hcast, xi_conj]
    simpa using hne x
  intro s hs
  have hzre : (((1 - a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).re = 1 - a := by simp
  have hzim : (((1 - a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).im = -T := by simp
  have hwre : ((a : ℂ) + (T : ℂ) * I).re = a := by simp
  have hwim : ((a : ℂ) + (T : ℂ) * I).im = T := by simp
  rw [RectangleBorder, hzre, hzim, hwre, hwim] at hs
  rcases hs with ((hs | hs) | hs) | hs
  · have him : s.im = -T := hs.2
    have hcast : s = ((s.re : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [him]
    rw [hcast]
    exact hneneg s.re
  · have hre : s.re = 1 - a := hs.1
    have hcast : s = (((1 - a : ℝ)) : ℂ) + ((s.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hre]
    rw [hcast]
    exact xi_vertical_ne_zero_of_reflect ha s.im
  · have him : s.im = T := hs.2
    have hcast : s = ((s.re : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [him]
    rw [hcast]
    exact hne s.re
  · have hre : s.re = a := hs.1
    have hcast : s = ((a : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hre]
    rw [hcast]
    exact xi_vertical_ne_zero_of_one_lt ha s.im

/-- **The quarter-path counting formula.**  The divisor mass of the symmetric rectangle is the
quarter-path combination of one vertical and one horizontal integral. -/
theorem two_pi_mul_regionOrderSum_eq {a T : ℝ} (ha : 1 ≤ a)
    (hne : ∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0) (hT : 0 ≤ T) :
    2 * Real.pi * ((xiRegionOrderSum
        (Rectangle (((1 - a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) ((a : ℂ) + (T : ℂ) * I)) : ℤ) : ℝ)
      = 4 * (∫ y in (0 : ℝ)..T, (logDeriv xi ((a : ℂ) + (y : ℂ) * I)).re)
        - 4 * ∫ x in (1 / 2 : ℝ)..a, (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im := by
  have hzre : (((1 - a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).re = 1 - a := by simp
  have hwre : ((a : ℂ) + (T : ℂ) * I).re = a := by simp
  have hzim : (((1 - a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).im = -T := by simp
  have hwim : ((a : ℂ) + (T : ℂ) * I).im = T := by simp
  have hres := rectangleIntegral_logDeriv_xi_eq_regionOrderSum
    (z := ((1 - a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) (w := (a : ℂ) + (T : ℂ) * I)
    (by rw [hzre, hwre]; linarith) (by rw [hzim, hwim]; linarith)
    (xi_ne_zero_on_rectangleBorder ha hne)
  rw [RectangleIntegral'] at hres
  have hI : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hrect : RectangleIntegral (logDeriv xi) (((1 - a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
      ((a : ℂ) + (T : ℂ) * I)
      = (2 * (Real.pi : ℂ) * I) * ((xiRegionOrderSum
        (Rectangle (((1 - a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) ((a : ℂ) + (T : ℂ) * I)) : ℤ) : ℂ) := by
    rw [← hres, smul_eq_mul]
    field_simp
  have him := congrArg Complex.im hrect
  rw [im_rectangleIntegral_logDeriv_xi ha hne] at him
  rw [him]
  simp [Complex.mul_im, Complex.mul_re]

end RHTower
