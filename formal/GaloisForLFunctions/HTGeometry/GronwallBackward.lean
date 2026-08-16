import GaloisForLFunctions.HTGeometry.GronwallVariableCoefficient

/-!
# Grönwall's inequality anchored at the right endpoint

The forward inequality bounds a function whose Volterra estimate accumulates from the left.  The
recessive branch of a second-order equation accumulates from the *right*: its Volterra equation
integrates from the far endpoint back, because that is the direction in which the kernel is
bounded.  Reflecting the interval through its midpoint turns one into the other.
-/

noncomputable section

open Set intervalIntegral MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- Reflection of an interval integral through the midpoint of `[a,b]`. -/
theorem integral_comp_reflect {a b x : ℝ} (f : ℝ → ℝ) :
    (∫ u in a..x, f (a + b - u)) = ∫ t in (a + b - x)..b, f t := by
  have h := intervalIntegral.integral_comp_sub_left (a := a) (b := x) f (a + b)
  rw [h]
  congr 1
  ring

/-- **Grönwall's inequality, backward form.**  A function whose Volterra estimate accumulates from
the right endpoint is bounded by the exponential of the accumulated coefficient. -/
theorem abs_le_exp_integral_of_volterra_bound_backward {a b : ℝ} (hab : a ≤ b) {h φ : ℝ → ℝ}
    (hh : Continuous h) (hφ : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hbd : ∀ x ∈ Icc a b, |h x| ≤ 1 + ∫ t in x..b, φ t * |h t|) :
    ∀ x ∈ Icc a b, |h x| ≤ Real.exp (∫ t in x..b, φ t) := by
  set σ : ℝ → ℝ := fun y => a + b - y with hσ
  set hr : ℝ → ℝ := fun y => h (σ y) with hhr
  set φr : ℝ → ℝ := fun y => φ (σ y) with hφr
  have hσcont : Continuous σ := by fun_prop
  have hhrc : Continuous hr := hh.comp hσcont
  have hφrc : Continuous φr := hφ.comp hσcont
  have hφr0 : ∀ x, 0 ≤ φr x := fun x => hφ0 _
  have hσmem : ∀ x ∈ Icc a b, σ x ∈ Icc a b := by
    intro x hx
    exact ⟨by simp only [hσ]; linarith [hx.2], by simp only [hσ]; linarith [hx.1]⟩
  have hrefl : ∀ x : ℝ, (∫ u in a..x, φr u * |hr u|) = ∫ t in (σ x)..b, φ t * |h t| := by
    intro x
    exact integral_comp_reflect (fun t => φ t * |h t|)
  have hreflφ : ∀ x : ℝ, (∫ u in a..x, φr u) = ∫ t in (σ x)..b, φ t := by
    intro x
    exact integral_comp_reflect φ
  have hbdr : ∀ x ∈ Icc a b, |hr x| ≤ 1 + ∫ t in a..x, φr t * |hr t| := by
    intro x hx
    rw [hrefl x]
    exact hbd (σ x) (hσmem x hx)
  have hmain := abs_le_exp_integral_of_volterra_bound hab hhrc hφrc hφr0 hbdr
  intro x hx
  have hσx := hmain (σ x) (hσmem x hx)
  rw [hreflφ (σ x)] at hσx
  have hσσ : σ (σ x) = x := by simp only [hσ]; ring
  have hval : hr (σ x) = h x := by
    show h (σ (σ x)) = h x
    rw [hσσ]
  rw [hval, hσσ] at hσx
  exact hσx

/-- The tail integral of a continuous coefficient is continuous. -/
theorem continuous_integral_tail {b : ℝ} {φ : ℝ → ℝ} (hφ : Continuous φ) :
    Continuous fun y : ℝ => ∫ u in y..b, φ u := by
  have hd : ∀ y : ℝ, HasDerivAt (fun z : ℝ => ∫ u in z..b, φ u) (-φ y) y := by
    intro y
    exact intervalIntegral.integral_hasDerivAt_left (hφ.intervalIntegrable y b)
      (hφ.stronglyMeasurableAtFilter _ _) hφ.continuousAt
  exact continuous_iff_continuousAt.2 fun y => (hd y).continuousAt

/-- **The error form, backward.** -/
theorem abs_sub_one_le_exp_sub_one_of_volterra_bound_backward {a b : ℝ} (hab : a ≤ b)
    {h φ : ℝ → ℝ}
    (hh : Continuous h) (hφ : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hbd : ∀ x ∈ Icc a b, |h x| ≤ 1 + ∫ t in x..b, φ t * |h t|)
    (herr : ∀ x ∈ Icc a b, |h x - 1| ≤ ∫ t in x..b, φ t * |h t|) :
    ∀ x ∈ Icc a b, |h x - 1| ≤ Real.exp (∫ t in x..b, φ t) - 1 := by
  intro x hx
  have hxb : x ≤ b := hx.2
  have hbound := abs_le_exp_integral_of_volterra_bound_backward hab hh hφ hφ0 hbd
  have hGcont : Continuous fun y : ℝ => ∫ u in y..b, φ u := continuous_integral_tail hφ
  have hprod : Continuous fun t : ℝ => φ t * Real.exp (∫ u in t..b, φ u) :=
    hφ.mul (Real.continuous_exp.comp hGcont)
  have hstep : (∫ t in x..b, φ t * |h t|)
      ≤ ∫ t in x..b, φ t * Real.exp (∫ u in t..b, φ u) := by
    refine intervalIntegral.integral_mono_on hxb ((hφ.mul hh.abs).intervalIntegrable _ _)
      (hprod.intervalIntegrable _ _) ?_
    intro t ht
    have hmem : t ∈ Icc a b := ⟨le_trans hx.1 ht.1, ht.2⟩
    exact mul_le_mul_of_nonneg_left (hbound t hmem) (hφ0 t)
  have hFTC : (∫ t in x..b, φ t * Real.exp (∫ u in t..b, φ u))
      = Real.exp (∫ u in x..b, φ u) - 1 := by
    have hderiv : ∀ t ∈ uIcc x b,
        HasDerivAt (fun y : ℝ => -Real.exp (∫ u in y..b, φ u))
          (φ t * Real.exp (∫ u in t..b, φ u)) t := by
      intro t _
      have hinner : HasDerivAt (fun y : ℝ => ∫ u in y..b, φ u) (-φ t) t :=
        intervalIntegral.integral_hasDerivAt_left (hφ.intervalIntegrable t b)
          (hφ.stronglyMeasurableAtFilter _ _) hφ.continuousAt
      have hexp := hinner.exp
      refine hexp.neg.congr_deriv ?_
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hprod.intervalIntegrable _ _)]
    simp
    ring
  calc |h x - 1| ≤ ∫ t in x..b, φ t * |h t| := herr x hx
    _ ≤ ∫ t in x..b, φ t * Real.exp (∫ u in t..b, φ u) := hstep
    _ = Real.exp (∫ u in x..b, φ u) - 1 := hFTC

end GaloisForLFunctions.HTGeometry
