import GaloisForLFunctions.HTGeometry.VerticalModulusDerivative

/-!
# The horizontal modulus derivative of an analytic function

Along a horizontal line the squared modulus of an analytic function has derivative

`d/dt ‖f (t + i b)‖² = 2 * Re (f' (t + i b) * conj (f (t + i b)))`.

As in the vertical case the right-hand side is defined at the zeros too, so the resulting
monotonicity criterion survives across the divisor.
-/

open Complex

namespace HTGeometry

/-- The horizontal path and its derivative. -/
theorem hasDerivAt_horizontalPath (b a : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ) + (b : ℂ) * Complex.I) 1 a := by
  have h : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 a := Complex.ofRealCLM.hasDerivAt
  simpa using h.add_const ((b : ℂ) * Complex.I)

/-- **The horizontal modulus derivative, valid at the zeros too.** -/
theorem hasDerivAt_normSq_horizontal_general (f : ℂ → ℂ) (b a : ℝ)
    (hf : DifferentiableAt ℂ f ((a : ℂ) + (b : ℂ) * Complex.I)) :
    HasDerivAt (fun t : ℝ => Complex.normSq (f ((t : ℂ) + (b : ℂ) * Complex.I)))
      (2 * (deriv f ((a : ℂ) + (b : ℂ) * Complex.I) *
        (starRingEnd ℂ) (f ((a : ℂ) + (b : ℂ) * Complex.I))).re) a := by
  set z : ℂ := (a : ℂ) + (b : ℂ) * Complex.I with hz
  set w : ℂ := f z with hw
  have hcomp : HasDerivAt (fun t : ℝ => f ((t : ℂ) + (b : ℂ) * Complex.I))
      ((1 : ℂ) • deriv f z) a := by
    have h := hf.hasDerivAt.scomp a (hasDerivAt_horizontalPath b a)
    simpa only [Function.comp_apply, smul_eq_mul] using! h
  have hre : HasDerivAt (fun t : ℝ => (f ((t : ℂ) + (b : ℂ) * Complex.I)).re)
      ((1 : ℂ) • deriv f z).re a :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt a hcomp
  have him : HasDerivAt (fun t : ℝ => (f ((t : ℂ) + (b : ℂ) * Complex.I)).im)
      ((1 : ℂ) • deriv f z).im a :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt a hcomp
  have hsq : HasDerivAt
      (fun t : ℝ => Complex.normSq (f ((t : ℂ) + (b : ℂ) * Complex.I)))
      (2 * w.re * ((1 : ℂ) • deriv f z).re +
        2 * w.im * ((1 : ℂ) • deriv f z).im) a := by
    have hform : (fun t : ℝ =>
        Complex.normSq (f ((t : ℂ) + (b : ℂ) * Complex.I))) =
        fun t : ℝ => (f ((t : ℂ) + (b : ℂ) * Complex.I)).re *
            (f ((t : ℂ) + (b : ℂ) * Complex.I)).re +
          (f ((t : ℂ) + (b : ℂ) * Complex.I)).im *
            (f ((t : ℂ) + (b : ℂ) * Complex.I)).im := by
      funext t
      rw [Complex.normSq_apply]
    rw [hform]
    have h := (hre.mul hre).add (him.mul him)
    simpa only [Pi.add_apply, Pi.mul_apply] using!
      h.congr_deriv (by rw [hw, hz]; ring)
  convert hsq using 1
  simp only [one_smul, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **Horizontal monotonicity from the sign of `Re (f' * conj f)`.** -/
theorem monotoneOn_normSq_horizontal_of_re_nonneg (f : ℂ → ℂ) (b : ℝ) {s : Set ℝ}
    (hconv : Convex ℝ s)
    (hf : ∀ t ∈ s, DifferentiableAt ℂ f ((t : ℂ) + (b : ℂ) * Complex.I))
    (hsign : ∀ t ∈ s, 0 ≤ (deriv f ((t : ℂ) + (b : ℂ) * Complex.I) *
      (starRingEnd ℂ) (f ((t : ℂ) + (b : ℂ) * Complex.I))).re) :
    MonotoneOn (fun t : ℝ => Complex.normSq (f ((t : ℂ) + (b : ℂ) * Complex.I))) s := by
  intro p hp q hq hpq
  rcases eq_or_lt_of_le hpq with rfl | hlt
  · exact le_refl _
  have hderiv : ∀ t ∈ Set.Icc p q,
      HasDerivAt (fun u : ℝ => Complex.normSq (f ((u : ℂ) + (b : ℂ) * Complex.I)))
        (2 * (deriv f ((t : ℂ) + (b : ℂ) * Complex.I) *
          (starRingEnd ℂ) (f ((t : ℂ) + (b : ℂ) * Complex.I))).re) t := by
    intro t ht
    exact hasDerivAt_normSq_horizontal_general f b t
      (hf t (hconv.segment_subset hp hq (by rw [segment_eq_Icc hpq]; exact ht)))
  have hmono : MonotoneOn (fun u : ℝ =>
      Complex.normSq (f ((u : ℂ) + (b : ℂ) * Complex.I))) (Set.Icc p q) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc p q) ?_ ?_ ?_
    · exact fun t ht => ((hderiv t ht).continuousAt).continuousWithinAt
    · intro t ht
      exact ((hderiv t (Set.mem_Icc_of_Ioo (by rwa [interior_Icc] at ht))).differentiableAt
        ).differentiableWithinAt
    · intro t ht
      rw [(hderiv t (Set.mem_Icc_of_Ioo (by rwa [interior_Icc] at ht))).deriv]
      have := hsign t (hconv.segment_subset hp hq (by
        rw [segment_eq_Icc hpq]
        exact Set.mem_Icc_of_Ioo (by rwa [interior_Icc] at ht)))
      linarith
  exact hmono (Set.left_mem_Icc.mpr hpq) (Set.right_mem_Icc.mpr hpq) hpq

end HTGeometry
