import Mathlib

/-!
# The vertical modulus derivative of an analytic function

Along a vertical line the squared modulus of an analytic function has derivative

`d/dt ‖f (x + i t)‖² = -2 * Im (f' (x + i t) * conj (f (x + i t)))`.

The right-hand side is defined at every point, including the zeros of `f`, whereas the
logarithmic-derivative form `-2 ‖f‖² * Im (logDeriv f)` requires `f ≠ 0`.  This matters for
criteria whose sharpness lives at the zeros: the two forms agree off the divisor, but only the
first extends across it, where it vanishes.
-/

open Complex

namespace HTGeometry

/-- The vertical path and its derivative. -/
theorem hasDerivAt_verticalPath (x a : ℝ) :
    HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) Complex.I a := by
  have h : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 a := Complex.ofRealCLM.hasDerivAt
  simpa using ((h.mul_const Complex.I).const_add ((x : ℂ)))

/-- **The vertical modulus derivative, valid at the zeros too.**  For `f` complex-differentiable at
`x + i a`, the squared modulus along the vertical line has derivative
`-2 * Im (f' * conj f)`.  No nonvanishing hypothesis is needed. -/
theorem hasDerivAt_normSq_vertical_general (f : ℂ → ℂ) (x a : ℝ)
    (hf : DifferentiableAt ℂ f ((x : ℂ) + (a : ℂ) * Complex.I)) :
    HasDerivAt (fun t : ℝ => Complex.normSq (f ((x : ℂ) + (t : ℂ) * Complex.I)))
      (-2 * (deriv f ((x : ℂ) + (a : ℂ) * Complex.I) *
        (starRingEnd ℂ) (f ((x : ℂ) + (a : ℂ) * Complex.I))).im) a := by
  set z : ℂ := (x : ℂ) + (a : ℂ) * Complex.I with hz
  set w : ℂ := f z with hw
  have hcomp : HasDerivAt (fun t : ℝ => f ((x : ℂ) + (t : ℂ) * Complex.I))
      (Complex.I • deriv f z) a := by
    have := hf.hasDerivAt.scomp a (hasDerivAt_verticalPath x a)
    simpa [Function.comp] using this
  have hre : HasDerivAt (fun t : ℝ => (f ((x : ℂ) + (t : ℂ) * Complex.I)).re)
      (Complex.I • deriv f z).re a :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt a hcomp
  have him : HasDerivAt (fun t : ℝ => (f ((x : ℂ) + (t : ℂ) * Complex.I)).im)
      (Complex.I • deriv f z).im a :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt a hcomp
  have hsq : HasDerivAt
      (fun t : ℝ => Complex.normSq (f ((x : ℂ) + (t : ℂ) * Complex.I)))
      (2 * w.re * (Complex.I • deriv f z).re +
        2 * w.im * (Complex.I • deriv f z).im) a := by
    have hform : (fun t : ℝ =>
        Complex.normSq (f ((x : ℂ) + (t : ℂ) * Complex.I))) =
        fun t : ℝ => (f ((x : ℂ) + (t : ℂ) * Complex.I)).re *
            (f ((x : ℂ) + (t : ℂ) * Complex.I)).re +
          (f ((x : ℂ) + (t : ℂ) * Complex.I)).im *
            (f ((x : ℂ) + (t : ℂ) * Complex.I)).im := by
      funext t
      rw [Complex.normSq_apply]
    rw [hform]
    have h := (hre.mul hre).add (him.mul him)
    convert h using 1
    ring
  convert hsq using 1
  simp only [smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Off the divisor the two forms of the vertical derivative agree. -/
theorem neg_two_im_deriv_mul_conj_eq (f : ℂ → ℂ) {z : ℂ} (hz : f z ≠ 0) :
    -2 * (deriv f z * (starRingEnd ℂ) (f z)).im
      = -2 * Complex.normSq (f z) * (logDeriv f z).im := by
  have hns : (Complex.normSq (f z) : ℝ) ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hz
  have hlog : logDeriv f z
      = ((Complex.normSq (f z))⁻¹ : ℝ) * (deriv f z * (starRingEnd ℂ) (f z)) := by
    rw [logDeriv, Pi.div_apply, div_eq_mul_inv, Complex.inv_def]
    push_cast
    ring
  rw [hlog]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  field_simp

/-- **Vertical monotonicity from the sign of `Im (f' * conj f)`.**  If the quantity
`-Im (f' * conj f)` is nonnegative along a vertical segment, the squared modulus is monotone
there.  This is the form that survives at the zeros of `f`. -/
theorem monotoneOn_normSq_vertical_of_neg_im_nonneg (f : ℂ → ℂ) (x : ℝ) {s : Set ℝ}
    (hconv : Convex ℝ s)
    (hf : ∀ t ∈ s, DifferentiableAt ℂ f ((x : ℂ) + (t : ℂ) * Complex.I))
    (hsign : ∀ t ∈ s, 0 ≤ -(deriv f ((x : ℂ) + (t : ℂ) * Complex.I) *
      (starRingEnd ℂ) (f ((x : ℂ) + (t : ℂ) * Complex.I))).im) :
    MonotoneOn (fun t : ℝ => Complex.normSq (f ((x : ℂ) + (t : ℂ) * Complex.I))) s := by
  intro p hp q hq hpq
  rcases eq_or_lt_of_le hpq with rfl | hlt
  · exact le_refl _
  have hderiv : ∀ t ∈ Set.Icc p q,
      HasDerivAt (fun u : ℝ => Complex.normSq (f ((x : ℂ) + (u : ℂ) * Complex.I)))
        (-2 * (deriv f ((x : ℂ) + (t : ℂ) * Complex.I) *
          (starRingEnd ℂ) (f ((x : ℂ) + (t : ℂ) * Complex.I))).im) t := by
    intro t ht
    exact hasDerivAt_normSq_vertical_general f x t
      (hf t (hconv.segment_subset hp hq (by
        rw [segment_eq_Icc hpq]
        exact ht)))
  have hmono : MonotoneOn (fun u : ℝ =>
      Complex.normSq (f ((x : ℂ) + (u : ℂ) * Complex.I))) (Set.Icc p q) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc p q) ?_ ?_ ?_
    · exact fun t ht => ((hderiv t ht).continuousAt).continuousWithinAt
    · intro t ht
      exact ((hderiv t (Set.mem_Icc_of_Ioo (by rwa [interior_Icc] at ht))).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [(hderiv t (Set.mem_Icc_of_Ioo (by rwa [interior_Icc] at ht))).deriv]
      have := hsign t (hconv.segment_subset hp hq (by
        rw [segment_eq_Icc hpq]
        exact Set.mem_Icc_of_Ioo (by rwa [interior_Icc] at ht)))
      linarith
  exact hmono (Set.left_mem_Icc.mpr hpq) (Set.right_mem_Icc.mpr hpq) hpq

end HTGeometry
