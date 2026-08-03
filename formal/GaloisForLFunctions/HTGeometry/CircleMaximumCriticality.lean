import Mathlib

/-!
# At a maximum of the modulus on a circle the logarithmic derivative is real

Moving along the circle `t ↦ z·e^{it}` differentiates the squared modulus of `f` to
`−2·Im(conj(f(z))·z·f'(z))`.  At a local maximum that derivative vanishes, so `z·f'(z)/f(z)` is real.

This is the input that no bound on the coefficients can supply: the maximum-modulus point is a
critical point of the modulus along the circle, and criticality kills exactly the imaginary part of
the logarithmic derivative.  In Wiman–Valiron theory it is what removes the component of the weighted
sum along the direction of the value, leaving only the transverse part that the alignment estimates
control.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- Dividing by a nonzero number preserves vanishing of the imaginary part of the conjugate
pairing. -/
theorem im_div_eq_zero_of_im_conj_mul_eq_zero {v w : ℂ} (hw : w ≠ 0)
    (h : ((starRingEnd ℂ) w * v).im = 0) : (v / w).im = 0 := by
  have hcw : (starRingEnd ℂ) w ≠ 0 := by simpa using hw
  have hrw : v / w = (v * (starRingEnd ℂ) w) / ((Complex.normSq w : ℝ) : ℂ) := by
    rw [← Complex.mul_conj]
    field_simp
  rw [hrw, Complex.div_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal]
  rw [mul_comm v ((starRingEnd ℂ) w), h]
  simp

/-- The circle path through `z`. -/
noncomputable def circlePath (z : ℂ) : ℝ → ℂ := fun t => z * Complex.exp (t * Complex.I)

@[simp] theorem circlePath_zero (z : ℂ) : circlePath z 0 = z := by
  simp [circlePath]

/-- The circle path has the expected derivative. -/
theorem hasDerivAt_circlePath (z : ℂ) (t : ℝ) :
    HasDerivAt (circlePath z) (z * (Complex.exp (t * Complex.I) * Complex.I)) t := by
  have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
      (Complex.I • Complex.exp ((t : ℂ) * Complex.I)) t :=
    HasDerivAt.scomp t (Complex.hasDerivAt_exp ((t : ℂ) * Complex.I)) hlin
  have hexp' : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
      (Complex.exp ((t : ℂ) * Complex.I) * Complex.I) t := by
    simpa [smul_eq_mul, mul_comm] using hexp
  exact hexp'.const_mul z

/-- Moving along the circle, the squared modulus has derivative `-2 Im(conj f · z f')`. -/
theorem hasDerivAt_normSq_circlePath {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    HasDerivAt (fun t : ℝ => ‖f (circlePath z t)‖ ^ 2)
      (-(2 * ((starRingEnd ℂ) (f z) * (z * deriv f z)).im)) 0 := by
  have hpath : HasDerivAt (circlePath z) (z * Complex.I) 0 := by
    simpa using hasDerivAt_circlePath z 0
  have hcomp : HasDerivAt (fun t : ℝ => f (circlePath z t)) (z * Complex.I * deriv f z) 0 := by
    have h := HasDerivAt.scomp 0 (hf (circlePath z 0)).hasDerivAt hpath
    rw [circlePath_zero, smul_eq_mul] at h
    exact h
  set D : ℂ := z * Complex.I * deriv f z with hD
  have hre : HasDerivAt (fun t : ℝ => (f (circlePath z t)).re) D.re 0 :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hcomp
  have him : HasDerivAt (fun t : ℝ => (f (circlePath z t)).im) D.im 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hcomp
  have h1 : HasDerivAt (fun t : ℝ => (f (circlePath z t)).re ^ 2) (2 * (f z).re * D.re) 0 := by
    have h := hre.fun_pow 2
    rw [circlePath_zero] at h
    norm_num at h
    exact h
  have h2 : HasDerivAt (fun t : ℝ => (f (circlePath z t)).im ^ 2) (2 * (f z).im * D.im) 0 := by
    have h := him.fun_pow 2
    rw [circlePath_zero] at h
    norm_num at h
    exact h
  have hsum : HasDerivAt
      (fun t : ℝ => (f (circlePath z t)).re ^ 2 + (f (circlePath z t)).im ^ 2)
      (2 * (f z).re * D.re + 2 * (f z).im * D.im) 0 := h1.add h2
  have hfun : (fun t : ℝ => ‖f (circlePath z t)‖ ^ 2)
      = fun t : ℝ => (f (circlePath z t)).re ^ 2 + (f (circlePath z t)).im ^ 2 := by
    funext t
    rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _), Complex.normSq_apply]
    ring
  have hval : 2 * (f z).re * D.re + 2 * (f z).im * D.im
      = -(2 * ((starRingEnd ℂ) (f z) * (z * deriv f z)).im) := by
    have hexpand : (starRingEnd ℂ) (f z) * (z * deriv f z)
        = (starRingEnd ℂ) (f z) * D * (-Complex.I) := by
      rw [hD]
      have : (Complex.I : ℂ) * (-Complex.I) = 1 := by
        simp [Complex.I_mul_I]
      calc (starRingEnd ℂ) (f z) * (z * deriv f z)
          = (starRingEnd ℂ) (f z) * (z * deriv f z) * ((Complex.I : ℂ) * (-Complex.I)) := by
            rw [this, mul_one]
        _ = (starRingEnd ℂ) (f z) * (z * Complex.I * deriv f z) * (-Complex.I) := by ring
    rw [hexpand]
    simp only [Complex.mul_im, Complex.mul_re, Complex.neg_im, Complex.neg_re, Complex.I_im,
      Complex.I_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hfun, ← hval]
  exact hsum

/-- **Criticality on the circle.**  At a local maximum of the modulus along the circle through `z`,
the pairing `conj(f(z)) · z f'(z)` is real. -/
theorem im_conj_mul_eq_zero_of_isLocalMax {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ)
    (hmax : IsLocalMax (fun t : ℝ => ‖f (circlePath z t)‖ ^ 2) 0) :
    ((starRingEnd ℂ) (f z) * (z * deriv f z)).im = 0 := by
  have hzero := hmax.hasDerivAt_eq_zero (hasDerivAt_normSq_circlePath hf z)
  linarith [hzero]

/-- **The logarithmic derivative is real at a circle maximum.** -/
theorem im_mul_deriv_div_eq_zero_of_isLocalMax {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z : ℂ}
    (hfz : f z ≠ 0)
    (hmax : IsLocalMax (fun t : ℝ => ‖f (circlePath z t)‖ ^ 2) 0) :
    (z * deriv f z / f z).im = 0 :=
  im_div_eq_zero_of_im_conj_mul_eq_zero hfz (im_conj_mul_eq_zero_of_isLocalMax hf z hmax)

end GaloisForLFunctions.HTGeometry
