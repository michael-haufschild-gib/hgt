import Mathlib

/-!
# A self-adjoint multiplier times `i` carries no radial mass

If `S` is self-adjoint then `⟪S v, v⟫` is real, so `i ⟪S v, v⟫` is purely imaginary and

`Re ⟪i • S v, v⟫ = 0`.

That is the whole cancellation behind frequency-current conservation: the multiplier survives in
full — it is not estimated, smoothed, or declared lower order — but it transports phase only and
creates no radial Fourier mass.  The same holds for any bounded self-adjoint seam coupling, so the
conservation is insensitive to which one is used.
-/

open scoped ComplexConjugate InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A self-adjoint operator has real quadratic form. -/
theorem inner_self_im_eq_zero_of_isSelfAdjoint {S : E →L[ℂ] E} (hS : IsSelfAdjoint S) (v : E) :
    (inner ℂ (S v) v : ℂ).im = 0 := by
  have hadj : ContinuousLinearMap.adjoint S = S := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hS
  have hconj : (starRingEnd ℂ) (inner ℂ (S v) v : ℂ) = inner ℂ (S v) v := by
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_left, hadj]
  exact Complex.conj_eq_iff_im.mp hconj

/-- **No radial mass.**  Multiplying a self-adjoint operator by `i` makes its quadratic form purely
imaginary, so the real part vanishes. -/
theorem re_inner_I_smul_isSelfAdjoint_eq_zero {S : E →L[ℂ] E} (hS : IsSelfAdjoint S) (v : E) :
    (inner ℂ (Complex.I • S v) v : ℂ).re = 0 := by
  rw [inner_smul_left, Complex.conj_I]
  have him := inner_self_im_eq_zero_of_isSelfAdjoint hS v
  simp [Complex.mul_re, him]

/-- The same statement for a real scalar multiple of `i`, which is the shape the frequency equation
produces. -/
theorem re_inner_real_smul_I_smul_isSelfAdjoint_eq_zero {S : E →L[ℂ] E} (hS : IsSelfAdjoint S)
    (c : ℝ) (v : E) :
    (inner ℂ (((c : ℂ) * Complex.I) • S v) v : ℂ).re = 0 := by
  have hsplit : (((c : ℂ) * Complex.I) • S v) = (c : ℂ) • (Complex.I • S v) := by
    rw [mul_smul]
  rw [hsplit, inner_smul_left, Complex.conj_ofReal]
  have hz := re_inner_I_smul_isSelfAdjoint_eq_zero hS v
  simp [Complex.mul_re, hz]

/-! ## The radial derivative of the squared norm -/

section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [NormedSpace ℝ F]

/-- **Vector form of the squared-norm derivative.**  Along a differentiable path in a complex
Hilbert space, `d/dt ‖f t‖² = 2 Re ⟪f'(t), f(t)⟫`. -/
theorem hasDerivAt_normSq_path {f : ℝ → F} {f' : F} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun t => ‖f t‖ ^ 2) (2 * (inner ℂ f' (f x) : ℂ).re) x := by
  have hinner := HasDerivAt.inner ℂ h h
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hinner
  have hnorm : (fun t => ‖f t‖ ^ 2) = fun t => (inner ℂ (f t) (f t) : ℂ).re := by
    funext t
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hval : ((inner ℂ (f x) f' : ℂ) + (inner ℂ f' (f x) : ℂ)).re =
      2 * (inner ℂ f' (f x) : ℂ).re := by
    rw [← inner_conj_symm f' (f x), Complex.add_re, Complex.conj_re]
    ring
  rw [hnorm, ← hval]
  exact hre

/-- **Frequency-current conservation.**  A path obeying the skew frequency equation has constant
radial current `η ‖f η‖²`: the self-adjoint block contributes nothing, so the whole derivative
comes from the explicit radial term and cancels it exactly. -/
theorem hasDerivAt_radialCurrent [CompleteSpace F] {S : F →L[ℂ] F} (hS : IsSelfAdjoint S)
    {f : ℝ → F} {η c : ℝ} (hη : η ≠ 0)
    (h : HasDerivAt f ((((-(1 / (2 * η)) : ℝ)) : ℂ) • f η + ((c : ℂ) * Complex.I) • S (f η)) η) :
    HasDerivAt (fun t => t * ‖f t‖ ^ 2) 0 η := by
  have hsq := hasDerivAt_normSq_path h
  have hself : (inner ℂ (f η) (f η) : ℂ).re = ‖f η‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hcross := re_inner_real_smul_I_smul_isSelfAdjoint_eq_zero hS c (f η)
  have hval : (inner ℂ ((((-(1 / (2 * η)) : ℝ)) : ℂ) • f η +
        ((c : ℂ) * Complex.I) • S (f η)) (f η) : ℂ).re =
      -(1 / (2 * η)) * ‖f η‖ ^ 2 := by
    rw [inner_add_left, Complex.add_re, hcross, add_zero, inner_smul_left,
      Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hself]
    ring
  rw [hval] at hsq
  have hid : HasDerivAt (fun t : ℝ => t) 1 η := hasDerivAt_id η
  have hprod := hid.mul hsq
  have hzero : (1 : ℝ) * ‖f η‖ ^ 2 + η * (2 * (-(1 / (2 * η)) * ‖f η‖ ^ 2)) = 0 := by
    field_simp
  rw [hzero] at hprod
  exact hprod

end

end GaloisForLFunctions.HTGeometry
