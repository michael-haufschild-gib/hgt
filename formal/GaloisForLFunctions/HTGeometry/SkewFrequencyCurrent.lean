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

omit [NormedSpace ℝ F] in
/-- The real part of an inner product against a real multiple of the same vector. -/
theorem re_inner_real_smul_self (r : ℝ) (x : F) :
    (inner ℂ (((r : ℝ) : ℂ) • x) x : ℂ).re = r * ‖x‖ ^ 2 := by
  rw [inner_smul_left, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  have hself : (inner ℂ x x : ℂ).re = ‖x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hself]
  ring

/-- **Frequency-current conservation.**  A path obeying the skew frequency equation has constant
radial current `η ‖f η‖²`: the self-adjoint block contributes nothing, so the whole derivative
comes from the explicit radial term and cancels it exactly. -/
theorem hasDerivAt_radialCurrent [CompleteSpace F] {S : F →L[ℂ] F} (hS : IsSelfAdjoint S)
    {f : ℝ → F} {η c : ℝ} (hη : η ≠ 0)
    (h : HasDerivAt f ((((-(1 / (2 * η)) : ℝ)) : ℂ) • f η + ((c : ℂ) * Complex.I) • S (f η)) η) :
    HasDerivAt (fun t => t * ‖f t‖ ^ 2) 0 η := by
  have hsq := hasDerivAt_normSq_path h
  have hcross := re_inner_real_smul_I_smul_isSelfAdjoint_eq_zero hS c (f η)
  have hval : (inner ℂ ((((-(1 / (2 * η)) : ℝ)) : ℂ) • f η +
        ((c : ℂ) * Complex.I) • S (f η)) (f η) : ℂ).re =
      -(1 / (2 * η)) * ‖f η‖ ^ 2 := by
    rw [inner_add_left, Complex.add_re, hcross, add_zero]
    exact re_inner_real_smul_self _ _
  rw [hval] at hsq
  have hprod := (hasDerivAt_id η).mul hsq
  simp only [id_eq] at hprod
  have hcancel : η * (2 * (-(1 / (2 * η)) * ‖f η‖ ^ 2)) = -‖f η‖ ^ 2 := by
    field_simp
  have hzero : (1 : ℝ) * ‖f η‖ ^ 2 + η * (2 * (-(1 / (2 * η)) * ‖f η‖ ^ 2)) = 0 := by
    rw [hcancel]; ring
  rw [hzero] at hprod
  exact hprod

/-! ## The conserved current -/

open Set in
/-- **Constancy of the radial current on a half-line.**  A vanishing derivative on an open
preconnected set makes the current constant there.  This is `(10)`. -/
theorem radialCurrent_const_of_hasDerivAt {g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hs' : IsPreconnected s) (hd : ∀ x ∈ s, HasDerivAt g 0 x) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) : g a = g b := by
  refine hs.is_const_of_deriv_eq_zero hs' (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt) ?_ ha hb
  intro x hx
  simpa using (hd x hx).deriv

open Set in
/-- The current is constant on the positive half-line. -/
theorem radialCurrent_const_Ioi [CompleteSpace F] {S : F →L[ℂ] F} (hS : IsSelfAdjoint S)
    {f : ℝ → F} {c : ℝ}
    (h : ∀ η ∈ Ioi (0 : ℝ),
      HasDerivAt f ((((-(1 / (2 * η)) : ℝ)) : ℂ) • f η + ((c : ℂ) * Complex.I) • S (f η)) η)
    {a b : ℝ} (ha : a ∈ Ioi (0 : ℝ)) (hb : b ∈ Ioi (0 : ℝ)) :
    a * ‖f a‖ ^ 2 = b * ‖f b‖ ^ 2 :=
  radialCurrent_const_of_hasDerivAt isOpen_Ioi (isPreconnected_Ioi)
    (fun η hη => hasDerivAt_radialCurrent hS (ne_of_gt hη) (h η hη)) ha hb

open Set in
/-- The current is constant on the negative half-line. -/
theorem radialCurrent_const_Iio [CompleteSpace F] {S : F →L[ℂ] F} (hS : IsSelfAdjoint S)
    {f : ℝ → F} {c : ℝ}
    (h : ∀ η ∈ Iio (0 : ℝ),
      HasDerivAt f ((((-(1 / (2 * η)) : ℝ)) : ℂ) • f η + ((c : ℂ) * Complex.I) • S (f η)) η)
    {a b : ℝ} (ha : a ∈ Iio (0 : ℝ)) (hb : b ∈ Iio (0 : ℝ)) :
    a * ‖f a‖ ^ 2 = b * ‖f b‖ ^ 2 :=
  radialCurrent_const_of_hasDerivAt isOpen_Iio (isPreconnected_Iio)
    (fun η hη => hasDerivAt_radialCurrent hS (ne_of_lt hη) (h η hη)) ha hb

open Set MeasureTheory in
/-- **`L²` Liouville.**  A square-integrable solution of the skew frequency equation vanishes on
the positive ray: the conserved current forces `‖f η‖² = C/η`, and `∫₁^∞ dη/η` diverges unless
`C = 0`. -/
theorem eq_zero_of_integrable_radialCurrent [CompleteSpace F] {S : F →L[ℂ] F}
    (hS : IsSelfAdjoint S) {f : ℝ → F} {c : ℝ}
    (h : ∀ η ∈ Ioi (0 : ℝ),
      HasDerivAt f ((((-(1 / (2 * η)) : ℝ)) : ℂ) • f η + ((c : ℂ) * Complex.I) • S (f η)) η)
    (hint : IntegrableOn (fun η => ‖f η‖ ^ 2) (Ioi (0 : ℝ))) :
    ∀ η ∈ Ioi (0 : ℝ), f η = 0 := by
  have hone : (1 : ℝ) ∈ Ioi (0 : ℝ) := by norm_num
  set C : ℝ := 1 * ‖f 1‖ ^ 2 with hCdef
  have hconst : ∀ η ∈ Ioi (0 : ℝ), η * ‖f η‖ ^ 2 = C := fun η hη =>
    radialCurrent_const_Ioi hS h hη hone
  have hCnn : 0 ≤ C := by
    rw [hCdef]; positivity
  have hCzero : C = 0 := by
    by_contra hC
    have hCpos : 0 < C := lt_of_le_of_ne hCnn (Ne.symm hC)
    have hval : ∀ η ∈ Ioi (1 : ℝ), ‖f η‖ ^ 2 = C * η ^ (-1 : ℝ) := by
      intro η hη
      have hη0 : (0 : ℝ) < η := lt_trans zero_lt_one hη
      have := hconst η (mem_Ioi.mpr hη0)
      rw [Real.rpow_neg_one]
      field_simp at this ⊢
      linarith [this]
    have hsub : IntegrableOn (fun η => ‖f η‖ ^ 2) (Ioi (1 : ℝ)) :=
      hint.mono_set (fun x hx => mem_Ioi.mpr (lt_trans zero_lt_one hx))
    have hCI : IntegrableOn (fun η : ℝ => C * η ^ (-1 : ℝ)) (Ioi (1 : ℝ)) := by
      refine hsub.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hval x hx
    have hpow : IntegrableOn (fun η : ℝ => η ^ (-1 : ℝ)) (Ioi (1 : ℝ)) := by
      have := hCI.const_mul C⁻¹
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      field_simp
    have hcontra := (integrableOn_Ioi_rpow_iff (t := (1 : ℝ)) (s := (-1 : ℝ))
      (by norm_num)).mp hpow
    exact absurd hcontra (lt_irrefl _)
  intro η hη
  have hη0 : (0 : ℝ) < η := hη
  have := hconst η hη
  rw [hCzero] at this
  have hz : ‖f η‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp this with h1 | h2
    · exact absurd h1 (ne_of_gt hη0)
    · exact h2
  have : ‖f η‖ = 0 := by
    nlinarith [norm_nonneg (f η), hz]
  exact norm_eq_zero.mp this

end

end GaloisForLFunctions.HTGeometry
