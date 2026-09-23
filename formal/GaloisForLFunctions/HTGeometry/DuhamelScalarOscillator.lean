import GaloisForLFunctions.HTGeometry.KleinGordonPotentialFlow

/-!
# The Duhamel formula for the driven oscillator

At a fixed frequency the evolution with a potential is the driven oscillator

`u''(t) = -ω²u(t) + h(t)`,

whose solution with data `u(0) = c/ω`, `u'(0) = 0` is the Duhamel integral

`u(t) = (cos(tω)/ω) c + ∫₀ᵗ (sin((t-s)ω)/ω) h(s) ds`.

The parameter sits inside the integrand *and* in the limit of integration, which is awkward to
differentiate directly. The addition formula removes the difficulty: expanding `sin((t-s)ω)`
separates the two variables, so the integral becomes a combination of two integrals whose integrands
do not depend on `t`, and the fundamental theorem of calculus applies. The source terms produced by
the two differentiations cancel in the first derivative and reappear exactly once in the second.
-/

namespace GaloisForLFunctions.HTGeometry

open intervalIntegral

variable {ω : ℝ} {c : ℂ} {h : ℝ → ℂ}

/-! ## The two separated integrals -/

/-- The cosine moment of the source. -/
noncomputable def duhamelCosPart (ω : ℝ) (h : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, ((Real.cos (s * ω) : ℝ) : ℂ) * h s

/-- The sine moment of the source. -/
noncomputable def duhamelSinPart (ω : ℝ) (h : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, ((Real.sin (s * ω) : ℝ) : ℂ) * h s

theorem continuous_cosMoment (ω : ℝ) (hh : Continuous h) :
    Continuous fun s : ℝ => ((Real.cos (s * ω) : ℝ) : ℂ) * h s :=
  ((Complex.continuous_ofReal.comp
    (Real.continuous_cos.comp (continuous_id.mul continuous_const))).mul hh)

theorem continuous_sinMoment (ω : ℝ) (hh : Continuous h) :
    Continuous fun s : ℝ => ((Real.sin (s * ω) : ℝ) : ℂ) * h s :=
  ((Complex.continuous_ofReal.comp
    (Real.continuous_sin.comp (continuous_id.mul continuous_const))).mul hh)

theorem hasDerivAt_duhamelCosPart (hh : Continuous h) (t : ℝ) :
    HasDerivAt (duhamelCosPart ω h) (((Real.cos (t * ω) : ℝ) : ℂ) * h t) t :=
  ((continuous_cosMoment ω hh).integral_hasStrictDerivAt 0 t).hasDerivAt

theorem hasDerivAt_duhamelSinPart (hh : Continuous h) (t : ℝ) :
    HasDerivAt (duhamelSinPart ω h) (((Real.sin (t * ω) : ℝ) : ℂ) * h t) t :=
  ((continuous_sinMoment ω hh).integral_hasStrictDerivAt 0 t).hasDerivAt

/-! ## The Duhamel solution -/

/-- The Duhamel solution of the driven oscillator at frequency `ω`. -/
noncomputable def duhamelScalar (ω : ℝ) (c : ℂ) (h : ℝ → ℂ) (t : ℝ) : ℂ :=
  ((Real.cos (t * ω) / ω : ℝ) : ℂ) * c
    + ∫ s in (0 : ℝ)..t, ((Real.sin ((t - s) * ω) / ω : ℝ) : ℂ) * h s

/-- **The addition formula separates the two variables.** -/
theorem duhamelScalar_eq (hω : ω ≠ 0) (hh : Continuous h) (t : ℝ) :
    duhamelScalar ω c h t
      = ((ω : ℝ) : ℂ)⁻¹ * (((Real.cos (t * ω) : ℝ) : ℂ) * c
          + ((Real.sin (t * ω) : ℝ) : ℂ) * duhamelCosPart ω h t
          - ((Real.cos (t * ω) : ℝ) : ℂ) * duhamelSinPart ω h t) := by
  have hωC : ((ω : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω
  have hpt : ∀ s : ℝ, ((Real.sin ((t - s) * ω) / ω : ℝ) : ℂ) * h s
      = ((ω : ℝ) : ℂ)⁻¹ * (((Real.sin (t * ω) : ℝ) : ℂ) * (((Real.cos (s * ω) : ℝ) : ℂ) * h s))
        - ((ω : ℝ) : ℂ)⁻¹
            * (((Real.cos (t * ω) : ℝ) : ℂ) * (((Real.sin (s * ω) : ℝ) : ℂ) * h s)) := by
    intro s
    have hre : Real.sin ((t - s) * ω) / ω
        = ω⁻¹ * (Real.sin (t * ω) * Real.cos (s * ω))
          - ω⁻¹ * (Real.cos (t * ω) * Real.sin (s * ω)) := by
      rw [sub_mul, Real.sin_sub]
      field_simp
    rw [hre]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_inv]
    ring
  have hcos := (continuous_cosMoment (h := h) ω hh).intervalIntegrable
    (μ := MeasureTheory.volume) 0 t
  have hsin := (continuous_sinMoment (h := h) ω hh).intervalIntegrable
    (μ := MeasureTheory.volume) 0 t
  rw [duhamelScalar, duhamelCosPart, duhamelSinPart,
    integral_congr (μ := MeasureTheory.volume) (g := fun s => ((ω : ℝ) : ℂ)⁻¹
        * (((Real.sin (t * ω) : ℝ) : ℂ) * (((Real.cos (s * ω) : ℝ) : ℂ) * h s))
      - ((ω : ℝ) : ℂ)⁻¹
        * (((Real.cos (t * ω) : ℝ) : ℂ) * (((Real.sin (s * ω) : ℝ) : ℂ) * h s)))
      (fun s _ => hpt s),
    integral_sub (((hcos.const_mul _).const_mul _)) ((hsin.const_mul _).const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  have hcast : ((Real.cos (t * ω) / ω : ℝ) : ℂ)
      = ((ω : ℝ) : ℂ)⁻¹ * ((Real.cos (t * ω) : ℝ) : ℂ) := by
    rw [Complex.ofReal_div]
    field_simp
  rw [hcast]
  ring

/-! ## The two time derivatives -/

theorem hasDerivAt_ofReal_cos_mul (ω t : ℝ) :
    HasDerivAt (fun r : ℝ => ((Real.cos (r * ω) : ℝ) : ℂ))
      (-(((ω : ℝ) : ℂ) * ((Real.sin (t * ω) : ℝ) : ℂ))) t := by
  have hre : HasDerivAt (fun r : ℝ => Real.cos (r * ω)) (-(ω * Real.sin (t * ω))) t := by
    have hmul : HasDerivAt (fun r : ℝ => r * ω) ω t := by
      simpa using (hasDerivAt_id t).mul_const ω
    have h := (Real.hasDerivAt_cos (t * ω)).comp t hmul
    have h2 : HasDerivAt (fun r : ℝ => Real.cos (r * ω)) (-Real.sin (t * ω) * ω) t := by
      simpa [Function.comp_def] using h
    exact h2.congr_deriv (by ring)
  refine (hre.ofReal_comp).congr_deriv ?_
  rw [Complex.ofReal_neg, Complex.ofReal_mul]

theorem hasDerivAt_ofReal_sin_mul (ω t : ℝ) :
    HasDerivAt (fun r : ℝ => ((Real.sin (r * ω) : ℝ) : ℂ))
      (((ω : ℝ) : ℂ) * ((Real.cos (t * ω) : ℝ) : ℂ)) t := by
  have hre : HasDerivAt (fun r : ℝ => Real.sin (r * ω)) (ω * Real.cos (t * ω)) t := by
    have hmul : HasDerivAt (fun r : ℝ => r * ω) ω t := by
      simpa using (hasDerivAt_id t).mul_const ω
    have h := (Real.hasDerivAt_sin (t * ω)).comp t hmul
    have h2 : HasDerivAt (fun r : ℝ => Real.sin (r * ω)) (Real.cos (t * ω) * ω) t := by
      simpa [Function.comp_def] using h
    exact h2.congr_deriv (by ring)
  refine (hre.ofReal_comp).congr_deriv ?_
  rw [Complex.ofReal_mul]

/-- **The first derivative of the Duhamel solution**: the two source terms cancel. -/
theorem hasDerivAt_duhamelScalar (hω : ω ≠ 0) (hh : Continuous h) (t : ℝ) :
    HasDerivAt (duhamelScalar ω c h)
      (-(((Real.sin (t * ω) : ℝ) : ℂ) * c) + ((Real.cos (t * ω) : ℝ) : ℂ) * duhamelCosPart ω h t
        + ((Real.sin (t * ω) : ℝ) : ℂ) * duhamelSinPart ω h t) t := by
  have hωC : ((ω : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω
  have heq : duhamelScalar ω c h = fun r : ℝ => ((ω : ℝ) : ℂ)⁻¹
      * (((Real.cos (r * ω) : ℝ) : ℂ) * c
        + ((Real.sin (r * ω) : ℝ) : ℂ) * duhamelCosPart ω h r
        - ((Real.cos (r * ω) : ℝ) : ℂ) * duhamelSinPart ω h r) := by
    funext r
    exact duhamelScalar_eq hω hh r
  rw [heq]
  have hA := hasDerivAt_duhamelCosPart (ω := ω) hh t
  have hB := hasDerivAt_duhamelSinPart (ω := ω) hh t
  have hc := hasDerivAt_ofReal_cos_mul ω t
  have hs := hasDerivAt_ofReal_sin_mul ω t
  have hmain := (((hc.mul_const c).add (hs.mul hA)).sub (hc.mul hB)).const_mul (((ω : ℝ) : ℂ)⁻¹)
  refine hmain.congr_deriv ?_
  field_simp
  ring

/-- **The Duhamel solution solves the driven oscillator equation.** -/
theorem hasDerivAt_deriv_duhamelScalar (hω : ω ≠ 0) (hh : Continuous h) (t : ℝ) :
    HasDerivAt (deriv (duhamelScalar ω c h))
      (-(((ω : ℝ) : ℂ) ^ (2 : ℕ) * duhamelScalar ω c h t) + h t) t := by
  have hderiv : deriv (duhamelScalar ω c h) = fun r : ℝ =>
      -(((Real.sin (r * ω) : ℝ) : ℂ) * c) + ((Real.cos (r * ω) : ℝ) : ℂ) * duhamelCosPart ω h r
        + ((Real.sin (r * ω) : ℝ) : ℂ) * duhamelSinPart ω h r := by
    funext r
    exact (hasDerivAt_duhamelScalar hω hh r).deriv
  rw [hderiv]
  have hA := hasDerivAt_duhamelCosPart (ω := ω) hh t
  have hB := hasDerivAt_duhamelSinPart (ω := ω) hh t
  have hc := hasDerivAt_ofReal_cos_mul ω t
  have hs := hasDerivAt_ofReal_sin_mul ω t
  have hmain := (((hs.mul_const c).neg).add (hc.mul hA)).add (hs.mul hB)
  refine hmain.congr_deriv ?_
  rw [duhamelScalar_eq hω hh t]
  have hW : ((ω : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω
  have hpy : ((Real.cos (t * ω) : ℝ) : ℂ) ^ (2 : ℕ) + ((Real.sin (t * ω) : ℝ) : ℂ) ^ (2 : ℕ) = 1 := by
    have hreal := Real.sin_sq_add_cos_sq (t * ω)
    have hcast : ((Real.sin (t * ω) ^ (2 : ℕ) + Real.cos (t * ω) ^ (2 : ℕ) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [hreal]
    simp only [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_one] at hcast
    linear_combination hcast
  have hsq : ∀ Z : ℂ, ((ω : ℝ) : ℂ) ^ (2 : ℕ) * (((ω : ℝ) : ℂ)⁻¹ * Z) = ((ω : ℝ) : ℂ) * Z := by
    intro Z
    rw [pow_two, mul_assoc, ← mul_assoc (((ω : ℝ) : ℂ)) (((ω : ℝ) : ℂ)⁻¹),
      mul_inv_cancel₀ hW, one_mul]
  rw [hsq]
  linear_combination h t * hpy

end GaloisForLFunctions.HTGeometry
