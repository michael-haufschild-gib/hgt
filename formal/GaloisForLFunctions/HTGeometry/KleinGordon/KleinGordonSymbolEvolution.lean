import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonSymbol

/-!
# The propagator symbols solve the Klein–Gordon equation in time

On the Fourier side the free Klein–Gordon evolution is, frequency by frequency, the harmonic
oscillator

`∂ₜ² û(t, ξ) = -⟨ξ⟩² û(t, ξ)`,  `⟨ξ⟩ = √(1 + ‖ξ‖²)`,

and the two propagator symbols `cos(t⟨ξ⟩)` and `sin(t⟨ξ⟩)/⟨ξ⟩` are its fundamental system: the first
carries the initial value, the second the initial velocity.

This file proves exactly that, at the level of the symbols: the two time derivatives, the oscillator
equation, and the four initial conditions. With mathlib's convention for the Fourier transform the
factor `⟨ξ⟩² = 1 + ‖ξ‖²` is the symbol of `1 - (2π)⁻²Δ`, so the equation above is the Klein–Gordon
equation of the physical field.
-/

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem hasDerivAt_freqLine (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => r * kgFreq ξ) (kgFreq ξ) t := by
  simpa using (hasDerivAt_id t).mul_const (kgFreq ξ)

/-! ## The real symbols -/

omit [InnerProductSpace ℝ E] in
/-- The time derivative of the cosine symbol. -/
theorem hasDerivAt_cosFreq (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => Real.cos (r * kgFreq ξ))
      (-(kgFreq ξ * Real.sin (t * kgFreq ξ))) t := by
  have h := (Real.hasDerivAt_cos (t * kgFreq ξ)).comp t (hasDerivAt_freqLine ξ t)
  refine h.congr_deriv ?_
  ring

omit [InnerProductSpace ℝ E] in
/-- The time derivative of the sine symbol. -/
theorem hasDerivAt_sinFreq (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => Real.sin (r * kgFreq ξ))
      (kgFreq ξ * Real.cos (t * kgFreq ξ)) t := by
  have h := (Real.hasDerivAt_sin (t * kgFreq ξ)).comp t (hasDerivAt_freqLine ξ t)
  refine h.congr_deriv ?_
  ring

omit [InnerProductSpace ℝ E] in
/-- **The sine symbol has unit initial velocity**: its time derivative is the cosine symbol. -/
theorem hasDerivAt_sincFreq (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => Real.sin (r * kgFreq ξ) / kgFreq ξ)
      (Real.cos (t * kgFreq ξ)) t := by
  have hne : kgFreq ξ ≠ 0 := ne_of_gt (kgFreq_pos ξ)
  have h := (hasDerivAt_sinFreq ξ t).div_const (kgFreq ξ)
  refine h.congr_deriv ?_
  field_simp

omit [InnerProductSpace ℝ E] in
/-- **The cosine symbol solves the oscillator equation.** -/
theorem hasDerivAt_deriv_cosFreq (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => -(kgFreq ξ * Real.sin (r * kgFreq ξ)))
      (-(kgFreq ξ ^ (2 : ℕ)) * Real.cos (t * kgFreq ξ)) t := by
  have h := ((hasDerivAt_sinFreq ξ t).const_mul (kgFreq ξ)).neg
  refine h.congr_deriv ?_
  ring

omit [InnerProductSpace ℝ E] in
/-- **The sine symbol solves the oscillator equation.** -/
theorem hasDerivAt_deriv_sincFreq (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => Real.cos (r * kgFreq ξ))
      (-(kgFreq ξ ^ (2 : ℕ)) * (Real.sin (t * kgFreq ξ) / kgFreq ξ)) t := by
  have hne : kgFreq ξ ≠ 0 := ne_of_gt (kgFreq_pos ξ)
  have h := hasDerivAt_cosFreq ξ t
  refine h.congr_deriv ?_
  field_simp

/-! ## The complex symbols -/

omit [InnerProductSpace ℝ E] in
theorem hasDerivAt_kgCosSymbol (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => kgCosSymbol r ξ)
      (((-(kgFreq ξ * Real.sin (t * kgFreq ξ)) : ℝ) : ℂ)) t :=
  Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_cosFreq ξ t)

omit [InnerProductSpace ℝ E] in
theorem hasDerivAt_kgSinSymbol (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => kgSinSymbol r ξ) (((Real.cos (t * kgFreq ξ) : ℝ) : ℂ)) t :=
  Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_sincFreq ξ t)

omit [InnerProductSpace ℝ E] in
theorem ofReal_kgCos_second (ξ : E) (t : ℝ) :
    ((-(kgFreq ξ ^ (2 : ℕ)) * Real.cos (t * kgFreq ξ) : ℝ) : ℂ)
      = -((kgFreq ξ ^ (2 : ℕ) : ℝ) : ℂ) * kgCosSymbol t ξ := by
  rw [kgCosSymbol, Complex.ofReal_mul, Complex.ofReal_neg]

omit [InnerProductSpace ℝ E] in
theorem ofReal_kgSin_second (ξ : E) (t : ℝ) :
    ((-(kgFreq ξ ^ (2 : ℕ)) * (Real.sin (t * kgFreq ξ) / kgFreq ξ) : ℝ) : ℂ)
      = -((kgFreq ξ ^ (2 : ℕ) : ℝ) : ℂ) * kgSinSymbol t ξ := by
  rw [kgSinSymbol, Complex.ofReal_mul, Complex.ofReal_neg]

omit [InnerProductSpace ℝ E] in
/-- **The cosine symbol solves the Klein–Gordon oscillator equation**, in the complex form the
Fourier multiplier calculus uses. -/
theorem hasDerivAt_deriv_kgCosSymbol (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => ((-(kgFreq ξ * Real.sin (r * kgFreq ξ)) : ℝ) : ℂ))
      (-((kgFreq ξ ^ (2 : ℕ) : ℝ) : ℂ) * kgCosSymbol t ξ) t := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_deriv_cosFreq ξ t)
  rw [← ofReal_kgCos_second]
  exact h

omit [InnerProductSpace ℝ E] in
/-- **The sine symbol solves the Klein–Gordon oscillator equation.** -/
theorem hasDerivAt_deriv_kgSinSymbol (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => ((Real.cos (r * kgFreq ξ) : ℝ) : ℂ))
      (-((kgFreq ξ ^ (2 : ℕ) : ℝ) : ℂ) * kgSinSymbol t ξ) t := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_deriv_sincFreq ξ t)
  rw [← ofReal_kgSin_second]
  exact h

/-! ## The initial conditions -/

omit [InnerProductSpace ℝ E] in
theorem kgCosSymbol_zero (ξ : E) : kgCosSymbol 0 ξ = 1 := by
  rw [kgCosSymbol]
  norm_num

omit [InnerProductSpace ℝ E] in
theorem kgSinSymbol_zero (ξ : E) : kgSinSymbol 0 ξ = 0 := by
  rw [kgSinSymbol]
  norm_num

omit [InnerProductSpace ℝ E] in
/-- The cosine symbol starts at rest. -/
theorem deriv_kgCosSymbol_zero (ξ : E) : deriv (fun r : ℝ => kgCosSymbol r ξ) 0 = 0 := by
  rw [(hasDerivAt_kgCosSymbol ξ 0).deriv]
  norm_num

omit [InnerProductSpace ℝ E] in
/-- The sine symbol starts with unit velocity. -/
theorem deriv_kgSinSymbol_zero (ξ : E) : deriv (fun r : ℝ => kgSinSymbol r ξ) 0 = 1 := by
  rw [(hasDerivAt_kgSinSymbol ξ 0).deriv]
  norm_num

end GaloisForLFunctions.HTGeometry
