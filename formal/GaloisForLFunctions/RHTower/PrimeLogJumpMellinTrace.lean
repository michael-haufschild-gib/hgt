import GaloisForLFunctions.RHTower.PrimeLogJumpMellinFrame

/-!
# The first Mellin boundary trace of the jump packet

The positive-ray Mellin evaluation of the essential-phase jump packet is

```text
M_κ(s) = ∫_A^B x^{-s} (cos (κ x) − μ_κ) dx.
```

One integration by parts moves the oscillation onto the endpoints:

```text
κ M_κ(s) = B^{-s} sin (κ B) − A^{-s} sin (κ A) − (sin (κ B) − sin (κ A)) H(s)
             + s ∫_A^B x^{-s-1} sin (κ x) dx,
```

and a second integration by parts shows the remaining integral is `O(1/κ)`.  So the discontinuous
packet is *exactly first order* at the Mellin boundary: the endpoint jumps survive, in contrast with
the all-orders flatness of a smooth amplitude.
-/

namespace GaloisForLFunctions.RHTower

open Complex intervalIntegral

variable {A B κ : ℝ}

/-- The derivative of the Mellin kernel along the positive ray. -/
theorem hasDerivAt_cpow_ofReal {s : ℂ} {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => ((t : ℂ)) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x := by
  have hx' : (0 : ℝ) < ((x : ℂ)).re ∨ ((x : ℂ)).im ≠ 0 := Or.inl (by simpa using hx)
  have h := (Complex.hasDerivAt_cpow_const (x := (x : ℂ)) (c := -s) hx')
  exact h.comp_ofReal

/-- The primitive of the modulating cosine. -/
theorem hasDerivAt_sin_div (hκ : κ ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => ((Real.sin (κ * t) : ℝ) : ℂ) / (κ : ℂ))
      (((Real.cos (κ * x) : ℝ) : ℂ)) x := by
  have hκ' : ((κ : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ
  have h1 : HasDerivAt (fun t : ℝ => Real.sin (κ * t)) (Real.cos (κ * x) * κ) x := by
    simpa [mul_comm] using
      (Real.hasDerivAt_sin (κ * x)).comp x ((hasDerivAt_id x).const_mul κ)
  have h2 : HasDerivAt (fun t : ℝ => ((Real.sin (κ * t) : ℝ) : ℂ))
      (((Real.cos (κ * x) * κ : ℝ) : ℂ)) x := h1.ofReal_comp
  have h3 := h2.div_const (κ : ℂ)
  refine h3.congr_deriv ?_
  push_cast
  field_simp

/-- **One integration by parts.**  The oscillation moves to the endpoints. -/
theorem integral_cpow_mul_cos (hA : 0 < A) (hAB : A < B) (hκ : κ ≠ 0) (s : ℂ) :
    (κ : ℂ) * ∫ x in A..B, (x : ℂ) ^ (-s) * ((Real.cos (κ * x) : ℝ) : ℂ)
      = (B : ℂ) ^ (-s) * ((Real.sin (κ * B) : ℝ) : ℂ)
        - (A : ℂ) ^ (-s) * ((Real.sin (κ * A) : ℝ) : ℂ)
        + s * ∫ x in A..B, (x : ℂ) ^ (-s - 1) * ((Real.sin (κ * x) : ℝ) : ℂ) := by
  have hκ' : ((κ : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ
  have hpos : ∀ x ∈ Set.uIcc A B, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le (le_of_lt hAB)] at hx
    linarith [hx.1]
  have hu : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun t : ℝ => ((t : ℂ)) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x :=
    fun x hx => hasDerivAt_cpow_ofReal (hpos x hx)
  have hv : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun t : ℝ => ((Real.sin (κ * t) : ℝ) : ℂ) / (κ : ℂ))
        (((Real.cos (κ * x) : ℝ) : ℂ)) x := fun x _ => hasDerivAt_sin_div hκ x
  have hu' : IntervalIntegrable (fun x : ℝ => -s * (x : ℂ) ^ (-s - 1)) MeasureTheory.volume A B := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    refine (continuousAt_const.mul ?_).continuousWithinAt
    exact ((hasDerivAt_cpow_ofReal (s := s + 1) (hpos x hx)).continuousAt).congr (by
      funext t
      ring_nf)
  have hv' : IntervalIntegrable (fun x : ℝ => ((Real.cos (κ * x) : ℝ) : ℂ))
      MeasureTheory.volume A B := by
    apply Continuous.intervalIntegrable
    exact Complex.continuous_ofReal.comp
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hleft : ∫ x in A..B, ((x : ℂ) ^ (-s)) * ((Real.cos (κ * x) : ℝ) : ℂ)
      = ((B : ℂ) ^ (-s) * (((Real.sin (κ * B) : ℝ) : ℂ) / (κ : ℂ))
        - (A : ℂ) ^ (-s) * (((Real.sin (κ * A) : ℝ) : ℂ) / (κ : ℂ)))
        - ∫ x in A..B, (-s * (x : ℂ) ^ (-s - 1)) * (((Real.sin (κ * x) : ℝ) : ℂ) / (κ : ℂ)) :=
    hIBP
  rw [hleft]
  have hrw : (∫ x in A..B, (-s * (x : ℂ) ^ (-s - 1)) * (((Real.sin (κ * x) : ℝ) : ℂ) / (κ : ℂ)))
      = (-s / (κ : ℂ)) * ∫ x in A..B, (x : ℂ) ^ (-s - 1) * ((Real.sin (κ * x) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro x _
    field_simp
    ring
  rw [hrw]
  field_simp
  ring

end GaloisForLFunctions.RHTower
