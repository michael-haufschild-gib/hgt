import GaloisForLFunctions.RHTower.ConstrainedProlatePointwiseRepresentative

/-!
# The prolate evaluation identity and the two-mode centre cancellation

For a nonzero time-band eigenmode `T_a f = χ f` with canonical compact representative `e`, the
Fourier eigen-equation holds pointwise on the open aperture, and the Fourier transform at frequency
zero is the plain integral.  Evaluating at the centre therefore gives the exact identity

`∫ e = χ · e 0`,

which is the coordinate law relating the vanishing-integral constraint to the centre value of a
mode.

The consequence for the two-mode contrast is an exact cancellation: the contrast
`ℓ₁ e₀ - ℓ₀ e₁` has centre value

`(χ₁ - χ₀) · e₀ 0 · e₁ 0`,

so its centre value is controlled by the *difference of the two eigenvalues*, not by their size.
Since both eigenvalues tend to one, this difference is the whole reason the constrained contrast is
small at the centre; no asymptotics are used to see it.

The aperture must be strictly positive so that the centre is interior.
-/

noncomputable section

open MeasureTheory Set FourierTransform

namespace RHTower

/-- The Fourier transform of an integrable function at frequency zero is its integral. -/
theorem fourier_zero_eq_integral (g : ℝ → ℂ) : 𝓕 g 0 = ∫ x : ℝ, g x := by
  rw [Real.fourier_eq]
  simp

/-- **Prolate evaluation identity.**  The integral coordinate of a nonzero time-band eigenmode is
its eigenvalue times the centre value of its canonical compact representative. -/
theorem timeBandEigenSourceIntegral_eq_mul_pointwiseSource_zero
    (a : ℝ) (ha : 0 < a) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) :
    timeBandEigenSourceIntegral a f χ hχ heig
      = χ * timeBandEigenPointwiseSource a f χ hχ heig 0 := by
  have hmem : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith, ha⟩
  have hkey :=
    timeBandEigenPointwiseSource_eq_inv_mul_fourier_interior a ha.le f χ hχ heig hmem
  have hF : 𝓕 (timeBandEigenPointwiseSource a f χ hχ heig) 0
      = timeBandEigenSourceIntegral a f χ hχ heig := by
    rw [fourier_zero_eq_integral]
    rfl
  rw [hF] at hkey
  field_simp at hkey
  linear_combination -hkey

/-- The centre value of a mode is its integral coordinate divided by its eigenvalue. -/
theorem timeBandEigenPointwiseSource_zero_eq
    (a : ℝ) (ha : 0 < a) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) :
    timeBandEigenPointwiseSource a f χ hχ heig 0
      = χ⁻¹ * timeBandEigenSourceIntegral a f χ hχ heig := by
  rw [timeBandEigenSourceIntegral_eq_mul_pointwiseSource_zero a ha f χ hχ heig,
    ← mul_assoc, inv_mul_cancel₀ hχ, one_mul]

/-- **Two-mode centre cancellation.**  The universal two-mode constrained contrast has centre value
exactly the *difference* of the two eigenvalues times the product of the two centre values.  The
constraint coefficients are the integral coordinates, and the evaluation identity turns each of
them into its own eigenvalue times its own centre value, so the two products differ only through
`χ₁ - χ₀`. -/
theorem timeBandTwoModeConstrainedSource_zero_eq
    (a : ℝ) (ha : 0 < a)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    timeBandTwoModeConstrainedSource a f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁ 0
      = (χ₁ - χ₀) * timeBandEigenPointwiseSource a f₀ χ₀ hχ₀ heig₀ 0
          * timeBandEigenPointwiseSource a f₁ χ₁ hχ₁ heig₁ 0 := by
  have h₀ := timeBandEigenSourceIntegral_eq_mul_pointwiseSource_zero a ha f₀ χ₀ hχ₀ heig₀
  have h₁ := timeBandEigenSourceIntegral_eq_mul_pointwiseSource_zero a ha f₁ χ₁ hχ₁ heig₁
  show timeBandEigenSourceIntegral a f₁ χ₁ hχ₁ heig₁ *
      timeBandEigenPointwiseSource a f₀ χ₀ hχ₀ heig₀ 0 -
    timeBandEigenSourceIntegral a f₀ χ₀ hχ₀ heig₀ *
      timeBandEigenPointwiseSource a f₁ χ₁ hχ₁ heig₁ 0 = _
  rw [h₀, h₁]
  ring

/-- The centre value of the two-mode contrast vanishes exactly when the two eigenvalues agree or one
of the two centre values vanishes.  In particular the contrast is centred by the eigenvalue gap. -/
theorem timeBandTwoModeConstrainedSource_zero_eq_zero_iff
    (a : ℝ) (ha : 0 < a)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    timeBandTwoModeConstrainedSource a f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁ 0 = 0 ↔
      χ₁ = χ₀ ∨ timeBandEigenPointwiseSource a f₀ χ₀ hχ₀ heig₀ 0 = 0 ∨
        timeBandEigenPointwiseSource a f₁ χ₁ hχ₁ heig₁ 0 = 0 := by
  rw [timeBandTwoModeConstrainedSource_zero_eq a ha f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h' | h'
    · rcases mul_eq_zero.1 h' with h'' | h''
      · exact Or.inl (by linear_combination h'')
      · exact Or.inr (Or.inl h'')
    · exact Or.inr (Or.inr h')
  · rintro (h | h | h)
    · have hz : χ₁ - χ₀ = 0 := by rw [h]; ring
      rw [hz]; ring
    · rw [h]; ring
    · rw [h]; ring

end RHTower

end
