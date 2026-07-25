import Mathlib

/-!
# The center-mixed density as a full-line integral

The Hedenmalm center-mixed density of an even kernel `Φ`,

`D a t = ∫_{r > 0} r * sinh (a r) * Φ (r/2 + t) * Φ (r/2 - t) dr`,

has an integrand which is **even in `r`**: negating `r` flips the sign of both `r` and `sinh (a r)`
and exchanges the two arguments of `Φ`, which the evenness of `Φ` undoes.  Hence the half-line
integral is half of a full-line integral.

This is the step that removes the constraint `r > 0` and makes the substitution `u = r/2 + t`,
`v = r/2 - t` a genuine change of variables on `ℝ²`, which is what lets the double integral
factor through the Fourier transform of `Φ`.
-/

open MeasureTheory

namespace HTGeometry

/-- An even integrable function has half its total integral on the positive half-line. -/
theorem integral_Ioi_zero_of_even {f : ℝ → ℝ} (heven : ∀ x, f (-x) = f x)
    (hint : Integrable f) :
    ∫ x in Set.Ioi (0 : ℝ), f x = (∫ x, f x) / 2 := by
  have hrefl : ∫ x in Set.Ioi (0 : ℝ), f x = ∫ x in Set.Iic (0 : ℝ), f x := by
    have h := integral_comp_neg_Ioi (0 : ℝ) f
    simpa [heven] using h
  have hsplit : (∫ x in Set.Iic (0 : ℝ), f x) + ∫ x in Set.Ioi (0 : ℝ), f x = ∫ x, f x := by
    have h := MeasureTheory.integral_add_compl (measurableSet_Iic (a := (0 : ℝ))) hint
    simpa [Set.compl_Iic] using h
  rw [← hrefl] at hsplit
  linarith

/-- The center-mixed integrand of an even kernel. -/
noncomputable def centerMixedIntegrand (Φ : ℝ → ℝ) (a t r : ℝ) : ℝ :=
  r * Real.sinh (a * r) * (Φ (r / 2 + t) * Φ (r / 2 - t))

/-- **The center-mixed integrand is even in `r`.** -/
theorem centerMixedIntegrand_even (Φ : ℝ → ℝ) (heven : ∀ x, Φ (-x) = Φ x) (a t r : ℝ) :
    centerMixedIntegrand Φ a t (-r) = centerMixedIntegrand Φ a t r := by
  unfold centerMixedIntegrand
  have h1 : Φ (-r / 2 + t) = Φ (r / 2 - t) := by
    rw [← heven (r / 2 - t)]
    ring_nf
  have h2 : Φ (-r / 2 - t) = Φ (r / 2 + t) := by
    rw [← heven (r / 2 + t)]
    ring_nf
  rw [h1, h2, show a * -r = -(a * r) by ring, Real.sinh_neg]
  ring

/-- **The center-mixed density is half a full-line integral.**  For an even kernel the constraint
`r > 0` is removable. -/
theorem integral_Ioi_centerMixedIntegrand (Φ : ℝ → ℝ) (heven : ∀ x, Φ (-x) = Φ x) (a t : ℝ)
    (hint : Integrable (centerMixedIntegrand Φ a t)) :
    ∫ r in Set.Ioi (0 : ℝ), centerMixedIntegrand Φ a t r
      = (∫ r, centerMixedIntegrand Φ a t r) / 2 :=
  integral_Ioi_zero_of_even (centerMixedIntegrand_even Φ heven a t) hint

end HTGeometry
