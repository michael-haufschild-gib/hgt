import GaloisForLFunctions.HTGeometry.CompositionImageCircle

/-!
# A circle floor cannot drive composition separation

The separation criterion asks for a floor `Λ` with `Λ ≤ log ‖f w‖` on a whole circle, beating a
multiple of the logarithm of the circle's radius.  For the exponential no such floor exists: on the
circle of radius `s` the modulus of `exp` dips to `e^{-s}`, so every admissible floor satisfies
`Λ ≤ -s`.  Any argument that supplies the floor from a *minimum* modulus is therefore insufficient
for separation, however the radius is chosen.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- The exponential dips to `e^{-s}` on the circle of radius `s`. -/
theorem exists_norm_exp_eq_exp_neg (s : ℝ) (hs : 0 ≤ s) :
    ∃ w : ℂ, ‖w‖ = s ∧ ‖Complex.exp w‖ = Real.exp (-s) := by
  refine ⟨(-s : ℝ), ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hs]
  · rw [Complex.norm_exp]
    simp

/-- **Every circle floor for the exponential is at most `-s`.**  So a floor obtained from a minimum
modulus cannot exceed a multiple of `log s`, and the separation criterion
`C log⁺(s + c) < Λ` is unsatisfiable for large `s`. -/
theorem circle_floor_le_neg (s Λ : ℝ) (hs : 0 ≤ s)
    (hfloor : ∀ w : ℂ, ‖w‖ = s → Λ ≤ Real.log ‖Complex.exp w‖) :
    Λ ≤ -s := by
  obtain ⟨w, hw, hval⟩ := exists_norm_exp_eq_exp_neg s hs
  have := hfloor w hw
  rw [hval, Real.log_exp] at this
  exact this

/-! ## The displacement floor is lossy -/

/-- The displacement of the exponential stays below `1` somewhere on every circle. -/
theorem exists_norm_exp_sub_one_le (r : ℝ) (hr : 0 ≤ r) :
    ∃ z : ℂ, ‖z‖ = r ∧ ‖Complex.exp z - 1‖ ≤ 1 := by
  refine ⟨(-r : ℝ), ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hr]
  · have hval : Complex.exp ((-r : ℝ) : ℂ) = ((Real.exp (-r) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_exp]
    rw [hval]
    have hsub : ((Real.exp (-r) : ℝ) : ℂ) - 1 = ((Real.exp (-r) - 1 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs]
    have h1 : Real.exp (-r) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have h0 : 0 < Real.exp (-r) := Real.exp_pos _
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- **Every displacement floor for the exponential is at most one.**  So the disc that a
minimum-modulus argument puts inside the image has radius `O(1)`, while the function itself reaches
modulus `e^r − 1` on the same circle: the route loses everything for a function of positive order. -/
theorem displacement_floor_le_one (r ε : ℝ) (hr : 0 ≤ r)
    (hfloor : ∀ z : ℂ, ‖z‖ = r → ε ≤ ‖Complex.exp z - 1‖) :
    ε ≤ 1 := by
  obtain ⟨z, hz, hval⟩ := exists_norm_exp_sub_one_le r hr
  exact le_trans (hfloor z hz) hval

end GaloisForLFunctions.HTGeometry
