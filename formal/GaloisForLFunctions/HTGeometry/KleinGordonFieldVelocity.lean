import GaloisForLFunctions.HTGeometry.KleinGordonDuhamelFirstDerivative

/-!
# The field-level solution is continuously differentiable

Adding the derivative of the free field (statement 87) to the derivative of the Duhamel term
(statement 96) gives the velocity of the mild solution in closed form:

`∂ₜu(t) = -sin(t⟨D⟩)g + cos(t⟨D⟩)h + ∫₀ᵗ cos((t-s)⟨D⟩) W u(s) ds`

for the Cauchy data `u(0) = ⟨D⟩⁻¹g`, `∂ₜu(0) = h`. One power of `⟨D⟩⁻¹` on the position datum is all
the regularity used; the velocity datum and the perturbation are arbitrary.

This is the classical variation-of-constants formula for the velocity, and at `t = 0` it returns the
velocity datum, so the Cauchy problem is solved in the `C¹` sense with the data one prescribes.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Velocity

variable {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- **The mild solution of the field equation is differentiable**, with the classical velocity. -/
theorem hasDerivAt_kgFieldMild (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    HasDerivAt (kgFieldMild W (kgFreqInvOp g) h)
      (-(kgSinOp t g) + kgCosOp t h
        + ∫ s in (0 : ℝ)..t, kgCosOp (t - s) (W (kgFieldMild W (kgFreqInvOp g) h s))) t := by
  have hu : Continuous (kgFieldMild W (kgFreqInvOp g) h) :=
    continuous_kgFieldMild hb0 hW (kgFreqInvOp g) h
  have hgf : Continuous fun s : ℝ => W (kgFieldMild W (kgFreqInvOp g) h s) :=
    W.continuous.comp hu
  have hsum := (hasDerivAt_kgFieldFree g h t).add (hasDerivAt_kgDuhamel hgf t)
  rw [kgDuhamel_deriv_eq hgf t] at hsum
  refine hsum.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall fun r => ?_
  simp only [Pi.add_apply]
  exact kgFieldMild_eq_separated hb0 hW (kgFreqInvOp g) h r

/-- **The velocity of the mild solution**, in closed form. -/
theorem deriv_kgFieldMild (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    deriv (kgFieldMild W (kgFreqInvOp g) h) t
      = -(kgSinOp t g) + kgCosOp t h
        + ∫ s in (0 : ℝ)..t, kgCosOp (t - s) (W (kgFieldMild W (kgFreqInvOp g) h s)) :=
  (hasDerivAt_kgFieldMild hb0 hW g h t).deriv

/-- **The solution starts at the position datum.** -/
theorem kgFieldMild_at_zero (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    kgFieldMild W (kgFreqInvOp g) h 0 = kgFreqInvOp g :=
  kgFieldMild_zero hb0 hW (kgFreqInvOp g) h

/-- **The solution starts with the velocity datum.** -/
theorem deriv_kgFieldMild_at_zero (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    deriv (kgFieldMild W (kgFreqInvOp g) h) 0 = h := by
  rw [deriv_kgFieldMild hb0 hW g h 0, intervalIntegral.integral_same, kgCosOp_zero, kgSinOp_zero]
  simp

/-- **The Cauchy problem of the field equation is solved in the `C¹` sense.** For every `g, h` in
`L²` and every bounded perturbation there is a differentiable curve with position datum `⟨D⟩⁻¹g`,
velocity datum `h`, satisfying the field-level Duhamel formula. -/
theorem exists_kgFieldMild_c1 (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    ∃ u : ℝ → Lp ℂ 2 (volume : Measure E),
      (∀ t : ℝ, HasDerivAt u (deriv u t) t) ∧
      (∀ t : ℝ, u t = kgFieldFree (kgFreqInvOp g) h t
        + ∫ s in (0 : ℝ)..t, kgFieldKernel W t s (u s)) ∧
      u 0 = kgFreqInvOp g ∧ deriv u 0 = h := by
  refine ⟨kgFieldMild W (kgFreqInvOp g) h, fun t => ?_,
    kgFieldMild_eq hb0 hW (kgFreqInvOp g) h,
    kgFieldMild_at_zero hb0 hW g h, deriv_kgFieldMild_at_zero hb0 hW g h⟩
  have hd := hasDerivAt_kgFieldMild hb0 hW g h t
  rwa [hd.deriv]

end Velocity

end GaloisForLFunctions.HTGeometry
