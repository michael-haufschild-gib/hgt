import GaloisForLFunctions.HTGeometry.PolydiscCoeffVanishing
import GaloisForLFunctions.HTGeometry.PolydiscCauchyLocal

/-!
# The multi-index Schwarz estimate for a locally holomorphic function

The polydisc expansion and the Schwarz estimate built on it need the function only on a polydisc
strictly larger than the contour, not on the whole space.  Combining the local Cauchy formula
`polydiscCauchyFormula_of_differentiableOn` with the expansion criterion
`polydiscSeries_hasSum_of_cauchy` gives the expansion, and the estimate then follows from its
`HasSum`-parameterized form.

This is what a chartwise Siegel argument needs: the numerators and denominators of a local
presentation of a meromorphic function are holomorphic on a polydisc around their centre and
nowhere else.
-/

open MeasureTheory Complex Set
open scoped Real

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **The polydisc expansion of a locally holomorphic function.** -/
theorem polydiscSeries_hasSum_of_differentiableOn {f : (Fin n → ℂ) → E} {c : Fin n → ℂ}
    {R R₁ : ℝ} (hR : 0 < R) (hRR₁ : R < R₁)
    (hf : DifferentiableOn ℂ f (polydiscSet c (fun _ => R₁)))
    {M : ℝ} (hM : ∀ θ : Fin n → ℝ, ‖f (torusMap c (fun _ => R) θ)‖ ≤ M)
    {y : Fin n → ℂ} (hy : ‖y‖ < R) :
    HasSum (fun k => polydiscSeries f c R k fun _ => y) (f (c + y)) := by
  refine polydiscSeries_hasSum_of_cauchy hR ?_ ?_ hM hy
  · refine hf.continuousOn.mono ?_
    intro z hz i
    have hzi : ‖z i - c i‖ = R := hz i
    rw [Metric.mem_ball, Complex.dist_eq, hzi]
    exact hRR₁
  · intro z hz
    exact polydiscCauchyFormula_of_differentiableOn n f c (fun _ => R₁) (fun _ => R) hf
      (fun _ => le_of_lt hR) (fun _ => hRR₁) z hz

/-- **The multi-index Schwarz estimate for a locally holomorphic function.** -/
theorem norm_le_of_polydiscCoeff_vanish_of_differentiableOn {N : ℕ} {f : (Fin n → ℂ) → E}
    {c : Fin n → ℂ} {R R₁ r M : ℝ} (hR : 0 < R) (hRR₁ : R < R₁)
    (hf : DifferentiableOn ℂ f (polydiscSet c (fun _ => R₁)))
    (hr : 0 ≤ r) (hrR : r < R)
    (hM : ∀ θ : Fin n → ℝ, ‖f (torusMap c (fun _ => R) θ)‖ ≤ M)
    (hvan : ∀ m : Fin n → ℕ, ∑ i, m i < N → polydiscCoeff f c R m = 0)
    {y : Fin n → ℂ} (hy : ‖y‖ ≤ r) :
    ‖f (c + y)‖ ≤ M * (((N + 1) ^ n : ℕ) : ℝ) * (r / R) ^ N *
      ∑' j : ℕ, (((j + 1) ^ n : ℕ) : ℝ) * (r / R) ^ j :=
  norm_le_of_polydiscCoeff_vanish_of_hasSum c hR hr hrR hM hvan hy
    (polydiscSeries_hasSum_of_differentiableOn hR hRR₁ hf hM (lt_of_le_of_lt hy hrR))

end GaloisForLFunctions.HTGeometry
