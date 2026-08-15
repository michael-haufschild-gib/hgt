import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Whole-line integration by parts through a vanishing Wronskian

A Schrödinger-type operator `ψ ↦ ψ″ + q ψ` is symmetric for the `L²(ℝ)` pairing because the
difference of the two pairings is the integral of an exact derivative,

```text
u″ v - u v″ = (u′ v - u v′)′ ,
```

and the Wronskian `u′v - uv′` vanishes at both ends for decaying solutions.  This file proves that
in the form the prolate-to-oscillator comparison uses: a derivative whose primitive tends to zero at
`±∞` integrates to zero over the line, and hence the Wronskian identity gives the symmetry with no
operator-theoretic input at all.

The potential `q` never appears: it cancels pointwise, so the statement is purely about the
second-derivative part.
-/

open MeasureTheory Filter Set

open scoped Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **A derivative with vanishing limits at both ends integrates to zero over the line.** -/
theorem integral_deriv_eq_zero_of_tendsto_zero {W W' : ℝ → ℝ}
    (hW : ∀ x, HasDerivAt W (W' x) x) (hint : Integrable W')
    (hplus : Tendsto W atTop (𝓝 0)) (hminus : Tendsto W atBot (𝓝 0)) :
    ∫ x, W' x = 0 := by
  have hcont : Continuous W := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    exact (hW x).continuousAt
  have h2 : ∫ x in Ioi (0 : ℝ), W' x = 0 - W 0 := by
    refine MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
      (hcont.continuousWithinAt) (fun x _ => hW x) hint.integrableOn hplus
  have h1 : ∫ x in Iic (0 : ℝ), W' x = W 0 - 0 := by
    refine MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto
      (hcont.continuousWithinAt) (fun x _ => hW x) hint.integrableOn hminus
  have hsplit : (∫ x in Iic (0 : ℝ), W' x) + (∫ x in Ioi (0 : ℝ), W' x) = ∫ x, W' x :=
    intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn
  rw [← hsplit, h1, h2]
  ring

/-- The Wronskian of two twice-differentiable functions differentiates to the antisymmetric
second-order pairing. -/
theorem hasDerivAt_wronskian {u v u' v' u'' v'' : ℝ → ℝ} {x : ℝ}
    (hu : HasDerivAt u (u' x) x) (hv : HasDerivAt v (v' x) x)
    (hu' : HasDerivAt u' (u'' x) x) (hv' : HasDerivAt v' (v'' x) x) :
    HasDerivAt (fun y => u' y * v y - u y * v' y) (u'' x * v x - u x * v'' x) x := by
  have h1 := hu'.mul hv
  have h2 := hu.mul hv'
  have h := h1.sub h2
  refine h.congr_deriv ?_
  ring

/-- **Whole-line symmetry of the second-derivative pairing.**  If the Wronskian of `u` and `v`
tends to zero at both ends, the antisymmetric pairing vanishes. -/
theorem integral_secondDeriv_pairing_eq_zero {u v u' v' u'' v'' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (hu' : ∀ x, HasDerivAt u' (u'' x) x) (hv' : ∀ x, HasDerivAt v' (v'' x) x)
    (hint : Integrable fun x => u'' x * v x - u x * v'' x)
    (hplus : Tendsto (fun x => u' x * v x - u x * v' x) atTop (𝓝 0))
    (hminus : Tendsto (fun x => u' x * v x - u x * v' x) atBot (𝓝 0)) :
    ∫ x, (u'' x * v x - u x * v'' x) = 0 :=
  integral_deriv_eq_zero_of_tendsto_zero
    (fun x => hasDerivAt_wronskian (hu x) (hv x) (hu' x) (hv' x)) hint hplus hminus

/-- The symmetry in pairing form, when both halves are separately integrable. -/
theorem integral_secondDeriv_mul_comm {u v u' v' u'' v'' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (hu' : ∀ x, HasDerivAt u' (u'' x) x) (hv' : ∀ x, HasDerivAt v' (v'' x) x)
    (hintL : Integrable fun x => u'' x * v x) (hintR : Integrable fun x => u x * v'' x)
    (hplus : Tendsto (fun x => u' x * v x - u x * v' x) atTop (𝓝 0))
    (hminus : Tendsto (fun x => u' x * v x - u x * v' x) atBot (𝓝 0)) :
    ∫ x, u'' x * v x = ∫ x, u x * v'' x := by
  have h := integral_secondDeriv_pairing_eq_zero hu hv hu' hv' (hintL.sub hintR) hplus hminus
  rw [MeasureTheory.integral_sub hintL hintR] at h
  linarith

/-! ## The first-order companion -/

/-- **Whole-line integration by parts.**  If `u v` tends to zero at both ends, the two pairings of
a derivative are negatives of each other. -/
theorem integral_deriv_mul_eq_neg {u v u' v' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (hintL : Integrable fun x => u' x * v x) (hintR : Integrable fun x => u x * v' x)
    (hplus : Tendsto (fun x => u x * v x) atTop (𝓝 0))
    (hminus : Tendsto (fun x => u x * v x) atBot (𝓝 0)) :
    ∫ x, u' x * v x = -∫ x, u x * v' x := by
  have hW : ∀ x, HasDerivAt (fun y => u y * v y) (u' x * v x + u x * v' x) x :=
    fun x => (hu x).mul (hv x)
  have hzero : ∫ x, (u' x * v x + u x * v' x) = 0 :=
    integral_deriv_eq_zero_of_tendsto_zero hW (hintL.add hintR) hplus hminus
  rw [MeasureTheory.integral_add hintL hintR] at hzero
  linarith

end GaloisForLFunctions.HTGeometry

end
