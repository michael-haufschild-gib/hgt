import GaloisForLFunctions.RHTower.BesselEndpointVariation
import GaloisForLFunctions.RHTower.XiAmplitudeEndpointSymbol
import GaloisForLFunctions.RHTower.CCMFirstRowDunsterModel
import GaloisForLFunctions.RHTower.ExteriorDunsterPrimitive

/-!
# The total variation of the leading first-row factor

The leading factor of a first-row Gram entry is Dunster's pole-uniform amplitude times the Bessel
comparison model,

```text
U(x) = A_s(x) · J₀(c ξ_s(x)) ,
```

and its derivative is exactly the shape `A′·J₀(cξ) + A·(J₀′(cξ)·cξ′)` that the endpoint-variation
estimate consumes.  Feeding the two amplitude bounds `|A| ≤ 2`, `|A′| ≤ 6` — valid on the *whole*
exterior ray, not only beyond the second dilation — gives the card's `(7)` for the leading factor
with explicit constants:

```text
∫_a^b |U′| ≤ 6 (b − a) + (2 c²/π) (ξ_s(b)² − ξ_s(a)²) .
```

Near the turning point the second term is `O(c²ξ²)`, which is bounded exactly on the endpoint layer
`c ξ_s(x) = O(1)`; beyond it, `ξ_s(x)² ≤ x²` supplies the exterior growth.  No lower bound on `ξ′`
and no cancellation is used.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The leading first-row factor: Dunster's amplitude times the Bessel model. -/
def firstRowModel (s c x : ℝ) : ℝ := xiAmplitude s x * lgBesselModel s c x

/-- Its derivative. -/
def firstRowModelDeriv (s c x : ℝ) : ℝ :=
  xiAmplitudeDeriv s x * lgBesselModel s c x + xiAmplitude s x * lgBesselModelDeriv s c x

theorem hasDerivAt_firstRowModel {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    HasDerivAt (firstRowModel s c) (firstRowModelDeriv s c x) x :=
  (hasDerivAt_xiAmplitude hs0 hs1 hx).mul (hasDerivAt_lgBesselModel hs0 hx)

/-- **The total variation of the leading first-row factor.**  This is `(7)` of the high radial
first-row card for the leading term, with every constant explicit. -/
theorem integral_abs_firstRowModelDeriv_le {s c a b : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 ≤ c) (ha : 1 < a) (hab : a ≤ b) :
    (∫ x in a..b, |firstRowModelDeriv s c x|)
      ≤ 6 * (b - a)
        + 2 * c ^ 2 * (xiEndpointPhase s b ^ 2 - xiEndpointPhase s a ^ 2) / Real.pi := by
  have hsub : Icc a b ⊆ Ioi (1 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  have hlt : ∀ x ∈ Icc a b, (1 : ℝ) < x := fun x hx => lt_of_lt_of_le ha hx.1
  have hmain := integral_abs_deriv_besselModulated_le (a := a) (b := b) (c := c)
    (Q := 2) (Q' := 6) (A := xiAmplitude s) (A' := xiAmplitudeDeriv s)
    (Θ := xiEndpointPhase s) (Θ' := xiSpeed s) hab hc (by norm_num)
    (fun x hx => hasDerivAt_xiEndpointPhase hs0 (hlt x hx))
    ((continuousOn_xiAmplitude hs0 hs1).mono hsub)
    ((continuousOn_xiAmplitudeDeriv hs0 hs1).mono hsub)
    ((continuousOn_xiEndpointPhase hs0).mono hsub)
    (fun x hx => ((continuousAt_xiSpeed (s := s) (hlt x hx)).continuousWithinAt))
    (fun x hx => abs_xiAmplitude_le_two hs0 hs1 (hlt x hx))
    (fun x hx => abs_xiAmplitudeDeriv_le_six hs0 hs1 (hlt x hx))
    (fun x hx => xiEndpointPhase_nonneg hs0 (by linarith) (hlt x hx).le)
    (fun x hx => (xiSpeed_pos hs1 (hlt x hx)).le)
  refine le_trans (le_of_eq ?_) (hmain.trans (le_of_eq ?_))
  · refine intervalIntegral.integral_congr fun x _ => ?_
    rw [firstRowModelDeriv, lgBesselModel, lgBesselModelDeriv]
  · ring

end GaloisForLFunctions.RHTower

end
