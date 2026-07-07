/-
Carlson's sublinear density from the large-values mechanism.

The built large-values inequality (`LargeValuesDpoly.large_values_dpoly`) bounds the number of grid
points where a Dirichlet polynomial is large by its second moment: `R·V² ≤ (moments)`.  Through the
mollifier (`Mollifier`), the ζ-zeros right of the critical line up to height `T` are `N(σ,T)` such
large values of the detection polynomial `1 − ζ·M`, whose second moment the Möbius cancellation makes
small.  This file closes the abstract endpoint: **a large-values bound with a sublinear right-hand
side forces a sublinear count**, and hence `RH₂` through the density engine.

`sublinearDensity_of_largeValues`: if `N(T)·V² ≤ Φ(T)` with `Φ` sublinear (`Φ(T)/T → 0`), then `N` is
sublinear (`ZeroDensityEngine.SubLinearDensity`).  This is the exact shape the large-values inequality
produces (`N·V² ≤ moments`) once the mollifier makes the moments `o(T·V²)` — Carlson's optimization.
Composed with the recurrence contradiction it gives `RH₂` (`rhLadder_one_of_recurrence_of_largeValues`).

The one remaining classical input is the *detection bound* — that the mollified moments are `o(T·V²)`
for a fixed threshold `V > 0` — which packages the Dirichlet convolution `ζ·M`, the built AFE, and the
mollifier-length optimization.  Everything downstream of it is now machine-checked.
-/
import GaloisForLFunctions.RHTower.ZeroDensityEngine
import GaloisForLFunctions.RHTower.LargeValuesDpoly
import GaloisForLFunctions.RHTower.Mollifier

namespace RHTower

/-- **Sublinear count from a sublinear large-values bound.**  Fix a threshold `V > 0`.  If a
nonnegative count `N` obeys `N(T)·V² ≤ Φ(T)` for all `T`, and `Φ` is sublinear
(`Φ(T) ≤ ε·V²·T` eventually, for every `ε > 0`), then `N` is sublinear.  This is the density shape the
large-values inequality yields: the count of large values divided by `V²` is at most the (mollified,
hence sublinear) second moment. -/
theorem sublinearDensity_of_largeValues {N Φ : ℝ → ℝ} {V : ℝ} (hV : 0 < V)
    (hbound : ∀ T, N T * V ^ 2 ≤ Φ T)
    (hsub : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, Φ T ≤ ε * V ^ 2 * T) :
    SubLinearDensity N := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := hsub ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 : N T * V ^ 2 ≤ ε * V ^ 2 * T := le_trans (hbound T) (hT₀ T hT)
  have hV2 : 0 < V ^ 2 := by positivity
  nlinarith [h1, hV2]

/-- **`RH₂` from recurrence and the large-values density.**  Combine the sublinear density produced by
the large-values mechanism with the defect-recurrence contradiction: if a right-half odd ξ-zero forces
a positive linear lower bound on the zero count `N`, while the mollified large-values bound makes `N`
sublinear, the two are incompatible — so every right-half ξ-zero has even multiplicity (`RHLadder 1`).
The sublinear input is exactly `sublinearDensity_of_largeValues` fed the mollified moments. -/
theorem rhLadder_one_of_recurrence_of_largeValues {N Φ : ℝ → ℝ} {c V : ℝ}
    (hc : 0 < c) (hV : 0 < V)
    (hrec : (∃ ρ, XiDefect ρ) → LinearLowerBound N c)
    (hbound : ∀ T, N T * V ^ 2 ≤ Φ T)
    (hsub : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, Φ T ≤ ε * V ^ 2 * T) :
    RHLadder 1 :=
  rhLadder_one_of_recurrence_of_density hc hrec
    (sublinearDensity_of_largeValues hV hbound hsub)

end RHTower
