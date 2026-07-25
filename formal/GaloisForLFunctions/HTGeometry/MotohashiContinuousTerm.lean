/-
The Plancherel density gap, and why the sixth moment inside Motohashi's identity is unreachable.

Motohashi's explicit formula for the error term in the fourth moment of `ζ` weights the spectrum by
`T^{1/2} r^{-3/2}`.  On the cuspidal spectrum the counting measure has density `≍ r dr`; on the
Eisenstein spectrum the Plancherel measure has density `≍ dr`.  The continuous term is therefore
suppressed by a full factor of `r` relative to the cuspidal one.

Consequences, all pure exponent arithmetic:

* the cuspidal sum has weight-plus-density exponent `-1/2 > -1`, so it is dominated by the **top** of
  the spectral range — which is why the cubic moment of cusp forms is what the identity sees;
* the continuous integral has exponent `-3/2 < -1`, so it converges and is dominated by the
  **bottom**, `r = O(1)`.  The sixth moment of `ζ` at large height never enters;
* even granting positivity of the spectral weight, the bound obtainable for the sixth moment at
  height `R` from the fourth moment at height `T = R²` is `R^{3/2}` at best — worse than the known
  `R^{5/4}`.
-/
import GaloisForLFunctions.HTGeometry.MomentChordPivot

namespace HTGeometry

/-- Exponent of the spectral weight in Motohashi's explicit formula: `T^{1/2} r^{-3/2}`. -/
def motohashiWeightExponent : ℚ := -3/2

/-- Density exponent of the cuspidal spectrum of `GL(2)`: the Weyl law gives `≍ r dr`. -/
def cuspidalDensityExponent : ℚ := 1

/-- Density exponent of the Eisenstein spectrum of `GL(2)`: the Plancherel measure is `≍ dr`. -/
def eisensteinDensityExponent : ℚ := 0

/-- **The Plancherel density gap.**  The continuous spectrum carries one power of `r` less than the
cuspidal spectrum; this single exponent is the whole obstruction. -/
theorem plancherel_density_gap :
    cuspidalDensityExponent - eisensteinDensityExponent = 1 := by
  unfold cuspidalDensityExponent eisensteinDensityExponent; norm_num

/-- The cuspidal sum is top-dominated: its integrand exponent exceeds `-1`. -/
theorem cuspidal_top_dominated :
    -1 < motohashiWeightExponent + cuspidalDensityExponent := by
  unfold motohashiWeightExponent cuspidalDensityExponent; norm_num

/-- The continuous integral is bottom-dominated: its integrand exponent is below `-1`, so it
converges and is governed by `r = O(1)`.  The sixth moment at large height is invisible to it. -/
theorem eisenstein_bottom_dominated :
    motohashiWeightExponent + eisensteinDensityExponent < -1 := by
  unfold motohashiWeightExponent eisensteinDensityExponent; norm_num

/-- Output exponent of the positivity route: from `E₂(T) ≪ T^{e}` and the weight `T^{1/2}R^{-3/2}`,
with the spectral range capped at `R ≤ T^{1/2}` so that `T = R²`, the sixth moment at height `R` is
bounded by `R^{2e - 1 + 3/2}`. -/
def positivityRouteOutput (e : ℚ) : ℚ := 2 * e - 1 + 3/2

/-- With the known bound `E₂(T) ≪ T^{2/3}` the route gives `11/6`. -/
theorem positivityRouteOutput_known : positivityRouteOutput (2/3) = 11/6 := by
  unfold positivityRouteOutput; norm_num

/-- With the conjectured, `Ω`-matching bound `E₂(T) ≪ T^{1/2+ε}` — which cannot be improved, since
`E₂(T) = Ω_±(T^{1/2})` — the route gives `3/2`. -/
theorem positivityRouteOutput_optimal : positivityRouteOutput (1/2) = 3/2 := by
  unfold positivityRouteOutput; norm_num

/-- **The ceiling.**  Even at the `Ω`-imposed floor for `E₂`, the positivity route returns `3/2`,
strictly worse than the known moment envelope value `5/4 = momentChord 6`.  So the route is void:
it cannot be made to work, and would be worthless if it could. -/
theorem positivity_route_void :
    momentChord (2 * 3) < positivityRouteOutput (1/2) ∧
    momentChord (2 * 3) < positivityRouteOutput (2/3) := by
  constructor
  · rw [positivityRouteOutput_optimal]; unfold momentChord; norm_num
  · rw [positivityRouteOutput_known]; unfold momentChord; norm_num

/-- The route improves on the envelope only for `E₂(T) ≪ T^{e}` with `e < 3/8`, below the `Ω`-result
`E₂(T) = Ω_±(T^{1/2})`.  So the obstruction is an `Ω`-result, not a lack of effort. -/
theorem positivity_route_threshold {e : ℚ} :
    positivityRouteOutput e < 5/4 ↔ e < 3/8 := by
  unfold positivityRouteOutput
  constructor <;> intro h <;> linarith

end HTGeometry
