import GaloisForLFunctions.RHTower.ProlateIndexedCoordinateLimit
import GaloisForLFunctions.RHTower.HermiteMomentClosedForm

/-!
# The constrained-prolate coordinate limit at every Fourier-even rung

Composing the coordinate limit of the canonical indexed prolate family with the closed form of the
Hermite shape ratio identifies the limit with the constrained-prolate Hermite coordinate:

```text
√c · ( ∫_{−1}^{1} R_{2j} )² / ∫_{−1}^{1} R_{2j}²  →  √(2π) · (a_j)² ,
```

where `a_j = constrainedProlateHermiteCoordinate j` is the card's Hermite coordinate, whose square is
`√2 · binom(4j,2j)/16^j`.  The `2j`-th canonical even mode sits at Hermite rung `4j`, which is the
Fourier-eigenvalue `+1` sector the constrained problem uses.
-/

noncomputable section

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- **The coordinate limit in the constrained-prolate normalization.** -/
theorem tendsto_indexedRung_constrainedCoordinate (j : ℕ) :
    Tendsto (fun a : ProlatePositiveAperture => Real.sqrt (indexedOscillatorBandwidth a) *
        ((∫ u in (-1 : ℝ)..1, (signedModeRadialData (a : ℝ) (2 * j)).R u) ^ 2
          / ∫ u in (-1 : ℝ)..1, ((signedModeRadialData (a : ℝ) (2 * j)).R u) ^ 2))
      atTop (𝓝 (Real.sqrt (2 * Real.pi) * constrainedProlateHermiteCoordinate j ^ 2)) := by
  have hbase := tendsto_indexedRung_coordinateLimit (2 * j)
  have hidx : 2 * (2 * j) = 4 * j := by ring
  have hval : (∫ x, hermiteFun (2 * (2 * j)) x) ^ 2 / ∫ x, hermiteFun (2 * (2 * j)) x ^ 2
      = Real.sqrt (2 * Real.pi) * constrainedProlateHermiteCoordinate j ^ 2 := by
    rw [hidx]
    exact hermiteShapeRatio_four_mul_eq_coordinate_sq j
  rwa [hval] at hbase

end GaloisForLFunctions.RHTower

end
