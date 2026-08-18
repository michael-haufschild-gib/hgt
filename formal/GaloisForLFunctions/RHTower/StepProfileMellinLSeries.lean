import GaloisForLFunctions.RHTower.AbelTailLSeries
import GaloisForLFunctions.HTGeometry.StepProfileMellinTransform

/-!
# The Mellin transform of a summatory profile is its `L`-series

Combining the integral form of Abel summation with the increment-series form gives, for a real
source `b` whose partial sums are `O(N^θ)` and `Re s > max(0, θ)` inside the domain of
convergence,

```text
s ∫_1^∞ ( ∑_{m ≤ x} b m ) x^{-s-1} dx  =  ∑_{n ≥ 1} b n n^{-s} .
```
-/

noncomputable section

open MeasureTheory Set Complex

namespace RHTower

/-- **Mellin form of Abel summation.**  The Mellin transform of the summatory step profile is
`1/s` times the `L`-series of the source. -/
theorem mellin_sourcePartialSum_eq_LSeries {b : ℕ → ℝ} {C θ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ N : ℕ, |sourcePartialSum b N| ≤ C * (N : ℝ) ^ θ) {s : ℂ} (hs : 0 < s.re)
    (hθs : θ < s.re) (hsum : LSeriesSummable (fun n => (b n : ℂ)) s) :
    s * (∫ x in Set.Ioi (1:ℝ), (sourcePartialSum b ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1))
      = LSeries (fun n => (b n : ℂ)) s := by
  rw [GaloisForLFunctions.HTGeometry.mellin_stepProfile_eq_tsum hC hb hs hθs]
  rw [← abelTailSeries_sourcePartialSum hC hb hs hθs hsum, abelTailSeries]

end RHTower

end
