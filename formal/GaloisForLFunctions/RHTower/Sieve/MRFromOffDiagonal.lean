import GaloisForLFunctions.RHTower.Sieve.FrequencyFromOffDiagonal
import GaloisForLFunctions.RHTower.Sieve.MRFromCorrelations

/-!
# The bilinear all-interval theorem from one off-diagonal bound

The direct route, end to end, in one statement:

```text
OffDiagonalSmall μ hh   ⟹   MRBilinear μ hh ,
```

for every window law with `hh → ∞` and `hh x ≤ √x`.  Unwinding the definition, the hypothesis is

> for every `ε > 0` and all large `x`, the Dirichlet polynomial `∑_{n ≤ M} μ(n)·n^{2πiw}` of length
> `M = ⌈√x + hh x⌉` satisfies `∫_{|w| ≤ T} ‖·‖² ≤ α·T + β` for every height `T > 0`, with `α ≤ 50√x`
> — the diagonal at its baseline — and `β ≤ ε·x = ε·M²`.

The diagonal costs nothing; the whole content is that the **off-diagonal beats `M²`**.  The mean
value theorem gives exactly `β ≍ M²` (`integral_Icc_normSq_logPoly_le_affine_majorant`), so any
saving at all closes the route, and with it both Route E sign-density theorems.
-/

noncomputable section

namespace RHTower.Sieve

open Filter Topology
open scoped ArithmeticFunction.Moebius

/-- **The bilinear all-interval theorem at `μ`, from one off-diagonal bound.** -/
theorem MRBilinear_moebius_of_offDiagonal {hh : ℝ → ℝ} (hgrow : Tendsto hh atTop atTop)
    (hcap : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x)
    (hoff : OffDiagonalSmall (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh) :
    MRBilinear (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh :=
  MRBilinear_moebius_of_averaged
    (averagedShortInterval_of_meanSquare hgrow
      (averagedMeanSquare_of_frequency abs_moebius_real_le_one hgrow hcap
        (frequencyMeanSquareSmall_of_offDiagonal hgrow hcap hoff)))
    (eventually_pos_window_normalisation hgrow)

end RHTower.Sieve

end
