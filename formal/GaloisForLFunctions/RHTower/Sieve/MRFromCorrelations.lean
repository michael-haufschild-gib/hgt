import GaloisForLFunctions.RHTower.Sieve.OffDiagonalFromCorrelations
import GaloisForLFunctions.RHTower.Sieve.MRFibreReduction

/-!
# The bilinear all-interval theorem from averaged correlations

The end of the reduction.  For a unit-bounded weight and a window law with `h → ∞` and `h ≤ √x`,

```text
AveragedCorrelationSmall f hh   ⟹   AveragedMeanSquare f hh   ⟹   AveragedShortInterval f hh ,
```

and at `f = μ`, whose block mean vanishes, the last of these is `MRBilinear μ hh`.  So Matomäki–
Radziwiłł's bilinear theorem for `μ` — the sole unproved input of the Route E sign-density
theorems — is implied by the statement that the partial sums of `∑_{n} μ(n)μ(n+k)`, averaged over
`1 ≤ k ≤ h`, are `o(h√x)`: the averaged form of Chowla's conjecture, in the maximal-partial-sum form
that partial summation consumes.
-/

noncomputable section

namespace RHTower.Sieve

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

/-- **The fibre mean square, from averaged correlations.** -/
theorem averagedMeanSquare_of_correlations {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {hh : ℝ → ℝ}
    (hgrow : Tendsto hh atTop atTop) (hcap : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x)
    (hcorr : AveragedCorrelationSmall f hh) :
    AveragedMeanSquare f hh :=
  averagedMeanSquare_of_offDiagonal hf hgrow
    (offDiagonalVanishes_of_correlations hf hgrow hcap hcorr)

/-- The normalisation is eventually positive. -/
theorem eventually_pos_window_normalisation {hh : ℝ → ℝ} (hgrow : Tendsto hh atTop atTop) :
    ∀ᶠ x in atTop, 0 < hh x * Real.sqrt x * Real.log 2 := by
  filter_upwards [hgrow.eventually_gt_atTop 0, Filter.eventually_gt_atTop (0 : ℝ)]
    with x hx1 hx2
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx2
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- **The bilinear all-interval theorem at `μ`, from averaged correlations.** -/
theorem MRBilinear_moebius_of_correlations {hh : ℝ → ℝ} (hgrow : Tendsto hh atTop atTop)
    (hcap : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x)
    (hcorr : AveragedCorrelationSmall (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh) :
    MRBilinear (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh :=
  MRBilinear_moebius_of_averaged
    (averagedShortInterval_of_meanSquare hgrow
      (averagedMeanSquare_of_correlations abs_moebius_real_le_one hgrow hcap hcorr))
    (eventually_pos_window_normalisation hgrow)

end RHTower.Sieve

end
