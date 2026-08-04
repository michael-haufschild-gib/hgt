import GaloisForLFunctions.RHTower.Sieve.RouteEMain
import GaloisForLFunctions.RHTower.Sieve.MRFibreDensity
import GaloisForLFunctions.RHTower.Sieve.MRFibreDensityAt

/-!
# The sign law from averaged short-interval estimates

`route_e_sign_density` takes the bilinear all-interval theorem at `μ` and at `μ²` as hypotheses.
The fibre decomposition replaces both by averaged short-interval estimates — one cancellation
statement and one equidistribution statement — over the `√x` starting points `x/a` with `a` in the
dyadic block:

    ∑_{a ∈ block} |∑_{b ∈ fibre(a)} μ(b)|                  = o(h√x),
    ∑_{a ∈ block} |∑_{b ∈ fibre(a)} μ²(b) − D·h√x/a|       = o(h√x).

Nothing is assumed about the constant `D²` appearing in the conclusion: it is produced by the
logarithmic block mean `∑_{√x < a ≤ 2√x} μ²(a)/a → D log 2`, which is proved here from Abel
summation against the squarefree count.
-/

namespace RHTower.Sieve

open Filter Topology
open scoped ArithmeticFunction.Moebius

/-- The normalising factor is eventually positive. -/
theorem eventually_pos_normalisation {hh : ℝ → ℝ} (hgrow : Tendsto hh atTop atTop) :
    ∀ᶠ x in atTop, 0 < hh x * Real.sqrt x * Real.log 2 := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), hgrow.eventually_gt_atTop 0] with x hx hhx
  have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- **The card's Theorem `(3)`, from averaged short-interval estimates.** -/
theorem route_e_sign_density_of_averaged {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (havg1 : AveragedShortInterval (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh)
    (havg2 : AveragedShortIntervalDensity (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ 2)
      squarefreeDensity hh)
    (hMRp : ∀ p : ℕ, p.Prime → MRBilinearAt (coprimeSquarefreeWeight p)
      (fun x => x / (p : ℝ) ^ 2) (fun x => hh x / (p : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ 2 / 2 - squarefreeDensity ^ 2 * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (hh x) s / (hh x * Real.sqrt x * Real.log 2) := by
  have hhtop : Tendsto hh atTop atTop := tendsto_of_growth hgrow
  exact route_e_sign_density hs hgrow
    (MRBilinear_moebius_of_averaged havg1 (eventually_pos_normalisation hhtop))
    (MRBilinear_moebius_sq_of_averaged havg2 hhtop) hMRp hε

/-- **Both sign classes are eventually nonempty, from averaged short-interval estimates.** -/
theorem route_e_signClass_nonempty_of_averaged {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (havg1 : AveragedShortInterval (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh)
    (havg2 : AveragedShortIntervalDensity (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ 2)
      squarefreeDensity hh)
    (hMRp : ∀ p : ℕ, p.Prime → MRBilinearAt (coprimeSquarefreeWeight p)
      (fun x => x / (p : ℝ) ^ 2) (fun x => hh x / (p : ℝ))) :
    ∀ᶠ x in atTop, (coprimeSignClass x (hh x) s).Nonempty := by
  have hhtop : Tendsto hh atTop atTop := tendsto_of_growth hgrow
  exact route_e_signClass_nonempty hs hgrow
    (MRBilinear_moebius_of_averaged havg1 (eventually_pos_normalisation hhtop))
    (MRBilinear_moebius_sq_of_averaged havg2 hhtop) hMRp

/-- **The card's Theorem `(3)` from averaged short-interval estimates alone.**  All three inputs of
the argument are now single averaged estimates over the block of starting points: one cancellation
statement for `μ`, one equidistribution statement for `μ²`, and one for `μ²·1_{p∤·}` at each
rescaled pair of parameters. -/
theorem route_e_sign_density_of_averaged_all {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (havg1 : AveragedShortInterval (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh)
    (havg2 : AveragedShortIntervalDensity (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ 2)
      squarefreeDensity hh)
    (havgp : ∀ p : ℕ, p.Prime → AveragedShortIntervalDensityAt (coprimeSquarefreeWeight p)
      (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1))
      (fun x => x / (p : ℝ) ^ 2) (fun x => hh x / (p : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ 2 / 2 - squarefreeDensity ^ 2 * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (hh x) s / (hh x * Real.sqrt x * Real.log 2) :=
  route_e_sign_density_of_averaged hs hgrow havg1 havg2
    (fun p hp => MRBilinearAt_coprime_of_averaged hp (tendsto_of_growth hgrow) (havgp p hp)) hε

/-- **Both sign classes are eventually nonempty, from averaged estimates alone.** -/
theorem route_e_signClass_nonempty_of_averaged_all {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (havg1 : AveragedShortInterval (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh)
    (havg2 : AveragedShortIntervalDensity (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ 2)
      squarefreeDensity hh)
    (havgp : ∀ p : ℕ, p.Prime → AveragedShortIntervalDensityAt (coprimeSquarefreeWeight p)
      (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1))
      (fun x => x / (p : ℝ) ^ 2) (fun x => hh x / (p : ℝ))) :
    ∀ᶠ x in atTop, (coprimeSignClass x (hh x) s).Nonempty :=
  route_e_signClass_nonempty_of_averaged hs hgrow havg1 havg2
    (fun p hp => MRBilinearAt_coprime_of_averaged hp (tendsto_of_growth hgrow) (havgp p hp))

end RHTower.Sieve
