import GaloisForLFunctions.RHTower.Sieve.RouteEMain
import GaloisForLFunctions.RHTower.Sieve.MRFibreDensity
import GaloisForLFunctions.RHTower.Sieve.MRFibreDensityAt
import GaloisForLFunctions.RHTower.Sieve.PairFibreMeanSquare
import GaloisForLFunctions.RHTower.Sieve.FibreStartSeparation
import GaloisForLFunctions.RHTower.Sieve.FibreDevSeparation
import GaloisForLFunctions.RHTower.Sieve.SquarefreeMaximalWindow
import GaloisForLFunctions.RHTower.Sieve.CoprimeMaximalWindow
import GaloisForLFunctions.RHTower.Sieve.MoebiusMaximalWindow

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
    (havg2 : AveragedShortIntervalDensity (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ (2 : ℕ))
      squarefreeDensity hh)
    (hMRp : ∀ p : ℕ, p.Prime → MRBilinearAt (coprimeSquarefreeWeight p)
      (fun x => x / (p : ℝ) ^ (2 : ℕ)) (fun x => hh x / (p : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ (2 : ℕ) / 2 - squarefreeDensity ^ (2 : ℕ) * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (hh x) s / (hh x * Real.sqrt x * Real.log 2) := by
  have hhtop : Tendsto hh atTop atTop := tendsto_of_growth hgrow
  exact route_e_sign_density hs hgrow
    (MRBilinear_moebius_of_averaged havg1 (eventually_pos_normalisation hhtop))
    (MRBilinear_moebius_sq_of_averaged havg2 hhtop) hMRp hε

/-- **Both sign classes are eventually nonempty, from averaged short-interval estimates.** -/
theorem route_e_signClass_nonempty_of_averaged {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (havg1 : AveragedShortInterval (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh)
    (havg2 : AveragedShortIntervalDensity (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ (2 : ℕ))
      squarefreeDensity hh)
    (hMRp : ∀ p : ℕ, p.Prime → MRBilinearAt (coprimeSquarefreeWeight p)
      (fun x => x / (p : ℝ) ^ (2 : ℕ)) (fun x => hh x / (p : ℝ))) :
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
    (havg2 : AveragedShortIntervalDensity (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ (2 : ℕ))
      squarefreeDensity hh)
    (havgp : ∀ p : ℕ, p.Prime → AveragedShortIntervalDensityAt (coprimeSquarefreeWeight p)
      (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1))
      (fun x => x / (p : ℝ) ^ (2 : ℕ)) (fun x => hh x / (p : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ (2 : ℕ) / 2 - squarefreeDensity ^ (2 : ℕ) * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (hh x) s / (hh x * Real.sqrt x * Real.log 2) :=
  route_e_sign_density_of_averaged hs hgrow havg1 havg2
    (fun p hp => MRBilinearAt_coprime_of_averaged hp (tendsto_of_growth hgrow) (havgp p hp)) hε

/-- **Both sign classes are eventually nonempty, from averaged estimates alone.** -/
theorem route_e_signClass_nonempty_of_averaged_all {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (havg1 : AveragedShortInterval (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh)
    (havg2 : AveragedShortIntervalDensity (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ (2 : ℕ))
      squarefreeDensity hh)
    (havgp : ∀ p : ℕ, p.Prime → AveragedShortIntervalDensityAt (coprimeSquarefreeWeight p)
      (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1))
      (fun x => x / (p : ℝ) ^ (2 : ℕ)) (fun x => hh x / (p : ℝ))) :
    ∀ᶠ x in atTop, (coprimeSignClass x (hh x) s).Nonempty :=
  route_e_signClass_nonempty_of_averaged hs hgrow havg1 havg2
    (fun p hp => MRBilinearAt_coprime_of_averaged hp (tendsto_of_growth hgrow) (havgp p hp))

/-- **The card's Theorem `(3)` from mean-square short-interval estimates.**  Cauchy–Schwarz over the
block turns each averaged hypothesis into a mean square over the starting points — the form in which
short-interval estimates for `μ` are proved and stated. -/
theorem route_e_sign_density_of_meanSquare {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (hms1 : AveragedMeanSquare (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh)
    (hms2 : AveragedMeanSquareDensityAt (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ (2 : ℕ))
      squarefreeDensity id hh)
    (hmsp : ∀ p : ℕ, p.Prime → AveragedMeanSquareDensityAt (coprimeSquarefreeWeight p)
      (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1))
      (fun x => x / (p : ℝ) ^ (2 : ℕ)) (fun x => hh x / (p : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ (2 : ℕ) / 2 - squarefreeDensity ^ (2 : ℕ) * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (hh x) s / (hh x * Real.sqrt x * Real.log 2) := by
  have hhtop : Tendsto hh atTop atTop := tendsto_of_growth hgrow
  refine route_e_sign_density_of_averaged_all hs hgrow
    (averagedShortInterval_of_meanSquare hhtop hms1)
    (averagedShortIntervalDensity_of_meanSquare hhtop hms2) ?_ hε
  intro p hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpsq : (0 : ℝ) < (p : ℝ) ^ (2 : ℕ) := by positivity
  exact averagedShortIntervalDensityAt_of_meanSquare (tendsto_id.atTop_div_const hpsq)
    (hhtop.atTop_div_const hp0) (hmsp p hp)

/-- **Both sign classes are eventually nonempty, from mean-square estimates.** -/
theorem route_e_signClass_nonempty_of_meanSquare {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (hms1 : AveragedMeanSquare (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh)
    (hms2 : AveragedMeanSquareDensityAt (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ (2 : ℕ))
      squarefreeDensity id hh)
    (hmsp : ∀ p : ℕ, p.Prime → AveragedMeanSquareDensityAt (coprimeSquarefreeWeight p)
      (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1))
      (fun x => x / (p : ℝ) ^ (2 : ℕ)) (fun x => hh x / (p : ℝ))) :
    ∀ᶠ x in atTop, (coprimeSignClass x (hh x) s).Nonempty := by
  have hhtop : Tendsto hh atTop atTop := tendsto_of_growth hgrow
  refine route_e_signClass_nonempty_of_averaged_all hs hgrow
    (averagedShortInterval_of_meanSquare hhtop hms1)
    (averagedShortIntervalDensity_of_meanSquare hhtop hms2) ?_
  intro p hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpsq : (0 : ℝ) < (p : ℝ) ^ (2 : ℕ) := by positivity
  exact averagedShortIntervalDensityAt_of_meanSquare (tendsto_id.atTop_div_const hpsq)
    (hhtop.atTop_div_const hp0) (hmsp p hp)

/-- **The card's Theorem `(3)` with the Möbius input in its literature form.**  The cancellation
hypothesis for `μ` is now the maximal-window mean square over *all* starting points in
`[√x/2, √x]` at window lengths at most `h` — the statement Matomäki–Radziwiłł's theorem provides. -/
theorem route_e_sign_density_of_maximalWindow {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (hmax : MaximalWindowMeanSquare (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh)
    (hms2 : AveragedMeanSquareDensityAt (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ (2 : ℕ))
      squarefreeDensity id hh)
    (hmsp : ∀ p : ℕ, p.Prime → AveragedMeanSquareDensityAt (coprimeSquarefreeWeight p)
      (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1))
      (fun x => x / (p : ℝ) ^ (2 : ℕ)) (fun x => hh x / (p : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ (2 : ℕ) / 2 - squarefreeDensity ^ (2 : ℕ) * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (hh x) s / (hh x * Real.sqrt x * Real.log 2) :=
  route_e_sign_density_of_meanSquare hs hgrow
    (averagedMeanSquare_of_maximal (tendsto_of_growth hgrow) hmax) hms2 hmsp hε

/-- **The card's Theorem `(3)` with all three inputs in their literature form.**  Every hypothesis
is now a maximal mean square of one arithmetic function over *all* starting points in a dyadic
range, at window lengths at most `h` — the statement short-interval theory proves.  The fibre
geometry has disappeared completely. -/
theorem route_e_sign_density_of_maximalWindow_all {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (hmax1 : MaximalWindowMeanSquare (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh)
    (hmax2 : MaximalWindowDevMeanSquareAt (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ (2 : ℕ))
      squarefreeDensity id hh)
    (hmaxp : ∀ p : ℕ, p.Prime → MaximalWindowDevMeanSquareAt (coprimeSquarefreeWeight p)
      (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1))
      (fun x => x / (p : ℝ) ^ (2 : ℕ)) (fun x => hh x / (p : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ (2 : ℕ) / 2 - squarefreeDensity ^ (2 : ℕ) * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (hh x) s / (hh x * Real.sqrt x * Real.log 2) := by
  have hhtop : Tendsto hh atTop atTop := tendsto_of_growth hgrow
  refine route_e_sign_density_of_meanSquare hs hgrow
    (averagedMeanSquare_of_maximal hhtop hmax1)
    (averagedMeanSquareDensityAt_of_maximal squarefreeDensity_nonneg' tendsto_id hhtop hmax2) ?_ hε
  intro p hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpsq : (0 : ℝ) < (p : ℝ) ^ (2 : ℕ) := by positivity
  exact averagedMeanSquareDensityAt_of_maximal (coprime_block_density_nonneg hp)
    (tendsto_id.atTop_div_const hpsq) (hhtop.atTop_div_const hp0) (hmaxp p hp)

/-- **Both sign classes are eventually nonempty**, from the same three maximal mean squares. -/
theorem route_e_signClass_nonempty_of_maximalWindow_all {hh : ℝ → ℝ} {s : ℤ}
    (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (hmax1 : MaximalWindowMeanSquare (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh)
    (hmax2 : MaximalWindowDevMeanSquareAt (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ (2 : ℕ))
      squarefreeDensity id hh)
    (hmaxp : ∀ p : ℕ, p.Prime → MaximalWindowDevMeanSquareAt (coprimeSquarefreeWeight p)
      (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1))
      (fun x => x / (p : ℝ) ^ (2 : ℕ)) (fun x => hh x / (p : ℝ))) :
    ∀ᶠ x in atTop, (coprimeSignClass x (hh x) s).Nonempty := by
  have hhtop : Tendsto hh atTop atTop := tendsto_of_growth hgrow
  refine route_e_signClass_nonempty_of_meanSquare hs hgrow
    (averagedMeanSquare_of_maximal hhtop hmax1)
    (averagedMeanSquareDensityAt_of_maximal squarefreeDensity_nonneg' tendsto_id hhtop hmax2) ?_
  intro p hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpsq : (0 : ℝ) < (p : ℝ) ^ (2 : ℕ) := by positivity
  exact averagedMeanSquareDensityAt_of_maximal (coprime_block_density_nonneg hp)
    (tendsto_id.atTop_div_const hpsq) (hhtop.atTop_div_const hp0) (hmaxp p hp)

/-- **The card's Theorem `(3)` with the `μ²` input discharged.**  The squarefree equidistribution
hypothesis is a theorem of this corpus, so only the `μ` cancellation and the deleted-squarefree
inputs remain. -/
theorem route_e_sign_density_of_maximalWindow_moebius {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (hsmall : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x)
    (hmax1 : MaximalWindowMeanSquare (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh)
    (hmaxp : ∀ p : ℕ, p.Prime → MaximalWindowDevMeanSquareAt (coprimeSquarefreeWeight p)
      (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1))
      (fun x => x / (p : ℝ) ^ (2 : ℕ)) (fun x => hh x / (p : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ (2 : ℕ) / 2 - squarefreeDensity ^ (2 : ℕ) * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (hh x) s / (hh x * Real.sqrt x * Real.log 2) :=
  route_e_sign_density_of_maximalWindow_all hs hgrow hmax1
    (maximalWindowDevMeanSquare_moebius_sq (tendsto_of_growth hgrow) hsmall) hmaxp hε

/-- **The card's Theorem `(3)` on the Möbius input alone.**  Both squarefree inputs are theorems of
this corpus, so the whole argument now rests on a single short-interval estimate: the mean square of
`μ` over short intervals, which is Matomäki–Radziwiłł's theorem. -/
theorem route_e_sign_density_of_moebius_maximal {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (hsmall : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x)
    (hmax1 : MaximalWindowMeanSquare (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ (2 : ℕ) / 2 - squarefreeDensity ^ (2 : ℕ) * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (hh x) s / (hh x * Real.sqrt x * Real.log 2) := by
  have hhtop : Tendsto hh atTop atTop := tendsto_of_growth hgrow
  refine route_e_sign_density_of_maximalWindow_moebius hs hgrow hsmall hmax1 ?_ hε
  intro p hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpsq : (0 : ℝ) < (p : ℝ) ^ (2 : ℕ) := by positivity
  refine maximalWindowDevMeanSquareAt_coprime hp (tendsto_id.atTop_div_const hpsq)
    (hhtop.atTop_div_const hp0) ?_
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [sqrt_div_sq hx0 hp.pos]
  exact div_le_div_of_nonneg_right hx hp0.le

/-- **The card's Theorem `(3)`, unconditionally, in the long-window regime.**  When the window
length stays within a constant factor of `√x` the Möbius input follows from the prime number
theorem alone, so the whole statement is a theorem of this corpus with no external input. -/
theorem route_e_sign_density_long_window {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1) {K : ℝ}
    (hK : 0 < K)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (hsmall : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x)
    (hlow : ∀ᶠ x in atTop, Real.sqrt x / K ≤ hh x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ (2 : ℕ) / 2 - squarefreeDensity ^ (2 : ℕ) * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (hh x) s / (hh x * Real.sqrt x * Real.log 2) :=
  route_e_sign_density_of_moebius_maximal hs hgrow hsmall
    (maximalWindowMeanSquare_of_firstMoment abs_moebius_real_le_one (tendsto_of_growth hgrow)
      (maximalWindowFirstMoment_moebius_long hK hlow hsmall)) hε

/-- **The card's Theorem `(3)` for every window law that outgrows the Mertens supremum.**  This is
the sharp form of what the argument gives: the admissible window range is governed exactly by the
error term in the prime number theorem, through `mertensSup` at the scale `3√x`. -/
theorem route_e_sign_density_of_mertens_rate {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (hsmall : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x)
    (hrate : Tendsto (fun x => mertensSup ⌈3 * Real.sqrt x⌉₊ / hh x) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ (2 : ℕ) / 2 - squarefreeDensity ^ (2 : ℕ) * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (hh x) s / (hh x * Real.sqrt x * Real.log 2) := by
  have hhtop : Tendsto hh atTop atTop := tendsto_of_growth hgrow
  exact route_e_sign_density_of_moebius_maximal hs hgrow hsmall
    (maximalWindowMeanSquare_of_firstMoment abs_moebius_real_le_one hhtop
      (maximalWindowFirstMoment_moebius_of_rate hsmall (hhtop.eventually_gt_atTop 0) hrate)) hε

end RHTower.Sieve
