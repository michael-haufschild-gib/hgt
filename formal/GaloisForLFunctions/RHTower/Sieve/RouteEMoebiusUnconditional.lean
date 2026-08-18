import GaloisForLFunctions.RHTower.Sieve.MoebiusMeanSquare
import GaloisForLFunctions.RHTower.Sieve.RouteEAveraged

/-!
# Route E, unconditionally

The sign-class density of coprime squarefree pairs, with no hypotheses.  All three short-interval
inputs are theorems: the two squarefree ones from the truncation machinery, and the Möbius one from
the fibre spectral budget.
-/

namespace RHTower.Sieve

open Filter Topology ArithmeticFunction

noncomputable section

/-- The window length outgrows the logarithm. -/
theorem tendsto_cardLength_div_log {β : ℝ} (hβ0 : 0 < β) :
    Tendsto (fun x : ℝ => cardLength β x / Real.log x) atTop atTop := by
  have h := (tendsto_exp_rpow_div_rpow (a := β) (k := 1) (c := 1) hβ0 one_pos).comp Real.tendsto_log_atTop
  refine h.congr fun x => ?_
  simp [Function.comp, cardLength, Real.rpow_one]

/-- The window length outgrows the Mertens scale. -/
theorem tendsto_cardLength_div_logLog {β : ℝ} (hβ0 : 0 < β) :
    Tendsto (fun x : ℝ => cardLength β x / Real.log (Real.log (3 * x))) atTop atTop := by
  have hbase : Tendsto (fun x : ℝ => cardLength β x / (2 * Real.log x)) atTop atTop := by
    have h := (tendsto_cardLength_div_log hβ0).const_mul_atTop (by norm_num : (0:ℝ) < 1 / 2)
    refine h.congr fun x => ?_
    ring
  refine Filter.tendsto_atTop_mono' _ ?_ hbase
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.log 3)] with x hx1 hlogE hlog3
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have h3x : Real.log (3 * x) = Real.log 3 + Real.log x :=
    Real.log_mul (by norm_num) (ne_of_gt hx0)
  have h3pos : (0 : ℝ) < Real.log (3 * x) := by
    have : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    linarith [h3x, this]
  have hll0 : (0 : ℝ) < Real.log (Real.log (3 * x)) := by
    refine Real.log_pos ?_
    have hE : (1 : ℝ) < Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have : Real.log 3 ≤ Real.log x := by linarith [hlog3]
    have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    linarith [h3x, hlogE, hE, h3]
  have hllle : Real.log (Real.log (3 * x)) ≤ 2 * Real.log x := by
    have hstep := Real.log_le_sub_one_of_pos h3pos
    have hl3 : Real.log 3 ≤ Real.log x := hlog3
    linarith [hstep, h3x, hl3]
  have hh0 : (0 : ℝ) ≤ cardLength β x := (cardLength_pos β x).le
  exact div_le_div_of_nonneg_left hh0 hll0 hllle

/-- **Route E's sign density from the averaged Möbius mean square alone.**  Both squarefree inputs
are supplied from the truncation machinery. -/
theorem route_e_sign_density_of_moebius_averaged {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (hsmall : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x)
    (hms1 : AveragedMeanSquare (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) hh)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ 2 / 2 - squarefreeDensity ^ 2 * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (hh x) s / (hh x * Real.sqrt x * Real.log 2) := by
  have hhtop : Tendsto hh atTop atTop := tendsto_of_growth hgrow
  refine route_e_sign_density_of_meanSquare hs hgrow hms1
    (averagedMeanSquareDensityAt_of_maximal squarefreeDensity_nonneg' tendsto_id hhtop
      (maximalWindowDevMeanSquare_moebius_sq hhtop hsmall)) ?_ hε
  intro p hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpsq : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  refine averagedMeanSquareDensityAt_of_maximal (coprime_block_density_nonneg hp)
    (tendsto_id.atTop_div_const hpsq) (hhtop.atTop_div_const hp0) ?_
  refine maximalWindowDevMeanSquareAt_coprime hp (tendsto_id.atTop_div_const hpsq)
    (hhtop.atTop_div_const hp0) ?_
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [sqrt_div_sq hx0 hp.pos]
  exact div_le_div_of_nonneg_right hx hp0.le

/-- **Both sign classes are eventually nonempty, from the averaged Möbius mean square alone.** -/
theorem route_e_signClass_nonempty_of_moebius_averaged {hh : ℝ → ℝ} {s : ℤ}
    (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (hsmall : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x)
    (hms1 : AveragedMeanSquare (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) hh) :
    ∀ᶠ x in atTop, (coprimeSignClass x (hh x) s).Nonempty := by
  have hhtop : Tendsto hh atTop atTop := tendsto_of_growth hgrow
  refine route_e_signClass_nonempty_of_meanSquare hs hgrow hms1
    (averagedMeanSquareDensityAt_of_maximal squarefreeDensity_nonneg' tendsto_id hhtop
      (maximalWindowDevMeanSquare_moebius_sq hhtop hsmall)) ?_
  intro p hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpsq : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  refine averagedMeanSquareDensityAt_of_maximal (coprime_block_density_nonneg hp)
    (tendsto_id.atTop_div_const hpsq) (hhtop.atTop_div_const hp0) ?_
  refine maximalWindowDevMeanSquareAt_coprime hp (tendsto_id.atTop_div_const hpsq)
    (hhtop.atTop_div_const hp0) ?_
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [sqrt_div_sq hx0 hp.pos]
  exact div_le_div_of_nonneg_right hx hp0.le

end

end RHTower.Sieve

namespace RHTower.Sieve

open Filter Topology ArithmeticFunction

noncomputable section

/-- **Route E's sign density, unconditionally.**  At window length `exp((log x)^{99/100})` both
sign classes carry at least `ϱ²/2 − ϱ²·δ` of the coprime squarefree pairs, up to any `ε`.  No
hypotheses: the Möbius input is the fibre spectral budget, the squarefree inputs the truncation
machinery. -/
theorem route_e_sign_density_unconditional {s : ℤ} (hs : s = 1 ∨ s = -1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ 2 / 2 - squarefreeDensity ^ 2 * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (cardLength (99 / 100) x) s
          / (cardLength (99 / 100) x * Real.sqrt x * Real.log 2) :=
  route_e_sign_density_of_moebius_averaged hs
    (tendsto_cardLength_div_logLog (by norm_num))
    (cardLength_le_sqrt (by norm_num) (by norm_num))
    averagedMeanSquare_moebius hε

/-- **Both sign classes are eventually nonempty, unconditionally.** -/
theorem route_e_signClass_nonempty_unconditional {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ∀ᶠ x in atTop, (coprimeSignClass x (cardLength (99 / 100) x) s).Nonempty :=
  route_e_signClass_nonempty_of_moebius_averaged hs
    (tendsto_cardLength_div_logLog (by norm_num))
    (cardLength_le_sqrt (by norm_num) (by norm_num))
    averagedMeanSquare_moebius

end

end RHTower.Sieve
