import GaloisForLFunctions.RHTower.XiPoleClearedFirstTraceRootReduction
import GaloisForLFunctions.HTGeometry.CaratheodoryNevanlinnaPick
import Mathlib.Analysis.Analytic.Binomial

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Shifted Cayley coordinate mapping `Re s > 1` to the unit disk. -/
def poleFactorCayley (s : ℂ) : ℂ := cayleyRight (s - 1)

theorem norm_poleFactorCayley_lt_one {s : ℂ} (hs : 1 < s.re) :
    ‖poleFactorCayley s‖ < 1 := by
  apply norm_cayleyRight_lt_one
  simp only [Complex.sub_re, Complex.one_re]
  linarith

theorem analyticOnNhd_poleFactorCayley_rightHalf :
    AnalyticOnNhd ℂ poleFactorCayley rightHalf := by
  intro s hs
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num [rightHalf] at hs
  change AnalyticAt ℂ (fun z : ℂ => ((z - 1) - 1) / ((z - 1) + 1)) s
  apply AnalyticAt.div
  · fun_prop
  · fun_prop
  · simpa using hs0

private theorem analytic_binomialPartialSum (a : ℂ) (n : ℕ) :
    AnalyticOnNhd ℂ (fun z => (binomialSeries ℂ a).partialSum n z) Set.univ := by
  let p := binomialSeries ℂ a
  have hpoly : (fun z => p.partialSum n z) =
      fun z => ∑ k ∈ Finset.range n, p.coeff k * z ^ k := by
    funext z
    rw [FormalMultilinearSeries.partialSum]
    exact Finset.sum_congr rfl (fun k _ => by
      rw [p.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm])
  have hdiff : Differentiable ℂ (fun z => p.partialSum n z) := by
    rw [hpoly]
    fun_prop
  exact hdiff.differentiableOn.analyticOnNhd isOpen_univ

/-- Rational Cayley-binomial approximant to the principal square root of `s - 1`. -/
def poleFactorSqrtApprox (n : ℕ) (s : ℂ) : ℂ :=
  (binomialSeries ℂ (1 / 2 : ℂ)).partialSum n (poleFactorCayley s) *
    (binomialSeries ℂ (-1 / 2 : ℂ)).partialSum n (-poleFactorCayley s)

/-- Limit represented by the two convergent binomial factors. -/
def poleFactorSqrtCayleyLimit (s : ℂ) : ℂ :=
  (1 + poleFactorCayley s) ^ (1 / 2 : ℂ) *
    (1 - poleFactorCayley s) ^ (-1 / 2 : ℂ)

theorem analyticOnNhd_poleFactorSqrtApprox_rightHalf (n : ℕ) :
    AnalyticOnNhd ℂ (poleFactorSqrtApprox n) rightHalf := by
  intro s hs
  have hc := analyticOnNhd_poleFactorCayley_rightHalf s hs
  have hp := (analytic_binomialPartialSum (1 / 2 : ℂ) n)
    (poleFactorCayley s) (Set.mem_univ _)
  have hm := (analytic_binomialPartialSum (-1 / 2 : ℂ) n)
    (-poleFactorCayley s) (Set.mem_univ _)
  have hcneg : AnalyticAt ℂ (fun z => -poleFactorCayley z) s := hc.neg
  exact (hp.comp hc).mul (AnalyticAt.comp
    (g := fun z => (binomialSeries ℂ (-1 / 2 : ℂ)).partialSum n z)
    (f := fun z => -poleFactorCayley z) (x := s) hm hcneg)

theorem tendstoLocallyUniformlyOn_poleFactorSqrtApprox :
    TendstoLocallyUniformlyOn poleFactorSqrtApprox poleFactorSqrtCayleyLimit atTop farHalf := by
  have hmapPlus : MapsTo poleFactorCayley farHalf (Metric.eball (0 : ℂ) 1) := by
    intro s hs
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa [Metric.mem_ball, dist_zero_right] using
      norm_poleFactorCayley_lt_one (mem_farHalf.mp hs)
  have hmapMinus : MapsTo (fun s => -poleFactorCayley s) farHalf
      (Metric.eball (0 : ℂ) 1) := by
    intro s hs
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa [Metric.mem_ball, dist_zero_right] using
      norm_poleFactorCayley_lt_one (mem_farHalf.mp hs)
  have hcontPlus : ContinuousOn poleFactorCayley farHalf :=
    analyticOnNhd_poleFactorCayley_rightHalf.continuousOn.mono farHalf_subset_rightHalf
  have hcontMinus : ContinuousOn (fun s => -poleFactorCayley s) farHalf :=
    hcontPlus.neg
  have hplus0 :=
    (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := (1 / 2 : ℂ))).tendstoLocallyUniformlyOn
  have hminus0 :=
    (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := (-1 / 2 : ℂ))).tendstoLocallyUniformlyOn
  have hplus := hplus0.comp poleFactorCayley hmapPlus hcontPlus
  have hminus := hminus0.comp (fun s => -poleFactorCayley s) hmapMinus hcontMinus
  have hplusCont :=
    (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero
      (a := (1 / 2 : ℂ))).continuousOn.comp hcontPlus hmapPlus
  have hminusCont :=
    (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero
      (a := (-1 / 2 : ℂ))).continuousOn.comp hcontMinus hmapMinus
  have hplusCont' : ContinuousOn
      ((fun y : ℂ => (1 + (0 + y)) ^ (1 / 2 : ℂ)) ∘ poleFactorCayley) farHalf := by
    simpa [Function.comp_def] using hplusCont
  have hminusCont' : ContinuousOn
      ((fun y : ℂ => (1 + (0 + y)) ^ (-1 / 2 : ℂ)) ∘
        (fun s => -poleFactorCayley s)) farHalf := by
    simpa [Function.comp_def] using hminusCont
  have hprod := hplus.mul₀ hminus hplusCont' hminusCont'
  convert hprod using 1
  · ext n s
    simp [poleFactorSqrtApprox, Function.comp_def]
  · ext s
    simp [poleFactorSqrtCayleyLimit, Function.comp_def, sub_eq_add_neg]

theorem poleFactorSqrtCayleyLimit_sq {s : ℂ} (hs : 1 < s.re) :
    poleFactorSqrtCayleyLimit s ^ 2 = s - 1 := by
  let w := poleFactorCayley s
  have hw : ‖w‖ < 1 := norm_poleFactorCayley_lt_one hs
  have hplus : ((1 + w) ^ (1 / 2 : ℂ)) ^ 2 = 1 + w := by
    rw [← Complex.cpow_nat_mul]
    norm_num
  have hminus : ((1 - w) ^ (-1 / 2 : ℂ)) ^ 2 = (1 - w)⁻¹ := by
    rw [← Complex.cpow_nat_mul]
    norm_num
    rw [Complex.cpow_neg_one]
  rw [poleFactorSqrtCayleyLimit, mul_pow, hplus, hminus]
  change (1 + w) * (1 - w)⁻¹ = s - 1
  rw [← div_eq_mul_inv]
  dsimp [w, poleFactorCayley]
  rw [cayleyRight_inv]
  simp only [Complex.sub_re, Complex.one_re]
  linarith

end

end RHTower
