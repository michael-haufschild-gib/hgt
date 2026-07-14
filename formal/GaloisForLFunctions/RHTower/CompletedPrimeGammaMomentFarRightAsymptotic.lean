import GaloisForLFunctions.Hurwitz.ShiftedPowerTailAsymptotic
import GaloisForLFunctions.RHTower.CompletedPrimeGammaMovingPolynomialParity
import GaloisForLFunctions.RHTower.EulerNormalizedTraceHankelFarRight
import GaloisForLFunctions.RHTower.XiCollapseDirichletLeg
import GaloisForLFunctions.HTGeometry.GammaDifferentialFE
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Unconditional all-order far-right asymptotics of the completed source

The odd completed logarithmic-derivative moments used by the moving polynomial Hankel route have
the exact scalar asymptotic

`x^(2k+1) Re c_k(x) → (-1)^k / (2(2k+1))`.

The proof is source-side and unconditional.  The rational polar leg has one additional inverse
power, the Euler leg is exponentially small after the first-prime normalization, and the exact
Hurwitz/polygamma asymptotic supplies the sole leading term.  Consequently the aggregate
far-right positivity hypothesis in the polynomial parity chain is completely discharged.
-/

open Complex Filter Topology LSeries

namespace RHTower

noncomputable section

/-- Exact positive-order derivative of the completed rational polar leg. -/
theorem iteratedDeriv_completedRationalLeg (j : ℕ) (hj : 0 < j) {x : ℂ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    iteratedDeriv j
        (fun w : ℂ => 1 / w + 1 / (w - 1) - (Real.log Real.pi) / 2) x =
      (-1 : ℂ) ^ j * (j.factorial : ℂ) *
        ((x ^ (j + 1))⁻¹ + (((x - 1) ^ (j + 1))⁻¹)) := by
  have hxsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have hzero : ContDiffAt ℂ j (fun w : ℂ => 1 / w) x :=
    contDiffAt_const.div contDiffAt_id hx0
  have hone : ContDiffAt ℂ j (fun w : ℂ => 1 / (w - 1)) x :=
    contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) hxsub
  change iteratedDeriv j
      (((fun w : ℂ => 1 / w) + (fun w : ℂ => 1 / (w - 1))) -
        (fun _ : ℂ => (Real.log Real.pi : ℂ) / 2)) x = _
  have hsub : iteratedDeriv j
      (((fun w : ℂ => 1 / w) + (fun w : ℂ => 1 / (w - 1))) -
        (fun _ : ℂ => (Real.log Real.pi : ℂ) / 2)) x =
      iteratedDeriv j ((fun w : ℂ => 1 / w) + (fun w : ℂ => 1 / (w - 1))) x -
        iteratedDeriv j (fun _ : ℂ => (Real.log Real.pi : ℂ) / 2) x :=
    iteratedDeriv_sub (hzero.add hone) contDiffAt_const
  rw [hsub, iteratedDeriv_add hzero hone]
  have h0 := GaloisForLFunctions.iteratedDeriv_inv_add_const 0 j x (by simpa using hx0)
  have h1 := GaloisForLFunctions.iteratedDeriv_inv_add_const (-1) j x (by simpa using hxsub)
  rw [show iteratedDeriv j (fun w : ℂ => 1 / w) x =
      (-1 : ℂ) ^ j * (j.factorial : ℂ) * (x ^ (j + 1))⁻¹ by simpa [one_div] using h0]
  rw [show iteratedDeriv j (fun w : ℂ => 1 / (w - 1)) x =
      (-1 : ℂ) ^ j * (j.factorial : ℂ) * ((x - 1) ^ (j + 1))⁻¹ by
        simpa [one_div, sub_eq_add_neg] using h1]
  rw [iteratedDeriv_const]
  simp [hj.ne']
  ring

/-- The completed rational polar leg is one inverse power smaller than the scale retained by the
odd completed moment. -/
theorem tendsto_scaled_completedRationalLeg (j : ℕ) (hj : 0 < j) :
    Tendsto
      (fun x : ℝ => (x : ℂ) ^ j *
        iteratedDeriv j
          (fun w : ℂ => 1 / w + 1 / (w - 1) - (Real.log Real.pi) / 2) (x : ℂ))
      atTop (nhds 0) := by
  have hinv : Tendsto (fun x : ℝ => ((x : ℂ))⁻¹) atTop (nhds 0) := by
    convert Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0)) using 1;
      simp [Function.comp_def]
  have hshift : Tendsto (fun x : ℝ => ((x : ℂ) - 1)⁻¹) atTop (nhds 0) := by
    have hreal : Tendsto (fun x : ℝ => (x - 1)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (-1) tendsto_id)
    convert Complex.continuous_ofReal.continuousAt.tendsto.comp hreal using 1;
      simp [Function.comp_def]
  have hratio : Tendsto (fun x : ℝ => (x : ℂ) / ((x : ℂ) - 1)) atTop (nhds 1) := by
    have h : Tendsto (fun x : ℝ => 1 + ((x : ℂ) - 1)⁻¹) atTop (nhds (1 + 0)) :=
      tendsto_const_nhds.add hshift
    have h' : Tendsto (fun x : ℝ => 1 + ((x : ℂ) - 1)⁻¹) atTop (nhds 1) := by
      simpa using h
    refine h'.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx1 : (x : ℂ) - 1 ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr (ne_of_gt hx)
    field_simp
    ring
  have hratioPow : Tendsto (fun x : ℝ => ((x : ℂ) / ((x : ℂ) - 1)) ^ j)
      atTop (nhds 1) := by simpa using hratio.pow j
  have htail := hinv.add (hratioPow.mul hshift)
  have hscaled := htail.const_mul ((-1 : ℂ) ^ j * (j.factorial : ℂ))
  have hevent :
      (fun x : ℝ => ((-1 : ℂ) ^ j * (j.factorial : ℂ)) *
        ((x : ℂ)⁻¹ + ((x : ℂ) / ((x : ℂ) - 1)) ^ j *
          ((x : ℂ) - 1)⁻¹)) =ᶠ[atTop]
      (fun x : ℝ => (x : ℂ) ^ j *
        iteratedDeriv j
          (fun w : ℂ => 1 / w + 1 / (w - 1) - (Real.log Real.pi) / 2) (x : ℂ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hx))
    have hx1 : (x : ℂ) ≠ 1 := by exact_mod_cast (ne_of_gt hx)
    rw [iteratedDeriv_completedRationalLeg j hj hx0 hx1]
    have hxsub : (x : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hx1
    have hfirst : (x : ℂ) ^ j * (((x : ℂ) ^ (j + 1))⁻¹) = (x : ℂ)⁻¹ := by
      rw [pow_succ]
      field_simp [hx0]
    have hsecond : (x : ℂ) ^ j * ((((x : ℂ) - 1) ^ (j + 1))⁻¹) =
        ((x : ℂ) / ((x : ℂ) - 1)) ^ j * ((x : ℂ) - 1)⁻¹ := by
      rw [div_pow]
      rw [pow_succ]
      field_simp [hxsub]
    symm
    calc
      (x : ℂ) ^ j * (((-1 : ℂ) ^ j * (j.factorial : ℂ)) *
          (((x : ℂ) ^ (j + 1))⁻¹ + (((x : ℂ) - 1) ^ (j + 1))⁻¹)) =
          ((-1 : ℂ) ^ j * (j.factorial : ℂ)) *
            ((x : ℂ) ^ j * (((x : ℂ) ^ (j + 1))⁻¹) +
              (x : ℂ) ^ j * ((((x : ℂ) - 1) ^ (j + 1))⁻¹)) := by ring
      _ = ((-1 : ℂ) ^ j * (j.factorial : ℂ)) *
          ((x : ℂ)⁻¹ + ((x : ℂ) / ((x : ℂ) - 1)) ^ j *
            ((x : ℂ) - 1)⁻¹) := by rw [hfirst, hsecond]
  simpa only [zero_add, one_mul, mul_zero] using hscaled.congr' hevent

/-- Exact leading constant of the completed half-argument Gamma leg. -/
theorem tendsto_scaled_completedGammaLeg (j : ℕ) (hj : 0 < j) :
    Tendsto
      (fun x : ℝ => (x : ℂ) ^ j * (1 / 2 : ℂ) ^ (j + 1) *
        iteratedDeriv j Complex.digamma ((x : ℂ) / 2))
      atTop
      (nhds (((-1 : ℂ) ^ (j + 1) * ((j - 1).factorial : ℂ)) / 2)) := by
  have hbase := (GaloisForLFunctions.tendsto_scaled_polygamma_ofReal j hj).comp
    (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  have hhalf := hbase.const_mul (1 / 2 : ℂ)
  convert hhalf using 1
  · funext x
    simp only [Function.comp_apply, id_eq]
    push_cast
    rw [div_pow]
    ring_nf
    rw [show (2 : ℂ)⁻¹ = 1 / 2 by norm_num]
    ring
  · ring

/-- Every logarithmically weighted von Mangoldt leg is exponentially smaller than the retained
polynomial scale. -/
theorem tendsto_scaled_completedEulerLeg (j : ℕ) :
    Tendsto
      (fun x : ℝ => (x : ℂ) ^ j *
        ((-1 : ℂ) ^ (j + 1) * LSeries (vonMangoldtLogCoeff j) (x : ℂ)))
      atTop (nhds 0) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdecayR : Tendsto (fun x : ℝ => x ^ j / (2 : ℝ) ^ x) atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (j : ℝ) (Real.log 2) hlog
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_natCast]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [div_eq_mul_inv, ← Real.exp_neg]
    congr 2
    ring
  have hdecay : Tendsto (fun x : ℝ => ((x ^ j / (2 : ℝ) ^ x : ℝ) : ℂ))
      atTop (nhds 0) := Complex.continuous_ofReal.continuousAt.tendsto.comp hdecayR
  have hsource := tendsto_vonMangoldtLogCoeff_firstPrime j
  have hproduct := hdecay.mul hsource
  have hzero : (0 : ℂ) * (Real.log 2 : ℂ) ^ (j + 1) = 0 := by ring
  rw [hzero] at hproduct
  have hraw : Tendsto
      (fun x : ℝ => (x : ℂ) ^ j * LSeries (vonMangoldtLogCoeff j) (x : ℂ))
      atTop (nhds 0) := by
    apply hproduct.congr'
    filter_upwards with x
    rw [vonMangoldtLogCoeff]
    have hpow : (2 : ℂ) ^ (x : ℂ) = ((2 : ℝ) ^ x : ℝ) := by
      rw [Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [hpow]
    push_cast
    have hne : (2 : ℝ) ^ x ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
    have hneC : (((2 : ℝ) ^ x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
    field_simp [hneC]
  have hscaled := hraw.const_mul ((-1 : ℂ) ^ (j + 1))
  simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- The odd derivatives of the full completed logarithmic source retain exactly the Gamma leading
term. -/
theorem tendsto_scaled_iteratedDeriv_xiLogDeriv_odd (k : ℕ) :
    Tendsto
      (fun x : ℝ => (x : ℂ) ^ (2 * k + 1) *
        iteratedDeriv (2 * k + 1) xiLogDeriv (x : ℂ))
      atTop
      (nhds (((2 * k).factorial : ℂ) / 2)) := by
  let j := 2 * k + 1
  have hj : 0 < j := by dsimp [j]; omega
  have hrat := tendsto_scaled_completedRationalLeg j hj
  have hgamma := tendsto_scaled_completedGammaLeg j hj
  have heuler := tendsto_scaled_completedEulerLeg j
  have hsum := (hrat.add hgamma).add heuler
  have hsign : (-1 : ℂ) ^ (j + 1) = 1 := by
    rw [show j + 1 = 2 * (k + 1) by dsimp [j]; omega, pow_mul]
    norm_num
  have hlim : (0 : ℂ) +
        ((-1 : ℂ) ^ (j + 1) * ((j - 1).factorial : ℂ) / 2) + 0 =
      ((2 * k).factorial : ℂ) / 2 := by
    rw [hsign]
    dsimp [j]
    simp
  rw [hlim] at hsum
  have hsum' : Tendsto
      (fun x : ℝ => (x : ℂ) ^ j *
        (iteratedDeriv j
            (fun w : ℂ => 1 / w + 1 / (w - 1) - (Real.log Real.pi) / 2) (x : ℂ) +
          (1 / 2 : ℂ) ^ (j + 1) * iteratedDeriv j Complex.digamma ((x : ℂ) / 2) +
          (-1 : ℂ) ^ (j + 1) * LSeries (vonMangoldtLogCoeff j) (x : ℂ)))
      atTop (nhds (((2 * k).factorial : ℂ) / 2)) := by
    convert hsum using 1
    funext x
    ring
  have hxi : Tendsto
      (fun x : ℝ => (x : ℂ) ^ j * iteratedDeriv j xiLogDeriv (x : ℂ))
      atTop (nhds (((2 * k).factorial : ℂ) / 2)) := by
    apply hsum'.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [iteratedDeriv_xiLogDeriv_split j (s := (x : ℂ)) (by simpa using hx)]
    rfl
  simpa only [j] using hxi

/-- Exact complex asymptotic of each normalized odd completed logarithmic-derivative moment. -/
theorem tendsto_scaled_completedOddLogDerivMoment (k : ℕ) :
    Tendsto
      (fun x : ℝ => (x : ℂ) ^ (2 * k + 1) *
        completedOddLogDerivMoment (x : ℂ) k)
      atTop
      (nhds ((((-1 : ℝ) ^ k / (2 * (2 * k + 1)) : ℝ) : ℂ))) := by
  let j := 2 * k + 1
  let C : ℂ := (-1 : ℂ) ^ k / (j.factorial : ℂ)
  have hjet := tendsto_scaled_iteratedDeriv_xiLogDeriv_odd k
  have hscaled := hjet.const_mul C
  have hfac0 : (((2 * k).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * k)
  have hj0 : ((2 * k + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (2 * k)
  have hlim : C * (((2 * k).factorial : ℂ) / 2) =
      ((((-1 : ℝ) ^ k / (2 * (2 * k + 1)) : ℝ) : ℂ)) := by
    dsimp [C, j]
    rw [Nat.factorial_succ]
    push_cast
    field_simp [hfac0, hj0]
  rw [hlim] at hscaled
  apply hscaled.congr'
  filter_upwards with x
  rw [completedOddLogDerivMoment]
  rw [show logDeriv xi = xiLogDeriv by
    funext s
    rw [logDeriv_apply, xiLogDeriv]]
  dsimp [C, j]
  ring

/-- **Unconditional discharge of the scalar far-right hypothesis.** -/
theorem completedOddLogDerivMomentFarRightAsymptotic :
    CompletedOddLogDerivMomentFarRightAsymptotic := by
  intro k
  have hcomplex := tendsto_scaled_completedOddLogDerivMoment k
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  convert hre using 1
  · funext x
    simp only [Function.comp_apply]
    have hrePow : ((x : ℂ) ^ (2 * k + 1)).re = x ^ (2 * k + 1) := by
      calc
        ((x : ℂ) ^ (2 * k + 1)).re = (((x ^ (2 * k + 1) : ℝ) : ℂ)).re :=
          congrArg Complex.re (Complex.ofReal_pow x (2 * k + 1)).symm
        _ = x ^ (2 * k + 1) := Complex.ofReal_re _
    have himPow : ((x : ℂ) ^ (2 * k + 1)).im = 0 := by
      calc
        ((x : ℂ) ^ (2 * k + 1)).im = (((x ^ (2 * k + 1) : ℝ) : ℂ)).im :=
          congrArg Complex.im (Complex.ofReal_pow x (2 * k + 1)).symm
        _ = 0 := Complex.ofReal_im _
    rw [Complex.mul_re, hrePow, himPow]
    ring

/-- **Top-down capstone.**  The completed-source far-right input is unconditional; even real
factorization of every moving polynomial test is the sole remaining hypothesis in this chain. -/
theorem riemannHypothesis_of_completedPolynomial_evenFactorization
    (heven : CompletedOddLogDerivPolynomialRightEvenFactorization) :
    RiemannHypothesis :=
  riemannHypothesis_of_momentAsymptotic_movingPolynomial_evenFactorization
    completedOddLogDerivMomentFarRightAsymptotic heven

end

end RHTower
