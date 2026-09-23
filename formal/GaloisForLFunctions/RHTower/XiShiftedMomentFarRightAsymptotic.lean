import GaloisForLFunctions.RHTower.XiLogDerivPositiveRayAsymptotic
import GaloisForLFunctions.HTGeometry.MixedEvenTrigMoments
import GaloisForLFunctions.HTGeometry.CentralBinomialRoot

/-!
# Full shifted-Xi moment recession to the arcsine sequence

The completed reverse-Bessel source has one logarithmic leading term.  Every positive-order jet
has a finite polynomially normalized limit, hence vanishes after the extra logarithmic division.
The exact source-to-moment identity then yields the central-binomial moment sequence.
-/

open Complex Filter Topology LSeries
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem tendsto_add_half :
    Tendsto (fun w : ℝ => 1 / 2 + w) atTop atTop := by
  simpa [add_comm] using
    (tendsto_atTop_add_const_right atTop (1 / 2 : ℝ) tendsto_id)

private theorem tendsto_log_add_half_div_log :
    Tendsto (fun w : ℝ => Real.log (1 / 2 + w) / Real.log w) atTop (nhds 1) := by
  have hinv : Tendsto (fun w : ℝ => w⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hratio : Tendsto (fun w : ℝ => (1 / 2 + w) / w) atTop (nhds 1) := by
    have h := (hinv.const_mul (1 / 2 : ℝ)).add_const 1
    have h' : Tendsto (fun w : ℝ => (1 / 2) * w⁻¹ + 1) atTop (nhds 1) := by
      simpa using h
    apply h'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
    field_simp [hw.ne']
  have hlogRatio : Tendsto (fun w : ℝ => Real.log ((1 / 2 + w) / w))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have hdiff : Tendsto
      (fun w : ℝ => Real.log (1 / 2 + w) - Real.log w)
      atTop (nhds 0) := by
    apply hlogRatio.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
    rw [Real.log_div (by linarith) hw.ne']
  have hlog : Tendsto (fun w : ℝ => Real.log w) atTop atTop := Real.tendsto_log_atTop
  have hsmall := hdiff.div_atTop hlog
  have hmain := hsmall.add (tendsto_const_nhds :
    Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1))
  rw [zero_add] at hmain
  apply hmain.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  have hlogne : Real.log w ≠ 0 := ne_of_gt (Real.log_pos hw)
  field_simp [hlogne]
  ring

private theorem tendsto_xiRayLogDeriv_shift_div_log :
    Tendsto
      (fun w : ℝ => xiRayLogDeriv (1 / 2 + w) / Real.log w)
      atTop (nhds (1 / 2 : ℝ)) := by
  have hbase := tendsto_xiRayLogDeriv_div_log.comp tendsto_add_half
  have hmul := hbase.mul tendsto_log_add_half_div_log
  have hlim : (1 / 2 : ℝ) * 1 = 1 / 2 := by ring
  rw [hlim] at hmul
  apply hmul.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  have hw' : 1 < 1 / 2 + w := by linarith
  have hlogw : Real.log w ≠ 0 := ne_of_gt (Real.log_pos hw)
  have hlogs : Real.log (1 / 2 + w) ≠ 0 := ne_of_gt (Real.log_pos hw')
  simp only [Function.comp_apply]
  field_simp [hlogw, hlogs]
  rw [show (1 + 2 * w) / 2 = 1 / 2 + w by ring]
  exact mul_div_cancel_right₀ _ hlogs

/-- Every positive-order Xi ray jet retains the exact Gamma constant after the reverse-Bessel
polynomial scaling. -/
theorem tendsto_scaled_iteratedDeriv_xiRayLogDeriv_shift (j : ℕ) (hj : 0 < j) :
    Tendsto
      (fun w : ℝ => w ^ j * iteratedDeriv j xiRayLogDeriv (1 / 2 + w))
      atTop
      (nhds (((-1 : ℝ) ^ (j + 1) * ((j - 1).factorial : ℝ)) / 2)) := by
  have hcomplex :=
    (tendsto_scaled_iteratedDeriv_xiLogDeriv_allOrder j hj).comp tendsto_add_half
  have hinv : Tendsto (fun w : ℝ => w⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hratioR : Tendsto (fun w : ℝ => w / (1 / 2 + w)) atTop (nhds 1) := by
    have hden : Tendsto (fun w : ℝ => 1 + (1 / 2) * w⁻¹) atTop (nhds 1) := by
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1)).add
          (hinv.const_mul (1 / 2 : ℝ))
    have hi := tendsto_inv₀ (by norm_num : (1 : ℝ) ≠ 0) |>.comp hden
    have hi' : Tendsto (fun w : ℝ => (1 + (1 / 2) * w⁻¹)⁻¹)
        atTop (nhds 1) := by
      simpa [Function.comp_def] using hi
    apply hi'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
    field_simp [hw.ne']
    ring
  have hratioC : Tendsto
      (fun w : ℝ => (((w / (1 / 2 + w) : ℝ) : ℂ) ^ j))
      atTop (nhds 1) := by
    simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp hratioR).pow j
  have hmul := hratioC.mul hcomplex
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hmul
  have hlimRe :
      ((((1 : ℂ) *
        (((-1 : ℂ) ^ (j + 1) * ((j - 1).factorial : ℂ)) / 2))).re) =
        ((-1 : ℝ) ^ (j + 1) * ((j - 1).factorial : ℝ)) / 2 := by
    have hcast : (1 : ℂ) *
        (((-1 : ℂ) ^ (j + 1) * ((j - 1).factorial : ℂ)) / 2) =
        (((( (-1 : ℝ) ^ (j + 1) * ((j - 1).factorial : ℝ)) / 2 : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [hcast, ofReal_re]
  rw [hlimRe] at hre
  apply hre.congr'
  filter_upwards [eventually_gt_atTop (1 / 2 : ℝ)] with w hw
  have hs : 1 < 1 / 2 + w := by linarith
  have harg : (1 / 2 + w : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hs)
  rw [iteratedDeriv_xiRayLogDeriv_eq_re j hs]
  have hpow : (w / (1 / 2 + w)) ^ j * (1 / 2 + w) ^ j = w ^ j := by
    rw [div_pow]
    field_simp [pow_ne_zero j harg]
  have hcoef : (((w / (1 / 2 + w) : ℝ) : ℂ) ^ j) *
      (((1 / 2 + w : ℝ) : ℂ) ^ j) = ((w ^ j : ℝ) : ℂ) := by
    exact_mod_cast hpow
  simp only [Function.comp_apply]
  rw [← mul_assoc, hcoef]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private theorem tendsto_positive_source_term_div_log
    (n j : ℕ) (hj : 0 < j) :
    Tendsto
      (fun w : ℝ =>
        ((-1 : ℝ) ^ j * (squaredRadialJetWeight n j : ℝ) * w ^ j *
          iteratedDeriv j xiRayLogDeriv (1 / 2 + w)) / Real.log w)
      atTop (nhds 0) := by
  have hscaled := (tendsto_scaled_iteratedDeriv_xiRayLogDeriv_shift j hj).const_mul
    ((-1 : ℝ) ^ j * (squaredRadialJetWeight n j : ℝ))
  have hdiv := hscaled.div_atTop Real.tendsto_log_atTop
  apply hdiv.congr'
  filter_upwards with w
  ring

/-- The completed source jet has exactly its constant reverse-Bessel coefficient as logarithmic
leading term. -/
theorem tendsto_completedSourceJet_div_log (n : ℕ) :
    Tendsto
      (fun w : ℝ => completedSourceJet n w / Real.log w)
      atTop (nhds ((squaredRadialJetWeight n 0 : ℝ) / 2)) := by
  let term : ℕ → ℝ → ℝ := fun j w =>
    ((-1 : ℝ) ^ j * (squaredRadialJetWeight n j : ℝ) * w ^ j *
      iteratedDeriv j xiRayLogDeriv (1 / 2 + w)) / Real.log w
  let target : ℕ → ℝ := fun j => if j = 0 then (squaredRadialJetWeight n 0 : ℝ) / 2 else 0
  have hterm : ∀ j ∈ Finset.range (n + 1),
      Tendsto (term j) atTop (nhds (target j)) := by
    intro j hjrange
    rcases eq_or_ne j 0 with rfl | hj0
    · simp only [term, target, if_pos, pow_zero, one_mul]
      have h := tendsto_xiRayLogDeriv_shift_div_log.const_mul
        (squaredRadialJetWeight n 0 : ℝ)
      convert h using 1
      · funext w
        simp only [iteratedDeriv_zero]
        ring
      · ring
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      simp only [target, if_neg hj0]
      exact tendsto_positive_source_term_div_log n j hjpos
  have hsum := tendsto_finsetSum (Finset.range (n + 1)) hterm
  have htarget : ∑ j ∈ Finset.range (n + 1), target j =
      (squaredRadialJetWeight n 0 : ℝ) / 2 := by
    rw [Finset.sum_eq_single 0]
    · simp [target]
    · intro b hb hb0
      simp [target, hb0]
    · simp
  rw [htarget] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  rw [completedSourceJet, Finset.sum_div]

/-- The constant reverse-Bessel coefficient, after the exact source-to-moment normalization, is
the normalized central-binomial coefficient. -/
theorem squaredRadialJetWeight_zero_normalized_eq (n : ℕ) :
    (squaredRadialJetWeight n 0 : ℝ) /
        ((2 : ℝ) ^ n * (n.factorial : ℝ)) =
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom n := by
  have hq := squaredRadialJetWeight_eq_closedForm n 0 (Nat.zero_le n)
  have hclosedNatDen : (squaredRadialJetWeight n 0 : ℝ) =
      (Nat.factorial (2 * n) : ℝ) /
        (((2 ^ n * n.factorial * 1 : ℕ) : ℝ)) := by
    rw [squaredRadialJetWeightClosedForm] at hq
    simp only [Nat.sub_zero, Nat.factorial_zero] at hq
    have hcast := congrArg (fun q : ℚ => (q : ℝ)) hq
    norm_num at hcast ⊢
    exact hcast
  have hclosed : (squaredRadialJetWeight n 0 : ℝ) =
      (Nat.factorial (2 * n) : ℝ) /
        ((2 : ℝ) ^ n * (n.factorial : ℝ)) := by
    simpa only [Nat.mul_one, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hclosedNatDen
  have hfac : (Nat.centralBinom n : ℝ) *
      ((n.factorial : ℝ) * (n.factorial : ℝ)) =
        (Nat.factorial (2 * n) : ℝ) := by
    exact_mod_cast
      GaloisForLFunctions.HTGeometry.centralBinom_mul_factorial_sq n
  have htwo : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hnfac : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [hclosed, GaloisForLFunctions.HTGeometry.normalizedCentralBinom]
  have hfour : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  rw [hfour]
  field_simp [htwo, hnfac]
  nlinarith

/-- Full all-order shifted-Xi moment asymptotic in the square-root parameter.  The limit is the
arcsine moment sequence `centralBinom n / 4^n`. -/
theorem tendsto_scaled_re_xiShiftedReciprocalMoment_squareParam (n : ℕ) :
    Tendsto
      (fun w : ℝ =>
        2 * w ^ (2 * n + 1) / Real.log w *
          (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) n).re)
      atTop
      (nhds (GaloisForLFunctions.HTGeometry.normalizedCentralBinom n)) := by
  have hsource := tendsto_completedSourceJet_div_log n
  have hscale := hsource.const_mul
    (2 / ((2 : ℝ) ^ n * (n.factorial : ℝ)))
  have hlim :
      2 / ((2 : ℝ) ^ n * (n.factorial : ℝ)) *
          ((squaredRadialJetWeight n 0 : ℝ) / 2) =
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom n := by
    rw [← squaredRadialJetWeight_zero_normalized_eq n]
    ring
  rw [hlim] at hscale
  apply hscale.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
  have hlog : Real.log w ≠ 0 := ne_of_gt (Real.log_pos hw)
  rw [completedSourceJet_eq_xiShiftedReciprocalMoment n (lt_trans zero_lt_one hw)]
  field_simp [hlog, hw0]

end

end RHTower
