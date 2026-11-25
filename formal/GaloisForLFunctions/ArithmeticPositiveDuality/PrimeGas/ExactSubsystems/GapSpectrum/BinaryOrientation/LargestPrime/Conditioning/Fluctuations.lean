import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Conditioning.MovingCutoff

/-! # The energy mean and variance below a largest-prime cutoff -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime

open Filter Topology Set _root_.RHTower _root_.RHTower.BAGTrace

def conditionalMoment (c : ℝ) (h : Ioi (0:ℝ)) (k : ℕ) : ℝ :=
  ∑ d : CutStates c h, conditionalWeight c h d*(measuredEnergy c h d)^k

def conditionalVariance (c : ℝ) (h : Ioi (0:ℝ)) : ℝ :=
  ∑ d : CutStates c h, conditionalWeight c h d*(measuredEnergy c h d-conditionalMoment c h 1)^2

theorem moment_at_zero (c : ℝ) (h : Ioi (0:ℝ)) (k : ℕ) :
    momentProbe c h k 0 = (conditionalMoment c h k:ℂ) := by
  simp only [momentProbe,conditionalMoment,zero_mul,Complex.exp_zero,mul_one,
    Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_pow]

theorem raw_moment_limit {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Tendsto (fun h => conditionalMoment c h k) criticalApproach (𝓝 (iteratedDeriv k (limitTransform c) 0).re) := by
  have H := (Complex.continuous_re.tendsto _).comp
    (conditioned_jet_limit (z := 0) hc k tendsto_const_nhds)
  simpa only [Function.comp_def,moment_at_zero,Complex.ofReal_re] using H

theorem conditionalVariance_eq (c : ℝ) (h : Ioi (0:ℝ)) :
    conditionalVariance c h = conditionalMoment c h 2-(conditionalMoment c h 1)^2 := by
  let m := conditionalMoment c h 1
  have hm : (∑ d, conditionalWeight c h d*measuredEnergy c h d) = m := by simp [m,conditionalMoment]
  calc conditionalVariance c h = ∑ d, ((conditionalWeight c h d*(measuredEnergy c h d)^2 -
      (2*m)*(conditionalWeight c h d*measuredEnergy c h d))+m^2*conditionalWeight c h d) := by
        apply Finset.sum_congr rfl
        intro d _
        change conditionalWeight c h d*(measuredEnergy c h d-m)^2 = _
        ring
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,hm,sum_conditionalWeight]
      change conditionalMoment c h 2-2*m*m+m^2*1 = conditionalMoment c h 2-m^2
      ring

private theorem mean_eq_div {u : ℂ} (hu : u ≠ 0) : criticalExponentialMean u = (Complex.exp u-1)/u := by
  apply (eq_div_iff hu).mpr
  have H := sub_smul_dslope Complex.exp 0 u
  rw [mul_comm]
  simpa only [sub_zero,Complex.exp_zero,smul_eq_mul,criticalExponentialMean] using H

private theorem mean_deriv {u : ℂ} (hu : u ≠ 0) :
    HasDerivAt criticalExponentialMean ((Complex.exp u*u-(Complex.exp u-1))/u^2) u := by
  have H := ((Complex.hasDerivAt_exp u).sub_const 1).div (hasDerivAt_id u) hu
  simp only [id_eq,mul_one] at H
  exact H.congr_of_eventuallyEq ((eventually_ne_nhds hu).mono fun _ hw => mean_eq_div hw)

private theorem carrier_first (u : ℂ) :
    deriv criticalEulerCarrier u = criticalEulerCarrier u*criticalExponentialMean u :=
  ((criticalEulerExponent_hasDerivAt u).cexp).deriv

private theorem carrier_second {u : ℂ} (hu : u ≠ 0) :
    iteratedDeriv 2 criticalEulerCarrier u = criticalEulerCarrier u*
      ((criticalExponentialMean u)^2+(Complex.exp u*u-(Complex.exp u-1))/u^2) := by
  rw [show (2:ℕ) = 1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,funext carrier_first]
  have H : HasDerivAt (fun w => criticalEulerCarrier w*criticalExponentialMean w)
      (criticalEulerCarrier u*criticalExponentialMean u*criticalExponentialMean u+
        criticalEulerCarrier u*((Complex.exp u*u-(Complex.exp u-1))/u^2)) u :=
    ((criticalEulerExponent_hasDerivAt u).cexp).mul (mean_deriv hu)
  change deriv (fun w => criticalEulerCarrier w*criticalExponentialMean w) u = _
  rw [H.deriv]
  ring

theorem first_jet {c : ℝ} (hc : 0 < c) :
    iteratedDeriv 1 (limitTransform c) 0 = ((1-Real.exp (-c):ℝ):ℂ) := by
  have hu : -(c:ℂ) ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hc.ne')
  have hF : criticalEulerCarrier (-(c:ℂ)) ≠ 0 := Complex.exp_ne_zero _
  rw [limitTransform_jet,pow_one,zero_sub,mul_neg_one,iteratedDeriv_one,carrier_first,mean_eq_div hu]
  push_cast
  field_simp [hF,hu,Complex.ofReal_ne_zero.mpr hc.ne']
  ring

theorem second_jet {c : ℝ} (hc : 0 < c) :
    iteratedDeriv 2 (limitTransform c) 0 =
      (((1-(1+c)*Real.exp (-c))+(1-Real.exp (-c))^2:ℝ):ℂ) := by
  have hu : -(c:ℂ) ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hc.ne')
  have hF : criticalEulerCarrier (-(c:ℂ)) ≠ 0 := Complex.exp_ne_zero _
  rw [limitTransform_jet,zero_sub,mul_neg_one,carrier_second hu,mean_eq_div hu]
  push_cast
  field_simp [hF,hu,Complex.ofReal_ne_zero.mpr hc.ne']
  ring

/-- The expected scaled energy of the retained orientation. -/
theorem conditioned_mean_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun h => conditionalMoment c h 1) criticalApproach (𝓝 (1-Real.exp (-c))) := by
  simpa only [first_jet hc,Complex.ofReal_re] using raw_moment_limit hc 1

/-- The limiting variance records the energy lost to the excluded large primes. -/
theorem conditioned_variance_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (conditionalVariance c) criticalApproach (𝓝 (1-(1+c)*Real.exp (-c))) := by
  have H := (raw_moment_limit hc 2).sub ((conditioned_mean_limit hc).pow 2)
  rw [second_jet hc,Complex.ofReal_re,add_sub_cancel_right] at H
  exact H.congr fun h => (conditionalVariance_eq c h).symm

#print axioms moment_at_zero
#print axioms raw_moment_limit
#print axioms conditionalVariance_eq
#print axioms first_jet
#print axioms second_jet
#print axioms conditioned_mean_limit
#print axioms conditioned_variance_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime
