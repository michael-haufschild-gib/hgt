import GaloisForLFunctions.RHTower.CCMPoleLeadingCancellation
import GaloisForLFunctions.RHTower.CCMContinuousNegativeSmoothSources

/-!
# Exact leading coefficient of odd prime--continuous cancellation

Both the literal continuous odd quadratic and the prime-operator quadratic
are asymptotic to -2 exp(2a). Their difference is the full odd Weil energy,
already proved little-o of exp(2a). The asymptotic identities do not determine
the sign of that residual.
-/

noncomputable section
open Filter
open scoped InnerProduct

namespace RHTower

private theorem aperture_val_tendsto :
    Tendsto (fun a : SuzukiPositiveAperture => a.1) atTop atTop :=
  tendsto_Ioi_atTop.mp tendsto_id

theorem tendsto_ccmGammaPoleCrossBoundaryMass_scaled_zero :
    Tendsto (fun a : SuzukiPositiveAperture =>
      Real.exp (-(2 * a.1)) * ccmGammaPoleCrossBoundaryMass a) atTop (nhds 0) := by
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (aperture_val_tendsto.const_mul_atTop two_pos)
  have hlim : Tendsto (fun a : SuzukiPositiveAperture =>
      (2 * Real.log 2 + Real.pi + 1) * Real.exp (-(2 * a.1))) atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero] using he.const_mul (2 * Real.log 2 + Real.pi + 1)
  apply squeeze_zero (fun a => mul_nonneg (Real.exp_pos _).le
    (ccmGammaPoleBoundaryMass_nonneg a).1) _ hlim
  intro a
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (ccmGammaPoleCrossBoundaryMass_le a)
    (Real.exp_pos (-(2 * a.1))).le

theorem tendsto_ccmGammaPoleSelfBoundaryMass_scaled_zero :
    Tendsto (fun a : SuzukiPositiveAperture =>
      Real.exp (-(2 * a.1)) * ccmGammaPoleSelfBoundaryMass a) atTop (nhds 0) := by
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp aperture_val_tendsto
  have hlim : Tendsto (fun a : SuzukiPositiveAperture =>
      (2 * Real.log 2 + Real.pi + 1) * Real.exp (-a.1)) atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero] using he.const_mul (2 * Real.log 2 + Real.pi + 1)
  apply squeeze_zero (fun a => mul_nonneg (Real.exp_pos _).le
    (ccmGammaPoleBoundaryMass_nonneg a).2) _ hlim
  intro a
  calc
    _ ≤ Real.exp (-(2 * a.1)) * ((2 * Real.log 2 + Real.pi + 1) * Real.exp a.1) :=
      mul_le_mul_of_nonneg_left (ccmGammaPoleSelfBoundaryMass_le a) (Real.exp_pos _).le
    _ = _ := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring

theorem ccmOddPoleGammaPolarBalance_scaled_eq (a : SuzukiPositiveAperture) :
    let e := Real.exp (-a.1)
    let t := a.1 * e
    let c := -Real.eulerMascheroniConstant - Real.log (2 * Real.pi)
    Real.exp (-(2 * a.1)) * ccmOddPoleGammaPolarBalance a =
      2 * (c * (1 - e ^ 2 - 2 * t) * e - e + (2 * t + e) * e ^ 2 + 2 * t ^ 2 +
        Real.exp (-(2 * a.1)) * ccmGammaPoleSelfBoundaryMass a -
        Real.exp (-(2 * a.1)) * ccmGammaPoleCrossBoundaryMass a - (1 - e ^ 2 - 2 * t) ^ 2) := by
  dsimp only
  let e := Real.exp (-a.1)
  let t := a.1 * e
  let c := -Real.eulerMascheroniConstant - Real.log (2 * Real.pi)
  let b := 2 * Real.sinh a.1 - 2 * a.1
  have hdouble : Real.exp (-(2 * a.1)) = e ^ 2 := by
    dsimp only [e]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hcancel : Real.exp a.1 * e = 1 := by
    dsimp only [e]
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hb : b * e = 1 - e ^ 2 - 2 * t := by
    calc
      _ = Real.exp a.1 * e - e ^ 2 - 2 * t := by
        dsimp only [b, t, e]
        rw [Real.sinh_eq]
        ring
      _ = _ := by rw [hcancel]
  rw [hdouble, ccmOddPoleGammaPolarBalance]
  change e ^ 2 * (2 * (c * b - Real.exp a.1 + (2 * a.1 + 1) * e + 2 * a.1 ^ 2 +
    ccmGammaPoleSelfBoundaryMass a - ccmGammaPoleCrossBoundaryMass a - b ^ 2)) = _
  calc
    _ = 2 * (c * (b * e) * e - (Real.exp a.1 * e) * e + (2 * t + e) * e ^ 2 +
        2 * t ^ 2 + e ^ 2 * ccmGammaPoleSelfBoundaryMass a -
        e ^ 2 * ccmGammaPoleCrossBoundaryMass a - (b * e) ^ 2) := by
      dsimp only [t]
      ring
    _ = _ := by rw [hb, hcancel, one_mul]

/-- The negative odd continuous term has exact leading coefficient -2. -/
theorem tendsto_ccmOddPoleGammaPolarBalance_scaled_neg_two :
    Tendsto (fun a : SuzukiPositiveAperture =>
      Real.exp (-(2 * a.1)) * ccmOddPoleGammaPolarBalance a) atTop (nhds (-2)) := by
  let c := -Real.eulerMascheroniConstant - Real.log (2 * Real.pi)
  have he : Tendsto (fun a : SuzukiPositiveAperture => Real.exp (-a.1)) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp aperture_val_tendsto
  have ht : Tendsto (fun a : SuzukiPositiveAperture => a.1 * Real.exp (-a.1)) atTop (nhds 0) := by
    simpa only [Function.comp_def, pow_one] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp aperture_val_tendsto
  have hu : Tendsto (fun a : SuzukiPositiveAperture =>
      1 - (Real.exp (-a.1)) ^ 2 - 2 * (a.1 * Real.exp (-a.1))) atTop (nhds 1) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero] using
      (tendsto_const_nhds.sub (he.pow 2) (a := (1 : ℝ))).sub (ht.const_mul 2)
  have h₁ := ((hu.const_mul c).mul he).sub he
  have h₂ := ((ht.const_mul 2).add he).mul (he.pow 2)
  have h₃ := (h₁.add h₂).add ((ht.pow 2).const_mul 2)
  have h₄ := (h₃.add tendsto_ccmGammaPoleSelfBoundaryMass_scaled_zero).sub
    tendsto_ccmGammaPoleCrossBoundaryMass_scaled_zero
  have h := (h₄.sub (hu.pow 2)).const_mul 2
  norm_num only [mul_one, mul_zero, sub_zero, add_zero, zero_add, zero_pow, one_pow,
    zero_sub, mul_neg, mul_one] at h
  exact h.congr fun a => (ccmOddPoleGammaPolarBalance_scaled_eq a).symm

/-- The signed recent-minus-old prime budget cancels the negative leading continuous term. -/
theorem tendsto_ccmOddPrimeBudgetDifference_scaled_two :
    Tendsto (fun a : SuzukiPositiveAperture => Real.exp (-(2 * a.1)) *
      (ccmOddPoleRecentPrimeBudget a - ccmOddPoleOldPrimeBudget a)) atTop (nhds 2) := by
  have h := (tendsto_ccmWeilParityPole_scaled_zero (-1) (Or.inr rfl)).sub
    tendsto_ccmOddPoleGammaPolarBalance_scaled_neg_two
  norm_num only [sub_neg_eq_add, zero_add] at h
  refine h.congr fun a => ?_
  rw [ccmWeilOddPole_eq_prime_budgets]
  ring

/-- The actual prime operator and continuous quadratic share the same negative leading coefficient. -/
theorem tendsto_ccmOddPrimeOperator_scaled_neg_two :
    Tendsto (fun a : SuzukiPositiveAperture => Real.exp (-(2 * a.1)) *
      (inner ℂ (ccmFinitePrimeOperator a
        (ccmPolarApertureVector a (1/2) - ccmPolarApertureVector a (-1/2)))
        (ccmPolarApertureVector a (1/2) - ccmPolarApertureVector a (-1/2))).re)
      atTop (nhds (-2)) := by
  refine tendsto_ccmOddPrimeBudgetDifference_scaled_two.neg.congr fun a => ?_
  rw [← ccmFinitePrimeOperator_polar_odd_eq_budgets]
  ring

end RHTower
