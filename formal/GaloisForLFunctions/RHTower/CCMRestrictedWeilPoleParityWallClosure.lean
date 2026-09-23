import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleParityWallGammaInvariant
import GaloisForLFunctions.RHTower.PoleBoundaryLogSharpConstant

open Set MeasureTheory Filter
open scoped Topology
noncomputable section
namespace RHTower

private def ccmGammaPoleWallIntegral (s : ℝ) : ℝ :=
  (1 / 2) * (∫ t in 0..2 * s, Real.exp (-t) * ccmGammaPoleBoundaryLog (2 * t)) -
    (∫ t in 0..2 * s,
      Real.exp t * (ccmGammaPoleBoundaryLog t - ccmGammaPoleBoundaryLog (2 * t) / 2)) +
    (Real.exp (2 * s) - 1) * ccmGammaPoleBoundaryLog (2 * s) -
      Real.sinh (2 * s) * ccmGammaPoleBoundaryLog (4 * s)

private theorem ccmGammaPoleWallInvariant_eq_integral (s : ℝ) :
    ccmGammaPoleWallInvariant s = ccmGammaPoleWallIntegral s := by
  unfold ccmGammaPoleWallInvariant ccmGammaPoleSelfBoundarySlope
    ccmGammaPoleSelfBoundaryPrimitive ccmGammaPoleWallIntegral
  change
    Real.cosh s *
        (Real.exp s / 2 * (∫ t in 0..2 * s, Real.exp (-t) * ccmGammaPoleBoundaryLog (2 * t)) -
          Real.exp (-s) * (∫ t in 0..2 * s,
            Real.exp t * (ccmGammaPoleBoundaryLog t - ccmGammaPoleBoundaryLog (2 * t) / 2)) +
          Real.exp (-s) * ccmGammaPoleBoundaryLog (4 * s) +
          2 * Real.exp s *
            (ccmGammaPoleBoundaryLog (2 * s) - ccmGammaPoleBoundaryLog (4 * s) / 2)) -
      Real.sinh s *
        (Real.exp s / 2 * (∫ t in 0..2 * s, Real.exp (-t) * ccmGammaPoleBoundaryLog (2 * t)) +
          Real.exp (-s) * (∫ t in 0..2 * s,
            Real.exp t * (ccmGammaPoleBoundaryLog t - ccmGammaPoleBoundaryLog (2 * t) / 2))) -
      2 * ccmGammaPoleBoundaryLog (2 * s) = ccmGammaPoleWallIntegral s
  unfold ccmGammaPoleWallIntegral
  rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
  rw [Real.sinh_eq (2 * s)]
  have h2 : Real.exp (2 * s) = Real.exp s ^ (2 : ℕ) := by
    rw [show 2 * s = s + s by ring, Real.exp_add]
    ring
  have hn2 : Real.exp (-(2 * s)) = (Real.exp s)⁻¹ ^ (2 : ℕ) := by
    rw [show -(2 * s) = (-s) + (-s) by ring, Real.exp_add, Real.exp_neg]
    ring
  rw [h2, hn2]
  have he : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  field_simp [he]
  ring

private def ccmGammaPoleWallFirstPrimitive (t : ℝ) : ℝ :=
  (Real.exp t - 1) * ccmGammaPoleBoundaryLog t

private def ccmGammaPoleWallSecondPrimitive (t : ℝ) : ℝ :=
  Real.sinh t * ccmGammaPoleBoundaryLog (2 * t)

private theorem hasDerivAt_ccmGammaPoleWallFirstPrimitive {t : ℝ} (ht : 0 < t) :
    HasDerivAt ccmGammaPoleWallFirstPrimitive
      (Real.exp t * ccmGammaPoleBoundaryLog t - 1) t := by
  unfold ccmGammaPoleWallFirstPrimitive
  have hd := ((Real.hasDerivAt_exp t).sub_const 1).mul
    (hasDerivAt_ccmGammaPoleBoundaryLog ht)
  convert! hd using 1
  have hne : Real.exp t - 1 ≠ 0 := ne_of_gt
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht))
  field_simp [hne]
  ring

private theorem hasDerivAt_ccmGammaPoleWallSecondPrimitive {t : ℝ} (ht : 0 < t) :
    HasDerivAt ccmGammaPoleWallSecondPrimitive
      (Real.cosh t * ccmGammaPoleBoundaryLog (2 * t) - Real.exp (-t)) t := by
  unfold ccmGammaPoleWallSecondPrimitive
  have hlog : HasDerivAt (fun y => ccmGammaPoleBoundaryLog (2 * y))
      (-2 / (Real.exp (2 * t) - 1)) t := by
    have h := (hasDerivAt_ccmGammaPoleBoundaryLog (show 0 < 2 * t by linarith)).comp t
      ((hasDerivAt_id t).const_mul 2)
    convert! h using 1
    ring
  convert! (Real.hasDerivAt_sinh t).mul hlog using 1
  have h2 : Real.exp (2 * t) - 1 ≠ 0 := ne_of_gt
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith)))
  have he : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
  rw [show 2 * t = t + t by ring] at h2 ⊢
  simp only [Real.exp_add] at h2 ⊢
  have hterm :
      (Real.exp t - (Real.exp t)⁻¹) / 2 *
          (-2 / (Real.exp t * Real.exp t - 1)) = -(Real.exp t)⁻¹ := by
    have hden : -1 + Real.exp t ^ (2 : ℕ) ≠ 0 := by
      simpa [pow_two, sub_eq_add_neg, add_comm] using h2
    have hden' : Real.exp t ^ (2 : ℕ) - 1 ≠ 0 := by
      simpa [pow_two] using h2
    field_simp [h2, he]
  rw [hterm]
  ring

private theorem ccmGammaPoleWallFirstPrimitive_eq (t : ℝ) :
    ccmGammaPoleWallFirstPrimitive t =
      -Real.exp t * ((1 - Real.exp (-t)) * Real.log (1 - Real.exp (-t))) := by
  unfold ccmGammaPoleWallFirstPrimitive ccmGammaPoleBoundaryLog
  have hprod : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [show Real.exp t - 1 = Real.exp t * (1 - Real.exp (-t)) by
    calc
      Real.exp t - 1 = Real.exp t - Real.exp t * Real.exp (-t) := by rw [hprod]
      _ = Real.exp t * (1 - Real.exp (-t)) := by ring]
  ring

private theorem ccmGammaPoleWallSecondPrimitive_eq (t : ℝ) :
    ccmGammaPoleWallSecondPrimitive t =
      -(Real.exp t / 2) *
        ((1 - Real.exp (-(2 * t))) * Real.log (1 - Real.exp (-(2 * t)))) := by
  unfold ccmGammaPoleWallSecondPrimitive ccmGammaPoleBoundaryLog
  have hprod : Real.exp t * Real.exp (-(2 * t)) = Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.sinh_eq, ← hprod]
  ring

private theorem tendsto_ccmGammaPoleWallFirstPrimitive_zero :
    Tendsto ccmGammaPoleWallFirstPrimitive (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [show ccmGammaPoleWallFirstPrimitive = fun t =>
      -Real.exp t * ((1 - Real.exp (-t)) * Real.log (1 - Real.exp (-t))) by
    funext t
    exact ccmGammaPoleWallFirstPrimitive_eq t]
  have hbase : Tendsto (fun t : ℝ =>
      (1 - Real.exp (-t)) * Real.log (1 - Real.exp (-t))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ =>
        (1 - Real.exp (-t)) * Real.log (1 - Real.exp (-t))) :=
      Real.continuous_mul_log.comp (by fun_prop)
    have h := hc.tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hcoef : Tendsto (fun t : ℝ => -Real.exp t) (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
    have h := (Real.continuous_exp.tendsto 0).neg
    simpa using h.mono_left nhdsWithin_le_nhds
  simpa using hcoef.mul hbase

private theorem tendsto_ccmGammaPoleWallSecondPrimitive_zero :
    Tendsto ccmGammaPoleWallSecondPrimitive (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [show ccmGammaPoleWallSecondPrimitive = fun t =>
      -(Real.exp t / 2) *
        ((1 - Real.exp (-(2 * t))) * Real.log (1 - Real.exp (-(2 * t)))) by
    funext t
    exact ccmGammaPoleWallSecondPrimitive_eq t]
  have hbase : Tendsto (fun t : ℝ =>
      (1 - Real.exp (-(2 * t))) * Real.log (1 - Real.exp (-(2 * t))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ =>
        (1 - Real.exp (-(2 * t))) * Real.log (1 - Real.exp (-(2 * t)))) :=
      Real.continuous_mul_log.comp (by fun_prop)
    have h := hc.tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hcoef : Tendsto (fun t : ℝ => -(Real.exp t / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(1 / 2))) := by
    have h := ((Real.continuous_exp.tendsto 0).div_const 2).neg
    norm_num at h ⊢
    exact h.mono_left nhdsWithin_le_nhds
  simpa using hcoef.mul hbase

private def ccmGammaPoleWallAntiderivative (t : ℝ) : ℝ :=
  ccmGammaPoleWallSecondPrimitive t - ccmGammaPoleWallFirstPrimitive t - t - Real.exp (-t)

private theorem hasDerivAt_ccmGammaPoleWallAntiderivative {t : ℝ} (ht : 0 < t) :
    HasDerivAt ccmGammaPoleWallAntiderivative
      (Real.cosh t * ccmGammaPoleBoundaryLog (2 * t) -
        Real.exp t * ccmGammaPoleBoundaryLog t) t := by
  unfold ccmGammaPoleWallAntiderivative
  convert! (((hasDerivAt_ccmGammaPoleWallSecondPrimitive ht).sub
    (hasDerivAt_ccmGammaPoleWallFirstPrimitive ht)).sub (hasDerivAt_id t)).sub
    (((hasDerivAt_id t).neg).exp) using 1
  have hid : (-id : ℝ → ℝ) t = -t := rfl
  rw [hid]
  ring

private theorem tendsto_ccmGammaPoleWallAntiderivative_zero :
    Tendsto ccmGammaPoleWallAntiderivative (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
  unfold ccmGammaPoleWallAntiderivative
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hexp : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := (Real.continuous_exp.comp continuous_neg).tendsto 0
    simpa only [Function.comp_def, neg_zero, Real.exp_zero] using
      h.mono_left nhdsWithin_le_nhds
  simpa using (((tendsto_ccmGammaPoleWallSecondPrimitive_zero.sub
    tendsto_ccmGammaPoleWallFirstPrimitive_zero).sub hid).sub hexp)

private theorem intervalIntegrable_ccmGammaPoleWallIntegrand {s : ℝ} (hs : 0 < s) :
    IntervalIntegrable (fun t : ℝ =>
      Real.cosh t * ccmGammaPoleBoundaryLog (2 * t) -
        Real.exp t * ccmGammaPoleBoundaryLog t) volume 0 (2 * s) := by
  have hL2 := intervalIntegrable_ccmGammaPoleBoundaryLog_two_mul (show 0 < 2 * s by linarith)
  have hL := intervalIntegrable_ccmGammaPoleBoundaryLog (show 0 < 2 * s by linarith)
  refine ((hL2.continuousOn_mul Real.continuous_cosh.continuousOn).sub
    (hL.continuousOn_mul Real.continuous_exp.continuousOn)).congr ?_
  intro t ht
  ring

private theorem integral_ccmGammaPoleWallIntegrand {s : ℝ} (hs : 0 < s) :
    (∫ t in 0..2 * s,
      Real.cosh t * ccmGammaPoleBoundaryLog (2 * t) -
        Real.exp t * ccmGammaPoleBoundaryLog t) =
      ccmGammaPoleWallSecondPrimitive (2 * s) -
        ccmGammaPoleWallFirstPrimitive (2 * s) - 2 * s - Real.exp (-(2 * s)) + 1 := by
  have hi := intervalIntegrable_ccmGammaPoleWallIntegrand hs
  have hb : Tendsto ccmGammaPoleWallAntiderivative (𝓝[<] (2 * s))
      (𝓝 (ccmGammaPoleWallAntiderivative (2 * s))) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      ((hasDerivAt_ccmGammaPoleWallAntiderivative (show 0 < 2 * s by linarith)).continuousAt.tendsto)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (show 0 < 2 * s by linarith)
    (fun x hx => hasDerivAt_ccmGammaPoleWallAntiderivative hx.1) hi
    tendsto_ccmGammaPoleWallAntiderivative_zero hb
  simpa [ccmGammaPoleWallAntiderivative] using h

private theorem ccmGammaPoleWallIntegral_eq {s : ℝ} (hs : 0 < s) :
    ccmGammaPoleWallIntegral s = 1 - 2 * s - Real.exp (-2 * s) := by
  have hI : IntervalIntegrable (fun t : ℝ =>
      Real.exp (-t) * ccmGammaPoleBoundaryLog (2 * t)) volume 0 (2 * s) :=
    (intervalIntegrable_ccmGammaPoleBoundaryLog_two_mul (show 0 < 2 * s by linarith)).continuousOn_mul
      (Real.continuous_exp.comp continuous_neg).continuousOn |>.congr (by
        intro t ht
        change Real.exp (-t) * ccmGammaPoleBoundaryLog (2 * t) =
          Real.exp (-t) * ccmGammaPoleBoundaryLog (2 * t)
        rfl)
  have hJ : IntervalIntegrable (fun t : ℝ =>
      Real.exp t * (ccmGammaPoleBoundaryLog t - ccmGammaPoleBoundaryLog (2 * t) / 2)) volume 0 (2 * s) :=
    ((intervalIntegrable_ccmGammaPoleBoundaryLog (show 0 < 2 * s by linarith)).sub
      ((intervalIntegrable_ccmGammaPoleBoundaryLog_two_mul (show 0 < 2 * s by linarith)).div_const 2)).continuousOn_mul
        Real.continuous_exp.continuousOn |>.congr (by
          intro t ht
          ring)
  have hcombine :
      (1 / 2) * (∫ t in 0..2 * s, Real.exp (-t) * ccmGammaPoleBoundaryLog (2 * t)) -
        (∫ t in 0..2 * s,
          Real.exp t * (ccmGammaPoleBoundaryLog t - ccmGammaPoleBoundaryLog (2 * t) / 2)) =
        ∫ t in 0..2 * s,
          Real.cosh t * ccmGammaPoleBoundaryLog (2 * t) -
            Real.exp t * ccmGammaPoleBoundaryLog t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (hI.const_mul (1 / 2)) hJ]
    apply intervalIntegral.integral_congr
    intro t ht
    change 1 / 2 * (Real.exp (-t) * ccmGammaPoleBoundaryLog (2 * t)) -
      Real.exp t * (ccmGammaPoleBoundaryLog t - ccmGammaPoleBoundaryLog (2 * t) / 2) =
      Real.cosh t * ccmGammaPoleBoundaryLog (2 * t) - Real.exp t * ccmGammaPoleBoundaryLog t
    rw [Real.cosh_eq]
    ring
  unfold ccmGammaPoleWallIntegral
  rw [hcombine, integral_ccmGammaPoleWallIntegrand hs]
  unfold ccmGammaPoleWallFirstPrimitive ccmGammaPoleWallSecondPrimitive
  ring

/-- Exact singular-endpoint normalization of the literal covariant Gamma/polar wall charge. -/
theorem ccmGammaPoleWallInvariant_eq {s : ℝ} (hs : 0 < s) :
    ccmGammaPoleWallInvariant s = 1 - 2 * s - Real.exp (-2 * s) := by
  rw [ccmGammaPoleWallInvariant_eq_integral, ccmGammaPoleWallIntegral_eq hs]

/-- The complete polar--Gamma smooth forcing in the parity-wall law vanishes identically. -/
theorem ccmWeilParitySmoothWallForcing_eq_zero (a : SuzukiPositiveAperture) :
    ccmWeilParitySmoothWallForcing a.1 = 0 := by
  rw [ccmWeilParitySmoothWallForcing_eq_gammaInvariant, ccmGammaPoleWallInvariant_eq a.2]
  ring

/-- Literal finite parity heads obey a homogeneous common-clock wall law. -/
theorem ccmWeilParityHeadTransgression_zero
    (S : Finset ℕ) (a : SuzukiPositiveAperture) :
    deriv (ccmWeilParityClockHead S) a.1 +
        Real.cosh a.1 * deriv (ccmWeilParityAgeHead S) a.1 -
          Real.sinh a.1 * ccmWeilParityAgeHead S a.1 = 0 := by
  rw [ccmWeilParityHeadTransgression]
  exact ccmWeilParitySmoothWallForcing_eq_zero a

end RHTower
