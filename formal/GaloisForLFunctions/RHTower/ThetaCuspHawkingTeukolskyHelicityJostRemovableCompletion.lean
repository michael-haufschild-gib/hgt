import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskySexticJostDealiasing

/-!
# Two-channel helicity cancellation of the sextic Jost zero

Write `y` for centered Xi tilt. The exact two-channel scalar/vector mass-jet defect gives the
helicity numerator

`24 y (y+2) / (5 (1/2-y) (5/2+y))`,

while the first charge-minus-two Jost factor is `1 / Gamma(-3+2y)`. Both have a simple zero at
`y=0`. Gamma recurrence cancels their common factor and gives a continuous, nowhere-zero physical
strip completion whose central value is `-16/25`.

Thus this controlled theta-specific helicity weld makes critical divisor incidence removable: it
produces neither a scattering zero nor a pole. Any RH-selecting nonlinear Teukolsky determinant
must contain a different source coefficient or a non-removable channel coupling.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

def d4ThetaHawkingTwoChannelHelicityNumeratorOfTilt (y : ℝ) : ℂ :=
  (24 * y * (y + 2) /
    (5 * (1 / 2 - y) * (5 / 2 + y)) : ℝ)

def d4ThetaHawkingHelicitySexticJostCompletionOfTilt (y : ℝ) : ℂ :=
  12 * (y + 2) /
    (5 * (1 / 2 - y) * (5 / 2 + y) *
      (2 * y - 1) * (2 * y - 2) * (2 * y - 3) *
        GaloisForLFunctions.reciprocalGammaEntire (1 + 2 * (y : ℂ)))

theorem d4ThetaHawkingTwoChannelHelicityNumeratorOfTilt_xi
    (q : XiZeroCopy) :
    d4ThetaHawkingTwoChannelHelicityNumeratorOfTilt (xiSpectralPoint q).im =
      (d4BMXiTwoChannelHelicityTransfer q : ℂ) := by
  rw [d4BMXiTwoChannelHelicityTransfer, d4BMXiTwoChannelBackreactionDefect_eq]
  rw [xiSpectralPoint_im_eq]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hσ : (q.1 : ℂ).re ≠ 0 := ne_of_gt hstrip.1
  have h3σ : 3 - (q.1 : ℂ).re ≠ 0 := ne_of_gt (by linarith)
  have h6σ : 6 - 2 * (q.1 : ℂ).re ≠ 0 := by linarith
  have hσc : ((q.1 : ℂ).re : ℂ) ≠ 0 := by exact_mod_cast hσ
  have h3σc : (3 : ℂ) - ((q.1 : ℂ).re : ℂ) ≠ 0 := by exact_mod_cast h3σ
  have h6σc : (6 : ℂ) - 2 * ((q.1 : ℂ).re : ℂ) ≠ 0 := by exact_mod_cast h6σ
  have h6σc' : (6 : ℂ) - ((q.1 : ℂ).re : ℂ) * 2 ≠ 0 := by
    simpa [mul_comm] using h6σc
  unfold d4ThetaHawkingTwoChannelHelicityNumeratorOfTilt
  push_cast
  rw [show (1 / 2 : ℂ) - (1 / 2 - ((q.1 : ℂ).re : ℂ)) =
      ((q.1 : ℂ).re : ℂ) by ring]
  rw [show (5 / 2 : ℂ) + (1 / 2 - ((q.1 : ℂ).re : ℂ)) =
      3 - ((q.1 : ℂ).re : ℂ) by ring]
  field_simp [hσc, h3σc, h6σc, h6σc']
  ring

lemma d4ThetaHawkingSexticNegativeJost_factor_tilt (y : ℝ) :
    GaloisForLFunctions.reciprocalGammaEntire (-3 + 2 * (y : ℂ)) =
      (2 * y - 1) * (2 * y - 2) * (2 * y - 3) * (2 * y) *
        GaloisForLFunctions.reciprocalGammaEntire (1 + 2 * (y : ℂ)) := by
  have hback := GaloisForLFunctions.reciprocalGammaEntire_neg_nat_add
    3 (2 * (y : ℂ))
  norm_num at hback
  rw [hback]
  have hrec := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (2 * (y : ℂ))
  change GaloisForLFunctions.reciprocalGammaEntire (2 * (y : ℂ)) =
      2 * (y : ℂ) * GaloisForLFunctions.reciprocalGammaEntire (2 * (y : ℂ) + 1) at hrec
  rw [hrec]
  simp [GaloisForLFunctions.reciprocalGammaBackwardProduct,
    Finset.prod_range_succ]
  ring

theorem d4ThetaHawkingHelicitySexticJostCompletionOfTilt_eq_ratio
    (y : ℝ) (hy : y ≠ 0) :
    d4ThetaHawkingHelicitySexticJostCompletionOfTilt y =
      d4ThetaHawkingTwoChannelHelicityNumeratorOfTilt y /
        GaloisForLFunctions.reciprocalGammaEntire (-3 + 2 * (y : ℂ)) := by
  rw [d4ThetaHawkingSexticNegativeJost_factor_tilt]
  unfold d4ThetaHawkingHelicitySexticJostCompletionOfTilt
    d4ThetaHawkingTwoChannelHelicityNumeratorOfTilt
  push_cast
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  field_simp [hyc]
  ring

theorem d4ThetaHawkingHelicitySexticJostCompletionOfTilt_zero :
    d4ThetaHawkingHelicitySexticJostCompletionOfTilt 0 = -16 / 25 := by
  norm_num [d4ThetaHawkingHelicitySexticJostCompletionOfTilt,
    GaloisForLFunctions.reciprocalGammaEntire, Complex.Gamma_one]

theorem continuousAt_d4ThetaHawkingHelicitySexticJostCompletionOfTilt_zero :
    ContinuousAt d4ThetaHawkingHelicitySexticJostCompletionOfTilt 0 := by
  unfold d4ThetaHawkingHelicitySexticJostCompletionOfTilt
  have hcast : Continuous (fun y : ℝ => (y : ℂ)) := Complex.continuous_ofReal
  have hrec : Continuous (fun y : ℝ =>
      GaloisForLFunctions.reciprocalGammaEntire (1 + 2 * (y : ℂ))) := by
    unfold GaloisForLFunctions.reciprocalGammaEntire
    exact Complex.differentiable_one_div_Gamma.continuous.comp
      (continuous_const.add (continuous_const.mul hcast))
  have hnum : Continuous (fun y : ℝ => 12 * ((y : ℂ) + 2)) :=
    continuous_const.mul (hcast.add continuous_const)
  have hA : Continuous (fun y : ℝ => (1 / 2 : ℂ) - (y : ℂ)) :=
    continuous_const.sub hcast
  have hB : Continuous (fun y : ℝ => (5 / 2 : ℂ) + (y : ℂ)) :=
    continuous_const.add hcast
  have h1 : Continuous (fun y : ℝ => 2 * (y : ℂ) - 1) :=
    (continuous_const.mul hcast).sub continuous_const
  have h2 : Continuous (fun y : ℝ => 2 * (y : ℂ) - 2) :=
    (continuous_const.mul hcast).sub continuous_const
  have h3 : Continuous (fun y : ℝ => 2 * (y : ℂ) - 3) :=
    (continuous_const.mul hcast).sub continuous_const
  have hden : Continuous (fun y : ℝ =>
      5 * ((1 / 2 : ℂ) - (y : ℂ)) * ((5 / 2 : ℂ) + (y : ℂ)) *
        (2 * (y : ℂ) - 1) * (2 * (y : ℂ) - 2) * (2 * (y : ℂ) - 3) *
          GaloisForLFunctions.reciprocalGammaEntire (1 + 2 * (y : ℂ))) :=
    (((((continuous_const.mul hA).mul hB).mul h1).mul h2).mul h3).mul hrec
  exact hnum.continuousAt.div hden.continuousAt
    (by norm_num [GaloisForLFunctions.reciprocalGammaEntire, Complex.Gamma_one])

theorem d4ThetaHawkingHelicitySexticJostCompletionOfTilt_ne_zero
    (y : ℝ) (hylo : -1 / 2 < y) (hyhi : y < 1 / 2) :
    d4ThetaHawkingHelicitySexticJostCompletionOfTilt y ≠ 0 := by
  unfold d4ThetaHawkingHelicitySexticJostCompletionOfTilt
  apply div_ne_zero
  · exact mul_ne_zero (by norm_num) (by exact_mod_cast (by linarith : y + 2 ≠ 0))
  · apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · apply mul_ne_zero
            · exact mul_ne_zero (by norm_num)
                (by
                  intro h
                  have hre := congrArg Complex.re h
                  simp at hre
                  linarith)
            · intro h
              have hre := congrArg Complex.re h
              simp at hre
              linarith
          · exact_mod_cast (by linarith : 2 * y - 1 ≠ 0)
        · exact_mod_cast (by linarith : 2 * y - 2 ≠ 0)
      · exact_mod_cast (by linarith : 2 * y - 3 ≠ 0)
    · apply inv_ne_zero
      apply Complex.Gamma_ne_zero
      intro n hn
      have hre := congrArg Complex.re hn
      simp at hre
      have : 0 < 1 + 2 * y := by linarith
      linarith

def d4BMXiHelicitySexticJostCompletion (q : XiZeroCopy) : ℂ :=
  d4ThetaHawkingHelicitySexticJostCompletionOfTilt (xiSpectralPoint q).im

theorem d4BMXiHelicitySexticJostCompletion_eq_ratio_of_tilted
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMXiHelicitySexticJostCompletion q =
      (d4BMXiTwoChannelHelicityTransfer q : ℂ) /
        d4ThetaHawkingChargeDecayNegativeJost 0 (xiSpectralPoint q) := by
  unfold d4BMXiHelicitySexticJostCompletion
  rw [d4ThetaHawkingHelicitySexticJostCompletionOfTilt_eq_ratio]
  · rw [d4ThetaHawkingTwoChannelHelicityNumeratorOfTilt_xi,
      d4ThetaHawkingSexticNegativeJost_eq]
  · intro hy
    apply hq
    rw [xiSpectralPoint_im_eq] at hy
    linarith

theorem d4BMXiHelicitySexticJostCompletion_ne_zero (q : XiZeroCopy) :
    d4BMXiHelicitySexticJostCompletion q ≠ 0 := by
  exact d4ThetaHawkingHelicitySexticJostCompletionOfTilt_ne_zero _
    (xiSpectralPoint_im_mem_open_half q).1
    (xiSpectralPoint_im_mem_open_half q).2

theorem d4BMXiHelicitySexticJostCompletion_eq_neg_sixteen_div_twentyFive_of_critical
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re = 1 / 2) :
    d4BMXiHelicitySexticJostCompletion q = -16 / 25 := by
  unfold d4BMXiHelicitySexticJostCompletion
  rw [show (xiSpectralPoint q).im = 0 by rw [xiSpectralPoint_im_eq]; linarith]
  exact d4ThetaHawkingHelicitySexticJostCompletionOfTilt_zero

end

end RHTower

