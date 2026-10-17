import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarSourceJumpDomain

/-! The actual narrow tent forces a logarithmic lower jump-energy cost. -/

open MeasureTheory Set Filter
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

theorem factorialSourceRight_autocorr_tail (n : ℕ) {x : ℝ}
    (hx : 2*sourceFactorialWidth (n+1) ≤ x) : autocorr (factorialSourceRight n) x = 0 := by
  unfold autocorr
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  change exponentialTentSource (sourceFactorialWidth (n+1)) u*
    exponentialTentSource (sourceFactorialWidth (n+1)) (u+x) = 0
  by_cases hu : u ≤ 0
  · simp [exponentialTentSource_eq, causalTent_zero_left _ hu]
  · have hv : 2*sourceFactorialWidth (n+1) ≤ u+x := by linarith
    simp [exponentialTentSource_eq, causalTent_zero_right _ hv]

theorem factorialSourceRight_jump_energy_lower (n : ℕ) :
    6*Real.exp (-(1/2 : ℝ))*((n+1 : ℕ) : ℝ)*Real.log ((n+1 : ℕ) : ℝ) ≤
      biScaleLevyEnergy (factorialSourceRight n) := by
  have hn : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n+1 by omega)
  have hnp : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  let a : ℝ := 1/((n+1 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := (div_le_iff₀ hnp).2 (by linarith)
  have hwidth : 2*sourceFactorialWidth (n+1) ≤ a := by
    have hh := (sourceFactorialWidth_bounds (by omega : 1 ≤ n+1)).2
    have hh' := (le_div_iff₀ (by positivity : 0 < 12*((n+1 : ℕ) : ℝ))).1 hh
    apply (le_div_iff₀ hnp).2
    nlinarith
  have hzero : 6*((n+1 : ℕ) : ℝ) ≤ autocorr (factorialSourceRight n) 0 := by
    rw [← integral_sq_eq_autocorr_zero]
    exact (factorialSourceRight_energy_bounds n).1
  have hci : ContinuousOn (fun x : ℝ => 1/x) (Icc a 1) :=
    continuousOn_const.div continuousOn_id (fun x hx => (ha.trans_le hx.1).ne')
  have hii : IntervalIntegrable (fun x : ℝ => 1/x) volume a 1 := hci.intervalIntegrable_of_Icc ha1
  have hi : IntervalIntegrable (fun x => (autocorr (factorialSourceRight n) 0-
      autocorr (factorialSourceRight n) x)*archLevySinhWeight x) volume a 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).2
      ((factorialSourceRight_jump_integrable n).mono_set (fun x hx => ha.trans hx.1))
  calc
    _ = ∫ x in a..1, (6*Real.exp (-(1/2 : ℝ))*((n+1 : ℕ) : ℝ))*(1/x) := by
      rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos ha (by norm_num)]
      dsimp [a]
      simp
    _ ≤ ∫ x in a..1, (autocorr (factorialSourceRight n) 0-
        autocorr (factorialSourceRight n) x)*archLevySinhWeight x := by
      apply intervalIntegral.integral_mono_on ha1 (hii.const_mul _) hi
      intro x hx
      have hxp : 0 < x := ha.trans_le hx.1
      rw [factorialSourceRight_autocorr_tail n (hwidth.trans hx.1), sub_zero]
      calc
        _ = (6*((n+1 : ℕ) : ℝ))*(Real.exp (-(1/2 : ℝ))/x) := by ring
        _ ≤ autocorr (factorialSourceRight n) 0*archLevySinhWeight x :=
          mul_le_mul hzero (exp_neg_half_div_le_archLevySinhWeight hxp hx.2)
            (by positivity) (by linarith)
    _ ≤ biScaleLevyEnergy (factorialSourceRight n) := by
      rw [intervalIntegral.integral_of_le ha1]
      apply setIntegral_mono_set (factorialSourceRight_jump_integrable n)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact mul_nonneg (autocorr_sub_nonneg (factorialSourceRight n).hasCompactSupport
          (factorialSourceRight n).continuous x) (archLevySinhWeight_pos hx).le
      · exact Eventually.of_forall fun x hx => ha.trans hx.1

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
