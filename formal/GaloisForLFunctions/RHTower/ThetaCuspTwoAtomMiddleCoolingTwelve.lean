import GaloisForLFunctions.HTGeometry.LogarithmicLaplaceMiddleAbsoluteTwelve
import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomMiddleCooling
import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomExponentialAdmission

/-!
# Retained two-atom partition bounds through twelve

The exact second-atom spectral measure is separated before taking absolute
values. Its twelfth moment at the physical lower tilt controls all lower
moments. Consequently the retained-partition bound contains no deep-tail
contribution; every deep-tail contribution remains in its own error term.
-/
open MeasureTheory Filter Topology Polynomial
namespace RHTower
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
private def momentStep (n : ℕ) (P : ℝ[X]) := (C 3*X+C (n+1 : ℝ))*P-X*P.derivative
private theorem moment_succ (n : ℕ) : thetaCuspSecondMomentNumerator (n+1) = momentStep n (thetaCuspSecondMomentNumerator n) := rfl
private theorem second_numerator_twelve_bound : (thetaCuspSecondMomentNumerator 12).eval (11/5 : ℝ) ≤
    65000*3^(12 : ℕ)/100*(11/5 : ℝ)^(13 : ℕ) := by
  conv_lhs =>
    arg 2
    rw [moment_succ]
    conv =>
      arg 2
      rw [moment_succ]
      conv =>
        arg 2
        rw [moment_succ]
        conv =>
          arg 2
          rw [moment_succ]
          conv =>
            arg 2
            rw [moment_succ]
            conv =>
              arg 2
              rw [moment_succ]
              conv =>
                arg 2
                rw [moment_succ]
                conv =>
                  arg 2
                  rw [moment_succ]
                  conv =>
                    arg 2
                    rw [moment_succ]
                    conv =>
                      arg 2
                      rw [moment_succ]
                      conv =>
                        arg 2
                        rw [moment_succ]
                        conv =>
                          arg 2
                          rw [moment_succ]
                          conv =>
                            arg 2
                            rw [thetaCuspSecondMomentNumerator]
                          unfold momentStep
                          simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
                            derivative_neg,derivative_pow,C_ofNat]
                          ring_nf
                        unfold momentStep
                        simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
                          derivative_neg,derivative_pow,C_ofNat]
                        ring_nf
                      unfold momentStep
                      simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
                        derivative_neg,derivative_pow,C_ofNat]
                      ring_nf
                    unfold momentStep
                    simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
                      derivative_neg,derivative_pow,C_ofNat]
                    ring_nf
                  unfold momentStep
                  simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
                    derivative_neg,derivative_pow,C_ofNat]
                  ring_nf
                unfold momentStep
                simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
                  derivative_neg,derivative_pow,C_ofNat]
                ring_nf
              unfold momentStep
              simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
                derivative_neg,derivative_pow,C_ofNat]
              ring_nf
            unfold momentStep
            simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
              derivative_neg,derivative_pow,C_ofNat]
            ring_nf
          unfold momentStep
          simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
            derivative_neg,derivative_pow,C_ofNat]
          ring_nf
        unfold momentStep
        simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
          derivative_neg,derivative_pow,C_ofNat]
        ring_nf
      unfold momentStep
      simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
        derivative_neg,derivative_pow,C_ofNat]
      ring_nf
    unfold momentStep
    simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
      derivative_neg,derivative_pow,C_ofNat]
    ring_nf
  norm_num

/-- The physical lower tilt admits the twelfth second-atom moment with the same coefficient. -/
theorem thetaCuspSecondAtomMoment_twelve_at_eleven_fifths_le :
    thetaCuspSecondAtomMoment (11/5) 12 ≤ (3 : ℝ)^(12 : ℕ)/100 := by
  rw [thetaCuspSecondAtomMoment_eq_allOrderProfile 12 (by norm_num)]
  unfold thetaCuspSecondMomentProfile
  have hn : (thetaCuspSecondMomentNumerator 12).eval (11/5)/(11/5 : ℝ)^(13 : ℕ) ≤
      65000*3^(12 : ℕ)/100 := by
    have h := second_numerator_twelve_bound
    norm_num at h ⊢
    linarith only [h]
  have he := thetaCuspTwoAtom_lower_envelope_admission (q:=37/10) le_rfl
  norm_num [HTGeometry.twoAtomLowerEnvelope] at he
  have hmul := mul_le_mul_of_nonneg_left hn (Real.exp_pos (-(111/10 : ℝ))).le
  have heq : Real.exp (-(9/2 : ℝ))*(Real.exp (-3*(11/5))*
      (thetaCuspSecondMomentNumerator 12).eval (11/5)/(11/5)^(13 : ℕ)) =
      Real.exp (-(111/10 : ℝ))*((thetaCuspSecondMomentNumerator 12).eval (11/5)/(11/5)^(13 : ℕ)) := by
    rw [show -(111/10 : ℝ) = -(9/2)+(-3*(11/5)) by norm_num,Real.exp_add]
    ring
  rw [heq]
  nlinarith only [hmul,he]

/-- The support edge transfers the physical twelfth-moment bound to every required order. -/
theorem thetaCuspSecondAtomMoment_le_middle_twelve {n : ℕ} (hn : n ≤ 12)
    {B : ℝ} (hB : 11/5 ≤ B) : thetaCuspSecondAtomMoment B n ≤ (3 : ℝ)^n/100 := by
  have hscaled : (3 : ℝ)^(12 : ℕ)*thetaCuspSecondAtomMoment (11/5) n ≤
      (3 : ℝ)^n*thetaCuspSecondAtomMoment (11/5) 12 := by
    unfold thetaCuspSecondAtomMoment
    rw [← integral_const_mul,← integral_const_mul]
    apply integral_mono_ae
      ((integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure n (by norm_num : (0 : ℝ) < 11/5)).const_mul _)
      ((integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure 12 (by norm_num : (0 : ℝ) < 11/5)).const_mul _)
    filter_upwards [ae_three_le_thetaCuspSecondAtomSpectralMeasure] with t ht
    have hp := pow_le_pow_right₀ (show (1 : ℝ) ≤ t/3 by linarith) hn
    rw [div_pow,div_pow] at hp
    have hp' : (3 : ℝ)^(12 : ℕ)*t^n ≤ (3 : ℝ)^n*t^(12 : ℕ) := by
      have h := (div_le_div_iff₀ (by positivity : (0 : ℝ) < 3^n)
        (by norm_num : (0 : ℝ) < 3^(12 : ℕ))).mp hp
      nlinarith only [h]
    have he := mul_le_mul_of_nonneg_right hp' (Real.exp_pos (-(11/5)*t)).le
    nlinarith only [he]
  have hm := mul_le_mul_of_nonneg_left thetaCuspSecondAtomMoment_twelve_at_eleven_fifths_le
    (by positivity : (0 : ℝ) ≤ 3^n)
  have hbase : thetaCuspSecondAtomMoment (11/5) n ≤ (3 : ℝ)^n/100 := by
    have h := hscaled.trans hm
    norm_num at h
    nlinarith only [h]
  exact (thetaCuspSecondAtomMoment_antitone n (by norm_num : (0 : ℝ) < 11/5) hB).trans hbase

/-- The retained partition is exactly the second-atom integral before taking absolute values. -/
theorem iteratedDeriv_thetaCuspTwoAtomLikelihoodPartition_eq_second_integral
    (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n thetaCuspTwoAtomLikelihoodPartition x = (0 : ℝ)^n+
      ∫ t : ℝ, HTGeometry.laplaceCoolingJet n 0
        (thetaCuspSingleAtomReflectionScale 1 x*t)*Real.exp (-thetaCuspLikelihoodCoordinate x*t)
        ∂thetaCuspSecondAtomSpectralMeasure := by
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  have hs := (integrable_laplaceCoolingJet_mul_exp_higher n 0 hB).mono_measure
    thetaCuspSecondAtomSpectralMeasure_le
  have hd := integrable_laplaceCoolingJet_mul_exp_deep n 0 hB
  rw [iteratedDeriv_thetaCuspTwoAtomLikelihoodPartition_eq n hx,
    iteratedDeriv_thetaCuspLikelihoodSourceRemainder n hx,
    iteratedDeriv_thetaCuspDeepLikelihoodRemainder n hx,
    thetaCuspCoolingJet_eq_integral_score n 0 hB,
    thetaCuspDeepCoolingJet_eq_integral_score n 0 hB,
    thetaCuspHigherLikelihoodSpectralMeasure_eq_second_add_deep,
    integral_add_measure hs hd]
  ring

/-- Through derivative twelve, the retained partition has no artificial deep-tail term. -/
theorem abs_iteratedDeriv_thetaCuspTwoAtomLikelihoodPartition_le_middle_twelve
    {n : ℕ} (hn : n ≤ 12) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |iteratedDeriv n thetaCuspTwoAtomLikelihoodPartition x| ≤
      (0 : ℝ)^n+(6*thetaCuspSingleAtomReflectionScale 1 x)^n/100 := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  have hBq : 11/5 ≤ thetaCuspLikelihoodCoordinate x := by
    have h := thetaCuspSingleAtomScale_likelihoodCoordinate x
    linarith
  have hqp : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hs := (integrable_laplaceCoolingJet_mul_exp_higher n 0 hB).mono_measure
    thetaCuspSecondAtomSpectralMeasure_le
  rw [iteratedDeriv_thetaCuspTwoAtomLikelihoodPartition_eq_second_integral n hx]
  apply (abs_add_le _ _).trans
  rw [abs_of_nonneg (pow_nonneg (le_refl (0 : ℝ)) n)]
  refine add_le_add le_rfl ?_
  calc
    _ ≤ ∫ t : ℝ, |HTGeometry.laplaceCoolingJet n 0
        (thetaCuspSingleAtomReflectionScale 1 x*t)*Real.exp (-thetaCuspLikelihoodCoordinate x*t)|
        ∂thetaCuspSecondAtomSpectralMeasure := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun t : ℝ => HTGeometry.laplaceCoolingJet n 0
          (thetaCuspSingleAtomReflectionScale 1 x*t)*Real.exp (-thetaCuspLikelihoodCoordinate x*t))
    _ ≤ (2*thetaCuspSingleAtomReflectionScale 1 x)^n*
        thetaCuspSecondAtomMoment (thetaCuspLikelihoodCoordinate x) n := by
      rw [thetaCuspSecondAtomMoment,← integral_const_mul]
      apply integral_mono_ae (by simpa only [Real.norm_eq_abs] using hs.norm)
        ((integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure n hB).const_mul _)
      filter_upwards [ae_three_le_thetaCuspSecondAtomSpectralMeasure] with t ht
      have hqt : 111/10 ≤ thetaCuspSingleAtomReflectionScale 1 x*t := by nlinarith
      have hb := HTGeometry.laplaceCoolingJet_abs_le_of_middle_twelve hn hqt
      rw [abs_mul,abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ (2*(thetaCuspSingleAtomReflectionScale 1 x*t))^n*
            Real.exp (-thetaCuspLikelihoodCoordinate x*t) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
        _ = _ := by simp only [mul_pow]; ring
    _ ≤ (2*thetaCuspSingleAtomReflectionScale 1 x)^n*((3 : ℝ)^n/100) :=
      mul_le_mul_of_nonneg_left (thetaCuspSecondAtomMoment_le_middle_twelve hn hBq) (by positivity)
    _ = _ := by
      have h6 : (6*thetaCuspSingleAtomReflectionScale 1 x)^n =
          (2*thetaCuspSingleAtomReflectionScale 1 x)^n*3^n := by
        rw [← mul_pow]
        congr 1
        ring
      rw [h6]
      ring

end
end RHTower
