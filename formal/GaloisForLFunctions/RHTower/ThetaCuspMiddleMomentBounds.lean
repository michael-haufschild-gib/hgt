import GaloisForLFunctions.RHTower.ThetaCuspSecondAtomAllMoments

/-! # Complete spectral moment bounds on the middle scale -/
open MeasureTheory Filter Topology
namespace RHTower
noncomputable section

/-- The second atom inherits the lower spectral support edge three. -/
theorem ae_three_le_thetaCuspSecondAtomSpectralMeasure :
    ∀ᵐ t ∂thetaCuspSecondAtomSpectralMeasure, 3 ≤ t :=
  ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure.filter_mono
    (ae_mono thetaCuspSecondAtomSpectralMeasure_le)

/-- Increasing positive tilt decreases every second-atom moment. -/
theorem thetaCuspSecondAtomMoment_antitone (n : ℕ) {A B : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) :
    thetaCuspSecondAtomMoment B n ≤ thetaCuspSecondAtomMoment A n := by
  apply integral_mono_ae
    (integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure n (hA.trans_le hAB))
    (integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure n hA)
  filter_upwards [ae_nonneg_thetaCuspSecondAtomSpectralMeasure] with t ht
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht n)
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- A single order-ten endpoint controls all ten lower moments on the full tilt ray. -/
theorem thetaCuspSecondAtomMoment_le_middle {n : ℕ} (hn : n ≤ 10)
    {B : ℝ} (hB : 2 ≤ B) : thetaCuspSecondAtomMoment B n ≤ (3 : ℝ)^n/100 := by
  have hscaled : (3 : ℝ)^(10 : ℕ)*thetaCuspSecondAtomMoment 2 n ≤
      (3 : ℝ)^n*thetaCuspSecondAtomMoment 2 10 := by
    unfold thetaCuspSecondAtomMoment
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_mono_ae
      ((integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure n (by norm_num : (0 : ℝ) < 2)).const_mul _)
      ((integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure 10 (by norm_num : (0 : ℝ) < 2)).const_mul _)
    filter_upwards [ae_three_le_thetaCuspSecondAtomSpectralMeasure] with t ht
    have hp := pow_le_pow_right₀ (show (1 : ℝ) ≤ t/3 by linarith) hn
    rw [div_pow, div_pow] at hp
    have hp' : (3 : ℝ)^(10 : ℕ)*t^n ≤ (3 : ℝ)^n*t^(10 : ℕ) := by
      have := (div_le_div_iff₀ (by positivity : (0 : ℝ) < 3^n)
        (by norm_num : (0 : ℝ) < 3^(10 : ℕ))).mp hp
      nlinarith only [this]
    have he := mul_le_mul_of_nonneg_right hp' (Real.exp_pos (-2*t)).le
    nlinarith only [he]
  have hten := thetaCuspSecondAtomMoment_ten_at_two_le
  have hm := mul_le_mul_of_nonneg_left hten (by positivity : (0 : ℝ) ≤ 3^n)
  have hbase : thetaCuspSecondAtomMoment 2 n ≤ (3 : ℝ)^n/100 := by
    have hfinal := hscaled.trans hm
    norm_num at hfinal
    nlinarith only [hfinal]
  exact (thetaCuspSecondAtomMoment_antitone n (by norm_num : (0 : ℝ) < 2) hB).trans hbase

/-- The complete higher measure retains the second-atom bound plus the calibrated infinite tail. -/
theorem thetaCuspHigherLikelihoodSpectralMoment_le_middle {n : ℕ} (hn : n ≤ 10)
    {x : ℝ} (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) n ≤
      (3 : ℝ)^n/100+8^n*thetaCuspDeepTailErrorScale x := by
  have hc := thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hB : 2 ≤ thetaCuspLikelihoodCoordinate x := by linarith
  rw [thetaCuspHigherLikelihoodSpectralMoment_eq_second_add_deep (by linarith) n]
  have hs := thetaCuspSecondAtomMoment_le_middle hn hB
  have hnr : (n : ℝ) ≤ 10 := by exact_mod_cast hn
  have hd := thetaCuspDeepTailMoment_le_errorScale n (x := x) (by linarith)
  linarith

end
end RHTower
