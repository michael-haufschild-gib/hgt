import GaloisForLFunctions.HTGeometry.LogarithmicLaplaceScoreBounds
import GaloisForLFunctions.RHTower.ThetaCuspEffectiveLikelihoodCooling

/-!
# Sharp signed cooling through order ten on physical scale at least seven

The complete positive higher-likelihood measure carries the exact scalar score.
Retaining its alternating coefficients before integration gives the leading
monomial bound, replacing the triangle-inequality factor eight by six.
-/
open MeasureTheory Filter Topology
namespace RHTower
noncomputable section

/-- Every finite scalar cooling score is integrable against the full tilted higher measure. -/
theorem integrable_laplaceCoolingJet_mul_exp_higher (n m : ℕ) {x : ℝ}
    (hB : 0 < thetaCuspLikelihoodCoordinate x) :
    Integrable (fun t : ℝ => HTGeometry.laplaceCoolingJet n m
      (thetaCuspSingleAtomReflectionScale 1 x*t)*Real.exp (-thetaCuspLikelihoodCoordinate x*t))
      thetaCuspHigherLikelihoodSpectralMeasure := by
  induction n generalizing m with
  | zero =>
    have h := (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure m hB).const_mul
      (thetaCuspSingleAtomReflectionScale 1 x^m)
    apply h.congr
    filter_upwards with t
    simp only [HTGeometry.laplaceCoolingJet, mul_pow]
    ring
  | succ n ih =>
    apply (((ih m).const_mul (2*(m : ℝ))).sub ((ih (m+1)).const_mul 2)).congr
    filter_upwards with t
    simp only [HTGeometry.laplaceCoolingJet, Pi.sub_apply]
    ring

/-- The actual derivative recurrence is the integral of the exact scalar score. -/
theorem thetaCuspCoolingJet_eq_integral_score (n m : ℕ) {x : ℝ}
    (hB : 0 < thetaCuspLikelihoodCoordinate x) :
    thetaCuspCoolingJet n m x =
      ∫ t : ℝ, HTGeometry.laplaceCoolingJet n m
        (thetaCuspSingleAtomReflectionScale 1 x*t)*Real.exp (-thetaCuspLikelihoodCoordinate x*t)
        ∂thetaCuspHigherLikelihoodSpectralMeasure := by
  induction n generalizing m with
  | zero =>
    rw [thetaCuspCoolingJet, thetaCuspCoolingMoment,
      thetaCuspHigherLikelihoodSpectralMoment_eq_integral, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    simp only [HTGeometry.laplaceCoolingJet, mul_pow]
    ring
  | succ n ih =>
    rw [thetaCuspCoolingJet, ih m, ih (m+1), ← integral_const_mul, ← integral_const_mul,
      ← integral_sub ((integrable_laplaceCoolingJet_mul_exp_higher n m hB).const_mul _)
        ((integrable_laplaceCoolingJet_mul_exp_higher n (m+1) hB).const_mul _)]
    apply integral_congr_ae
    filter_upwards with t
    simp only [HTGeometry.laplaceCoolingJet, Pi.sub_apply]
    ring

/-- Signed finite cooling preserves positivity and is bounded by the leading spectral moment. -/
theorem thetaCuspCoolingJet_signed_le_leadingMoment {n : ℕ} (hn : n ≤ 10) {x : ℝ}
    (hq : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 ≤ (-1 : ℝ)^n*thetaCuspCoolingJet n 0 x ∧
    (-1 : ℝ)^n*thetaCuspCoolingJet n 0 x ≤
      (2*thetaCuspSingleAtomReflectionScale 1 x)^n *
        thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) n := by
  have hx := regimeOne_pos_of_six_le hq
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hs := integrable_laplaceCoolingJet_mul_exp_higher n 0 hB
  rw [thetaCuspCoolingJet_eq_integral_score n 0 hB, ← integral_const_mul]
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure] with t ht
    have hqt : 18 ≤ q*t := by nlinarith
    have hb := (HTGeometry.laplaceCoolingJet_signed_bounds hn hqt).1
    have hm := mul_nonneg hb (Real.exp_pos (-thetaCuspLikelihoodCoordinate x*t)).le
    change 0 ≤ (-1 : ℝ)^n*(HTGeometry.laplaceCoolingJet n 0 (q*t)*
      Real.exp (-thetaCuspLikelihoodCoordinate x*t))
    nlinarith only [hm]
  · rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral, ← integral_const_mul]
    apply integral_mono_ae (hs.const_mul _)
      ((integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure n hB).const_mul _)
    filter_upwards [ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure] with t ht
    have hqt : 18 ≤ q*t := by nlinarith
    have hb := (HTGeometry.laplaceCoolingJet_signed_bounds hn hqt).2
    have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-thetaCuspLikelihoodCoordinate x*t)).le
    change (-1 : ℝ)^n*(HTGeometry.laplaceCoolingJet n 0 (q*t)*
      Real.exp (-thetaCuspLikelihoodCoordinate x*t)) ≤
      (2*q)^n*(t^n*Real.exp (-thetaCuspLikelihoodCoordinate x*t))
    calc
      _ ≤ (2*(q*t))^n*Real.exp (-thetaCuspLikelihoodCoordinate x*t) := by nlinarith only [hm]
      _ = _ := by simp only [mul_pow]; ring

/-- Every required higher-likelihood derivative has its sharp leading-scale ceiling. -/
theorem thetaCuspLikelihoodSourceRemainder_signed_bounds_of_seven_le
    {n : ℕ} (hn : n ≤ 10) {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 ≤ (-1 : ℝ)^n*iteratedDeriv n thetaCuspLikelihoodSourceRemainder x ∧
    (-1 : ℝ)^n*iteratedDeriv n thetaCuspLikelihoodSourceRemainder x ≤
      (6*thetaCuspSingleAtomReflectionScale 1 x)^n*regimeOneLikelihoodScale x := by
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  rw [iteratedDeriv_thetaCuspLikelihoodSourceRemainder n hx]
  have h := thetaCuspCoolingJet_signed_le_leadingMoment hn (x := x) (by linarith)
  refine ⟨h.1, h.2.trans ?_⟩
  have hnr : (n : ℝ) ≤ 10 := by exact_mod_cast hn
  have hδ : (n : ℝ)/3 ≤ thetaCuspSingleAtomReflectionScale 1 x-Real.pi := by
    linarith [Real.pi_lt_d2]
  have hb := thetaCuspHigherLikelihoodSpectralMoment_le_explicitScale n hδ
  have hqp : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  calc
    (2*thetaCuspSingleAtomReflectionScale 1 x)^n*
        thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) n ≤
      (2*thetaCuspSingleAtomReflectionScale 1 x)^n*(3^n*regimeOneLikelihoodScale x) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (6*thetaCuspSingleAtomReflectionScale 1 x)^n*regimeOneLikelihoodScale x := by
      rw [← mul_assoc, ← mul_pow]
      congr 2
      ring

/-- Absolute finite derivative errors retain factor six on the full scale-seven ray. -/
theorem abs_iteratedDeriv_thetaCuspLikelihoodSourceRemainder_le_six_scale
    {n : ℕ} (hn : n ≤ 10) {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |iteratedDeriv n thetaCuspLikelihoodSourceRemainder x| ≤
      (6*thetaCuspSingleAtomReflectionScale 1 x)^n*regimeOneLikelihoodScale x := by
  have h := thetaCuspLikelihoodSourceRemainder_signed_bounds_of_seven_le hn hq
  have heq : |iteratedDeriv n thetaCuspLikelihoodSourceRemainder x| =
      (-1 : ℝ)^n*iteratedDeriv n thetaCuspLikelihoodSourceRemainder x := by
    rw [← abs_of_nonneg h.1, abs_mul, abs_pow]
    norm_num
  rw [heq]
  exact h.2

end
end RHTower
