import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodFourthScaleElevenThirdsExactAtomLower

/-!
# Scale-free exact dominant fourth atom

The literal fourth likelihood score on the dominant mixed atom-ray has one formula at every
positive likelihood coordinate.  This module removes scale-chamber hypotheses from the repeated
integral computation and exposes the exact factor `exp (-3A)` times the rational ray polynomial.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Integrability of the fourth likelihood score against the complete higher spectral measure. -/
theorem integrable_thetaLikelihoodFourthScore_mul_exp_higher_general
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ => thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t)))
      thetaCuspHigherLikelihoodSpectralMeasure := by
  have h4 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 4 hB).const_mul (A ^ 4)
  have h3 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 3 hB).const_mul
      (6 * A ^ 3)
  have h2 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 2 hB).const_mul
      (7 * A ^ 2)
  have h1 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 1 hB).const_mul A
  convert (((h4.sub h3).add h2).sub h1) using 1
  funext t
  dsimp [thetaLikelihoodFourthScore]
  ring

/-- The complete fourth-score integral is the corresponding linear combination of raw moments. -/
theorem integral_thetaLikelihoodFourthScore_mul_exp_higher_eq_general
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ, thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t))
      ∂thetaCuspHigherLikelihoodSpectralMeasure) =
      A ^ 4 * thetaCuspHigherLikelihoodSpectralMoment B 4 -
        6 * A ^ 3 * thetaCuspHigherLikelihoodSpectralMoment B 3 +
        7 * A ^ 2 * thetaCuspHigherLikelihoodSpectralMoment B 2 -
        A * thetaCuspHigherLikelihoodSpectralMoment B 1 := by
  have h4 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 4 hB).const_mul (A ^ 4)
  have h3 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 3 hB).const_mul
      (6 * A ^ 3)
  have h2 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 2 hB).const_mul
      (7 * A ^ 2)
  have h1 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 1 hB).const_mul A
  let f4 : ℝ → ℝ := fun t => A ^ 4 * (t ^ 4 * Real.exp (-B * t))
  let f3 : ℝ → ℝ := fun t => (6 * A ^ 3) * (t ^ 3 * Real.exp (-B * t))
  let f2 : ℝ → ℝ := fun t => (7 * A ^ 2) * (t ^ 2 * Real.exp (-B * t))
  let f1 : ℝ → ℝ := fun t => A * (t ^ 1 * Real.exp (-B * t))
  rw [show (fun t : ℝ => thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t))) =
      ((f4 - f3) + f2) - f1 by
    funext t
    dsimp [thetaLikelihoodFourthScore, f4, f3, f2, f1]
    ring]
  rw [integral_sub' ((h4.sub h3).add h2) h1,
    integral_add' (h4.sub h3) h2, integral_sub' h4 h3]
  simp only [integral_const_mul]
  rw [← thetaCuspHigherLikelihoodSpectralMoment_eq_integral,
    ← thetaCuspHigherLikelihoodSpectralMoment_eq_integral,
    ← thetaCuspHigherLikelihoodSpectralMoment_eq_integral,
    ← thetaCuspHigherLikelihoodSpectralMoment_eq_integral]

/-- Scale-free exact evaluation of the literal dominant mixed atom-ray fourth score. -/
theorem integral_thetaLikelihoodFourthScore_dominantAtom_eq_exact
    {A B : ℝ} (hB : 0 < B) (hBA : B = A - 3 / 2) :
    (∫ t : ℝ, thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t))
        ∂thetaCuspAtomLikelihoodSpectralMeasure 2) =
      Real.exp (-(3 * A)) * thetaCuspLikelihoodFourthExactDominantPolynomial A B := by
  have hextract :
      Real.exp (-(9 / 2 : ℝ)) * Real.exp (-(3 * B)) = Real.exp (-(3 * A)) := by
    rw [← Real.exp_add]
    congr 1
    rw [hBA]
    ring
  have hMeasure : thetaCuspAtomLikelihoodSpectralMeasure 2 ≤
      thetaCuspHigherLikelihoodSpectralMeasure := by
    rw [thetaCuspHigherLikelihoodSpectralMeasure]
    simpa only [Nat.zero_add] using
      Measure.le_sum (fun k : ℕ => thetaCuspAtomLikelihoodSpectralMeasure (k + 2)) 0
  have h4 :=
    ((integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 4 hB).mono_measure
      hMeasure).const_mul (A ^ 4)
  have h3 :=
    ((integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 3 hB).mono_measure
      hMeasure).const_mul (6 * A ^ 3)
  have h2 :=
    ((integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 2 hB).mono_measure
      hMeasure).const_mul (7 * A ^ 2)
  have h1 :=
    ((integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 1 hB).mono_measure
      hMeasure).const_mul A
  let f4 : ℝ → ℝ := fun t => A ^ 4 * (t ^ 4 * Real.exp (-B * t))
  let f3 : ℝ → ℝ := fun t => (6 * A ^ 3) * (t ^ 3 * Real.exp (-B * t))
  let f2 : ℝ → ℝ := fun t => (7 * A ^ 2) * (t ^ 2 * Real.exp (-B * t))
  let f1 : ℝ → ℝ := fun t => A * (t ^ 1 * Real.exp (-B * t))
  rw [show (fun t : ℝ => thetaLikelihoodFourthScore (A * t) * Real.exp (-(B * t))) =
      ((f4 - f3) + f2) - f1 by
    funext t
    dsimp [thetaLikelihoodFourthScore, f4, f3, f2, f1]
    ring]
  rw [integral_sub' ((h4.sub h3).add h2) h1,
    integral_add' (h4.sub h3) h2, integral_sub' h4 h3]
  simp only [integral_const_mul]
  simp only [neg_mul]
  rw [integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure
      (n := 2) (by norm_num) 4 hB,
    integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure
      (n := 2) (by norm_num) 3 hB,
    integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure
      (n := 2) (by norm_num) 2 hB,
    integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure
      (n := 2) (by norm_num) 1 hB]
  norm_num [thetaCuspLikelihoodGap, Finset.sum_range_succ, Nat.factorial, Nat.choose]
  rw [show B * 3 = 3 * B by ring]
  rw [hextract]
  dsimp [thetaCuspLikelihoodFourthExactDominantPolynomial, thetaLikelihoodFourthScore]
  ring

end

end RHTower
