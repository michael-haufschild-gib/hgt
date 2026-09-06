import GaloisForLFunctions.HTGeometry.RankThreeHankelMixture
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthGlobal
import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedFourPointOddParityCusp

/-! # Strict rank-three curvature of the literal center mixture -/
open MeasureTheory Set
namespace RHTower
noncomputable section

theorem iteratedDeriv_seven_thetaCuspCenterMixedDensity
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    iteratedDeriv 7 (thetaCuspCenterMixedDensity a) =
      thetaCuspCenterMixedDensitySeventhJet a := by
  rw [show (7 : ℕ) = 6+1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_six_thetaCuspCenterMixedDensity ha0 ha]
  funext t
  exact (hasDerivAt_thetaCuspCenterMixedDensitySixthJet ha0 ha t).deriv

theorem iteratedDeriv_eight_thetaCuspCenterMixedDensity
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    iteratedDeriv 8 (thetaCuspCenterMixedDensity a) =
      thetaCuspCenterMixedDensityEighthJet a := by
  rw [show (8 : ℕ) = 7+1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_seven_thetaCuspCenterMixedDensity ha0 ha]
  funext t
  exact (hasDerivAt_thetaCuspCenterMixedDensitySeventhJet ha0 ha t).deriv

/-- Eighth reflected jet of one literal source fibre. -/
def thetaCuspSourceReflectionJetEight (x : ℝ) : ℝ :=
  HilbertMetric.reflectedProductEighthJet
    (iteratedDeriv 0 thetaCuspFullSource x) (iteratedDeriv 1 thetaCuspFullSource x)
    (iteratedDeriv 2 thetaCuspFullSource x) (iteratedDeriv 3 thetaCuspFullSource x)
    (iteratedDeriv 4 thetaCuspFullSource x) (iteratedDeriv 5 thetaCuspFullSource x)
    (iteratedDeriv 6 thetaCuspFullSource x) (iteratedDeriv 7 thetaCuspFullSource x)
    (iteratedDeriv 8 thetaCuspFullSource x)

/-- Eighth reflected jet with the complete positive center-mixture weight. -/
def thetaCuspCenterMixedReflectionJetEightIntegrand (a r : ℝ) : ℝ :=
  r * Real.sinh (a*r) * thetaCuspSourceReflectionJetEight (r/2)

private theorem eightIntegrand_eq_products (a r : ℝ) :
    thetaCuspCenterMixedReflectionJetEightIntegrand a r =
      2 * thetaCuspCenterMixedDerivativeProduct 8 0 a r 0 -
      16 * thetaCuspCenterMixedDerivativeProduct 7 1 a r 0 +
      56 * thetaCuspCenterMixedDerivativeProduct 6 2 a r 0 -
      112 * thetaCuspCenterMixedDerivativeProduct 5 3 a r 0 +
      70 * thetaCuspCenterMixedDerivativeProduct 4 4 a r 0 := by
  unfold thetaCuspCenterMixedReflectionJetEightIntegrand thetaCuspSourceReflectionJetEight
    thetaCuspCenterMixedDerivativeProduct HilbertMetric.reflectedProductEighthJet
  simp only [add_zero, sub_zero, iteratedDeriv_zero]
  ring

theorem integrableOn_thetaCuspCenterMixedReflectionJetEightIntegrand
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    IntegrableOn (thetaCuspCenterMixedReflectionJetEightIntegrand a) (Ioi 0) := by
  have h80 := integrable_thetaCuspCenterMixedDerivativeProduct (t:=0) ha0 ha 8 0
  have h71 := integrable_thetaCuspCenterMixedDerivativeProduct (t:=0) ha0 ha 7 1
  have h62 := integrable_thetaCuspCenterMixedDerivativeProduct (t:=0) ha0 ha 6 2
  have h53 := integrable_thetaCuspCenterMixedDerivativeProduct (t:=0) ha0 ha 5 3
  have h44 := integrable_thetaCuspCenterMixedDerivativeProduct (t:=0) ha0 ha 4 4
  exact (((((h80.const_mul 2).sub (h71.const_mul 16)).add
    (h62.const_mul 56)).sub (h53.const_mul 112)).add (h44.const_mul 70)).congr
      (ae_of_all _ fun r => (eightIntegrand_eq_products a r).symm)

theorem integral_thetaCuspCenterMixedReflectionJetEightIntegrand
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    (∫ r : ℝ in Ioi 0, thetaCuspCenterMixedReflectionJetEightIntegrand a r) =
      thetaCuspCenterMixedDensityEighthJet a 0 := by
  have h80 := integrable_thetaCuspCenterMixedDerivativeProduct (t:=0) ha0 ha 8 0
  have h71 := integrable_thetaCuspCenterMixedDerivativeProduct (t:=0) ha0 ha 7 1
  have h62 := integrable_thetaCuspCenterMixedDerivativeProduct (t:=0) ha0 ha 6 2
  have h53 := integrable_thetaCuspCenterMixedDerivativeProduct (t:=0) ha0 ha 5 3
  have h44 := integrable_thetaCuspCenterMixedDerivativeProduct (t:=0) ha0 ha 4 4
  dsimp only [IntegrableOn] at h80 h71 h62 h53 h44
  simp_rw [eightIntegrand_eq_products]
  rw [integral_add, integral_sub, integral_add, integral_sub] <;> try fun_prop
  simp only [integral_const_mul]
  change 2 * thetaCuspCenterMixedDerivativeProductIntegral 8 0 a 0 -
    16 * thetaCuspCenterMixedDerivativeProductIntegral 7 1 a 0 +
    56 * thetaCuspCenterMixedDerivativeProductIntegral 6 2 a 0 -
    112 * thetaCuspCenterMixedDerivativeProductIntegral 5 3 a 0 +
    70 * thetaCuspCenterMixedDerivativeProductIntegral 4 4 a 0 = _
  unfold thetaCuspCenterMixedDensityEighthJet
  rw [thetaCuspCenterMixedDerivativeProductIntegral_zero_comm 0 8,
    thetaCuspCenterMixedDerivativeProductIntegral_zero_comm 1 7,
    thetaCuspCenterMixedDerivativeProductIntegral_zero_comm 2 6,
    thetaCuspCenterMixedDerivativeProductIntegral_zero_comm 3 5]
  ring

/-- The full rank-three Hankel determinant of the actual center mixture is strictly positive. -/
theorem thetaCuspCenterMixedDensity_eighthHankel_pos
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    0 < HilbertMetric.signedEvenHankelThreeDet
      (thetaCuspCenterMixedDensity a 0) (thetaCuspCenterMixedDensitySecondJet a 0)
      (thetaCuspCenterMixedDensityFourthJet a 0) (thetaCuspCenterMixedDensitySixthJet a 0)
      (thetaCuspCenterMixedDensityEighthJet a 0) := by
  let p0 := thetaCuspCenterMixedReflectionJetZeroIntegrand a
  let p2 := thetaCuspCenterMixedReflectionJetTwoIntegrand a
  let p4 := thetaCuspCenterMixedReflectionJetFourIntegrand a
  let p6 := thetaCuspCenterMixedReflectionJetSixIntegrand a
  let p8 := thetaCuspCenterMixedReflectionJetEightIntegrand a
  have hp0eq : p0 = fun r => thetaCuspCenterMixedDerivativeProduct 0 0 a r 0 := by
    funext r
    dsimp only [p0, thetaCuspCenterMixedReflectionJetZeroIntegrand,
      thetaCuspSourceReflectionJetZero,thetaCuspCenterMixedDerivativeProduct]
    simp only [iteratedDeriv_zero,add_zero,sub_zero]
    ring
  have hI0 : IntegrableOn p0 (Ioi 0) := by
    rw [hp0eq]
    exact integrable_thetaCuspCenterMixedDerivativeProduct ha0.le ha 0 0
  have hI2 := integrableOn_thetaCuspCenterMixedReflectionJetTwoIntegrand ha0.le ha
  have hI4 := integrableOn_thetaCuspCenterMixedReflectionJetFourIntegrand ha0.le ha
  have hI6 := integrableOn_thetaCuspCenterMixedReflectionJetSixIntegrand ha0.le ha
  have hI8 := integrableOn_thetaCuspCenterMixedReflectionJetEightIntegrand ha0.le ha
  have hI0value : (∫ r : ℝ in Ioi 0, p0 r) = thetaCuspCenterMixedDensity a 0 := by
    rw [hp0eq]
    unfold thetaCuspCenterMixedDerivativeProduct thetaCuspCenterMixedDensity
    simp only [iteratedDeriv_zero,add_zero,sub_zero]
  have hmass : 0 < ∫ r : ℝ in Ioi 0, p0 r := by
    rw [hI0value]
    exact thetaCuspCenterMixedDensity_pos ha0 ha 0
  have hpoint : ∀ᵐ r : ℝ ∂volume.restrict (Ioi 0),
      0 < p0 r ∧ 0 < p0 r*p4 r-p2 r^2 ∧
        0 < HilbertMetric.signedEvenHankelThreeDet (p0 r) (p2 r) (p4 r) (p6 r) (p8 r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hweight : 0 < r * Real.sinh (a*r) :=
      mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha0 hr))
    have hp0 : 0 < thetaCuspSourceReflectionJetZero (r/2) := by
      unfold thetaCuspSourceReflectionJetZero
      exact sq_pos_of_pos (thetaCuspFullSource_pos_of_pos (half_pos hr))
    have hhead := thetaCuspSourceReflectionFourthHankel_pos (x:=r/2) (half_pos hr)
    have hnative := thetaCuspFullReflectionEighthHankelCurvature_pos_on_nonnegative
      (r/2) (half_pos hr).le
    have hs := thetaCuspFullSource_pos_of_pos (half_pos hr)
    have hraw : 0 < thetaCuspFullSourceReflectionEighthHankelCurvature (r/2) := by
      rw [thetaCuspFullSourceReflectionEighthHankelCurvature_eq_fullReflection (half_pos hr)]
      exact mul_pos (by positivity) hnative
    refine ⟨mul_pos hweight hp0, ?_, ?_⟩
    · change 0 < (r * Real.sinh (a*r) * thetaCuspSourceReflectionJetZero (r/2)) *
          (r * Real.sinh (a*r) * thetaCuspSourceReflectionJetFour (r/2)) -
          (r * Real.sinh (a*r) * thetaCuspSourceReflectionJetTwo (r/2))^2
      have h := mul_pos (sq_pos_of_pos hweight) hhead
      nlinarith only [h]
    · have heq : HilbertMetric.signedEvenHankelThreeDet
          (p0 r) (p2 r) (p4 r) (p6 r) (p8 r) =
        (r * Real.sinh (a*r))^3 * thetaCuspFullSourceReflectionEighthHankelCurvature (r/2) := by
        dsimp only [p0,p2,p4,p6,p8,thetaCuspCenterMixedReflectionJetZeroIntegrand,
          thetaCuspCenterMixedReflectionJetTwoIntegrand,thetaCuspCenterMixedReflectionJetFourIntegrand,
          thetaCuspCenterMixedReflectionJetSixIntegrand,thetaCuspCenterMixedReflectionJetEightIntegrand,
          thetaCuspFullSourceReflectionEighthHankelCurvature,thetaCuspSourceReflectionJetZero,
          thetaCuspSourceReflectionJetTwo,thetaCuspSourceReflectionJetFour,
          thetaCuspSourceReflectionJetSix,thetaCuspSourceReflectionJetEight,
          HilbertMetric.signedEvenHankelThreeDet,HilbertMetric.reflectedProductSecondJet,
          HilbertMetric.reflectedProductFourthJet]
        simp only [iteratedDeriv_zero]
        ring
      rw [heq]
      exact mul_pos (pow_pos hweight 3) hraw
  have h := GaloisForLFunctions.HTGeometry.integral_threeByThree_det_pos
    p0 p2 p4 p6 p8 hI0 hI2 hI4 hI6 hI8 hmass hpoint
  rw [hI0value] at h
  dsimp only [p2,p4,p6,p8] at h
  rw [integral_thetaCuspCenterMixedReflectionJetTwoIntegrand ha0.le ha,
    integral_thetaCuspCenterMixedReflectionJetFourIntegrand ha0.le ha,
    integral_thetaCuspCenterMixedReflectionJetSixIntegrand ha0.le ha,
    integral_thetaCuspCenterMixedReflectionJetEightIntegrand ha0.le ha] at h
  exact h

/-- All five entries are the actual derivatives of the literal center-mixed density. -/
theorem thetaCuspCenterMixedDensity_iteratedDeriv_eighthHankel_pos
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    0 < HilbertMetric.signedEvenHankelThreeDet
      (thetaCuspCenterMixedDensity a 0)
      (iteratedDeriv 2 (thetaCuspCenterMixedDensity a) 0)
      (iteratedDeriv 4 (thetaCuspCenterMixedDensity a) 0)
      (iteratedDeriv 6 (thetaCuspCenterMixedDensity a) 0)
      (iteratedDeriv 8 (thetaCuspCenterMixedDensity a) 0) := by
  rw [iteratedDeriv_two_thetaCuspCenterMixedDensity ha0.le ha,
    iteratedDeriv_four_thetaCuspCenterMixedDensity ha0.le ha,
    iteratedDeriv_six_thetaCuspCenterMixedDensity ha0.le ha,
    iteratedDeriv_eight_thetaCuspCenterMixedDensity ha0.le ha]
  exact thetaCuspCenterMixedDensity_eighthHankel_pos ha0 ha

end
end RHTower
