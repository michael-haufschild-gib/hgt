import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionSixthGlobal
import GaloisForLFunctions.RHTower.HedenmalmCenterMixedRaywiseCoalescedCone

/-!
# Center-mixed sixth Hankel closure

Transfers global strict second--sixth reflected-source curvature through the physical
center mixture.  The signed jets form a pointwise positive-definite two-by-two field;
strict determinant positivity is preserved by integration.  This closes the TCD C1
center-mixed sixth Hankel burden for every aperture \(0 < a < 1/2\).
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Sixth center jet of one reflected complete-source fibre. -/
def thetaCuspSourceReflectionJetSix (x : ℝ) : ℝ :=
  HilbertMetric.reflectedProductSixthJet
    (iteratedDeriv 0 thetaCuspFullSource x)
    (iteratedDeriv 1 thetaCuspFullSource x)
    (iteratedDeriv 2 thetaCuspFullSource x)
    (iteratedDeriv 3 thetaCuspFullSource x)
    (iteratedDeriv 4 thetaCuspFullSource x)
    (iteratedDeriv 5 thetaCuspFullSource x)
    (iteratedDeriv 6 thetaCuspFullSource x)

/-- Weighted sixth reflected-source jet in the center mixture. -/
def thetaCuspCenterMixedReflectionJetSixIntegrand (a r : ℝ) : ℝ :=
  r * Real.sinh (a * r) * thetaCuspSourceReflectionJetSix (r / 2)

theorem integrableOn_thetaCuspCenterMixedReflectionJetSixIntegrand
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    IntegrableOn (thetaCuspCenterMixedReflectionJetSixIntegrand a) (Ioi 0) := by
  have h60 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 6 0
  have h51 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 5 1
  have h42 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 4 2
  have h33 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 3 3
  have h24 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 2 4
  have h15 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 1 5
  have h06 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 0 6
  have hcomb := ((((((h60.sub (h51.const_mul 6)).add (h42.const_mul 15)).sub
    (h33.const_mul 20)).add (h24.const_mul 15)).sub (h15.const_mul 6)).add h06)
  exact hcomb.congr (ae_of_all _ fun r => by
    unfold thetaCuspCenterMixedReflectionJetSixIntegrand
      thetaCuspSourceReflectionJetSix thetaCuspCenterMixedDerivativeProduct
      HilbertMetric.reflectedProductSixthJet
    simp only [add_zero, sub_zero, iteratedDeriv_zero, Pi.add_apply, Pi.sub_apply]
    ring)

theorem integral_thetaCuspCenterMixedReflectionJetSixIntegrand
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    (∫ r : ℝ in Ioi 0, thetaCuspCenterMixedReflectionJetSixIntegrand a r) =
      thetaCuspCenterMixedDensitySixthJet a 0 := by
  have h60 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 6 0
  have h51 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 5 1
  have h42 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 4 2
  have h33 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 3 3
  have h24 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 2 4
  have h15 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 1 5
  have h06 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 0 6
  have h51s := h51.const_mul 6
  have h42s := h42.const_mul 15
  have h33s := h33.const_mul 20
  have h24s := h24.const_mul 15
  have h15s := h15.const_mul 6
  have h1 := h60.sub h51s
  have h2 := h1.add h42s
  have h3 := h2.sub h33s
  have h4 := h3.add h24s
  have h5 := h4.sub h15s
  have hi1 :
      (∫ r : ℝ in Ioi 0,
        thetaCuspCenterMixedDerivativeProduct 6 0 a r 0 -
          6 * thetaCuspCenterMixedDerivativeProduct 5 1 a r 0) =
        (∫ r : ℝ in Ioi 0, thetaCuspCenterMixedDerivativeProduct 6 0 a r 0) -
          ∫ r : ℝ in Ioi 0, 6 * thetaCuspCenterMixedDerivativeProduct 5 1 a r 0 :=
    integral_sub h60 h51s
  have hi2 :
      (∫ r : ℝ in Ioi 0,
        (thetaCuspCenterMixedDerivativeProduct 6 0 a r 0 -
          6 * thetaCuspCenterMixedDerivativeProduct 5 1 a r 0) +
            15 * thetaCuspCenterMixedDerivativeProduct 4 2 a r 0) =
        (∫ r : ℝ in Ioi 0,
          thetaCuspCenterMixedDerivativeProduct 6 0 a r 0 -
            6 * thetaCuspCenterMixedDerivativeProduct 5 1 a r 0) +
          ∫ r : ℝ in Ioi 0, 15 * thetaCuspCenterMixedDerivativeProduct 4 2 a r 0 :=
    integral_add h1 h42s
  have hi3 :
      (∫ r : ℝ in Ioi 0,
        ((thetaCuspCenterMixedDerivativeProduct 6 0 a r 0 -
          6 * thetaCuspCenterMixedDerivativeProduct 5 1 a r 0) +
            15 * thetaCuspCenterMixedDerivativeProduct 4 2 a r 0) -
          20 * thetaCuspCenterMixedDerivativeProduct 3 3 a r 0) =
        (∫ r : ℝ in Ioi 0,
          (thetaCuspCenterMixedDerivativeProduct 6 0 a r 0 -
            6 * thetaCuspCenterMixedDerivativeProduct 5 1 a r 0) +
              15 * thetaCuspCenterMixedDerivativeProduct 4 2 a r 0) -
          ∫ r : ℝ in Ioi 0, 20 * thetaCuspCenterMixedDerivativeProduct 3 3 a r 0 :=
    integral_sub h2 h33s
  have hi4 :
      (∫ r : ℝ in Ioi 0,
        (((thetaCuspCenterMixedDerivativeProduct 6 0 a r 0 -
          6 * thetaCuspCenterMixedDerivativeProduct 5 1 a r 0) +
            15 * thetaCuspCenterMixedDerivativeProduct 4 2 a r 0) -
          20 * thetaCuspCenterMixedDerivativeProduct 3 3 a r 0) +
            15 * thetaCuspCenterMixedDerivativeProduct 2 4 a r 0) =
        (∫ r : ℝ in Ioi 0,
          ((thetaCuspCenterMixedDerivativeProduct 6 0 a r 0 -
            6 * thetaCuspCenterMixedDerivativeProduct 5 1 a r 0) +
              15 * thetaCuspCenterMixedDerivativeProduct 4 2 a r 0) -
            20 * thetaCuspCenterMixedDerivativeProduct 3 3 a r 0) +
          ∫ r : ℝ in Ioi 0, 15 * thetaCuspCenterMixedDerivativeProduct 2 4 a r 0 :=
    integral_add h3 h24s
  have hi5 :
      (∫ r : ℝ in Ioi 0,
        ((((thetaCuspCenterMixedDerivativeProduct 6 0 a r 0 -
          6 * thetaCuspCenterMixedDerivativeProduct 5 1 a r 0) +
            15 * thetaCuspCenterMixedDerivativeProduct 4 2 a r 0) -
          20 * thetaCuspCenterMixedDerivativeProduct 3 3 a r 0) +
            15 * thetaCuspCenterMixedDerivativeProduct 2 4 a r 0) -
          6 * thetaCuspCenterMixedDerivativeProduct 1 5 a r 0) =
        (∫ r : ℝ in Ioi 0,
          (((thetaCuspCenterMixedDerivativeProduct 6 0 a r 0 -
            6 * thetaCuspCenterMixedDerivativeProduct 5 1 a r 0) +
              15 * thetaCuspCenterMixedDerivativeProduct 4 2 a r 0) -
            20 * thetaCuspCenterMixedDerivativeProduct 3 3 a r 0) +
              15 * thetaCuspCenterMixedDerivativeProduct 2 4 a r 0) -
          ∫ r : ℝ in Ioi 0, 6 * thetaCuspCenterMixedDerivativeProduct 1 5 a r 0 :=
    integral_sub h4 h15s
  have hi6 :
      (∫ r : ℝ in Ioi 0,
        (((((thetaCuspCenterMixedDerivativeProduct 6 0 a r 0 -
          6 * thetaCuspCenterMixedDerivativeProduct 5 1 a r 0) +
            15 * thetaCuspCenterMixedDerivativeProduct 4 2 a r 0) -
          20 * thetaCuspCenterMixedDerivativeProduct 3 3 a r 0) +
            15 * thetaCuspCenterMixedDerivativeProduct 2 4 a r 0) -
          6 * thetaCuspCenterMixedDerivativeProduct 1 5 a r 0) +
            thetaCuspCenterMixedDerivativeProduct 0 6 a r 0) =
        (∫ r : ℝ in Ioi 0,
          ((((thetaCuspCenterMixedDerivativeProduct 6 0 a r 0 -
            6 * thetaCuspCenterMixedDerivativeProduct 5 1 a r 0) +
              15 * thetaCuspCenterMixedDerivativeProduct 4 2 a r 0) -
            20 * thetaCuspCenterMixedDerivativeProduct 3 3 a r 0) +
              15 * thetaCuspCenterMixedDerivativeProduct 2 4 a r 0) -
            6 * thetaCuspCenterMixedDerivativeProduct 1 5 a r 0) +
          ∫ r : ℝ in Ioi 0, thetaCuspCenterMixedDerivativeProduct 0 6 a r 0 :=
    integral_add h5 h06
  calc
    (∫ r : ℝ in Ioi 0, thetaCuspCenterMixedReflectionJetSixIntegrand a r) =
        ∫ r : ℝ in Ioi 0,
          (((((thetaCuspCenterMixedDerivativeProduct 6 0 a r 0 -
              6 * thetaCuspCenterMixedDerivativeProduct 5 1 a r 0) +
            15 * thetaCuspCenterMixedDerivativeProduct 4 2 a r 0) -
          20 * thetaCuspCenterMixedDerivativeProduct 3 3 a r 0) +
        15 * thetaCuspCenterMixedDerivativeProduct 2 4 a r 0) -
      6 * thetaCuspCenterMixedDerivativeProduct 1 5 a r 0) +
      thetaCuspCenterMixedDerivativeProduct 0 6 a r 0 := by
        apply integral_congr_ae
        filter_upwards with r
        unfold thetaCuspCenterMixedReflectionJetSixIntegrand
          thetaCuspSourceReflectionJetSix thetaCuspCenterMixedDerivativeProduct
          HilbertMetric.reflectedProductSixthJet
        simp only [add_zero, sub_zero, iteratedDeriv_zero]
        ring
    _ = thetaCuspCenterMixedDerivativeProductIntegral 6 0 a 0 -
          6 * thetaCuspCenterMixedDerivativeProductIntegral 5 1 a 0 +
        15 * thetaCuspCenterMixedDerivativeProductIntegral 4 2 a 0 -
          20 * thetaCuspCenterMixedDerivativeProductIntegral 3 3 a 0 +
        15 * thetaCuspCenterMixedDerivativeProductIntegral 2 4 a 0 -
          6 * thetaCuspCenterMixedDerivativeProductIntegral 1 5 a 0 +
        thetaCuspCenterMixedDerivativeProductIntegral 0 6 a 0 := by
      rw [hi6, hi5, hi4, hi3, hi2, hi1,
        integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const_mul, integral_const_mul]
      rfl
    _ = thetaCuspCenterMixedDensitySixthJet a 0 := by rfl

/-- Every reflected complete-source fibre has negative second center jet. -/
theorem thetaCuspSourceReflectionJetTwo_neg (x : ℝ) :
    thetaCuspSourceReflectionJetTwo x < 0 := by
  have hnum := thetaCuspLogConcavityNumerator_neg_all x
  unfold thetaCuspLogConcavityNumerator at hnum
  unfold thetaCuspSourceReflectionJetTwo
  simp only [iteratedDeriv_one] at hnum ⊢
  nlinarith

/-- Strict raw curvature and negative second jet force negative sixth jet. -/
theorem thetaCuspSourceReflectionJetSix_neg (x : ℝ) :
    thetaCuspSourceReflectionJetSix x < 0 := by
  have h2 := thetaCuspSourceReflectionJetTwo_neg x
  have hdet := thetaCuspFullSourceReflectionSecondSixthCurvature_pos x
  have hid : thetaCuspFullSourceReflectionSecondSixthCurvature x =
      thetaCuspSourceReflectionJetTwo x * thetaCuspSourceReflectionJetSix x -
        thetaCuspSourceReflectionJetFour x ^ (2 : ℕ) := by
    unfold thetaCuspFullSourceReflectionSecondSixthCurvature
      thetaCuspSourceReflectionJetTwo thetaCuspSourceReflectionJetFour
      thetaCuspSourceReflectionJetSix HilbertMetric.reflectedProductSecondJet
      HilbertMetric.reflectedProductFourthJet
    simp only [iteratedDeriv_zero]
  rw [hid] at hdet
  by_contra hn
  have h6 : 0 ≤ thetaCuspSourceReflectionJetSix x := le_of_not_gt hn
  have hprod : thetaCuspSourceReflectionJetTwo x * thetaCuspSourceReflectionJetSix x ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg h2.le h6
  nlinarith [sq_nonneg (thetaCuspSourceReflectionJetFour x)]

/-- C1: strict second--sixth Hankel margin of every physical center-mixed theta density. -/
theorem thetaCuspCenterMixedDensity_secondSixthHankel_pos
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    0 < thetaCuspCenterMixedDensitySecondJet a 0 *
        thetaCuspCenterMixedDensitySixthJet a 0 -
      thetaCuspCenterMixedDensityFourthJet a 0 ^ (2 : ℕ) := by
  let p0 : ℝ → ℝ := fun r => -thetaCuspCenterMixedReflectionJetTwoIntegrand a r
  let p2 : ℝ → ℝ := thetaCuspCenterMixedReflectionJetFourIntegrand a
  let p4 : ℝ → ℝ := fun r => -thetaCuspCenterMixedReflectionJetSixIntegrand a r
  have hI2 := integrableOn_thetaCuspCenterMixedReflectionJetTwoIntegrand ha0.le ha
  have hI4 := integrableOn_thetaCuspCenterMixedReflectionJetFourIntegrand ha0.le ha
  have hI6 := integrableOn_thetaCuspCenterMixedReflectionJetSixIntegrand ha0.le ha
  have hp0I : IntegrableOn p0 (Ioi 0) := hI2.neg
  have hp2I : IntegrableOn p2 (Ioi 0) := hI4
  have hp4I : IntegrableOn p4 (Ioi 0) := hI6.neg
  have hmass : 0 < ∫ r : ℝ in Ioi 0, p0 r := by
    dsimp only [p0]
    rw [integral_neg, integral_thetaCuspCenterMixedReflectionJetTwoIntegrand ha0.le ha]
    linarith [thetaCuspCenterMixedDensitySecondJet_zero_neg ha0 ha]
  have hpoint : ∀ᵐ r : ℝ ∂volume.restrict (Ioi 0),
      0 < p0 r ∧ 0 < p0 r * p4 r - p2 r ^ (2 : ℕ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hweight : 0 < r * Real.sinh (a * r) :=
      mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha0 hr))
    have h2 := thetaCuspSourceReflectionJetTwo_neg (r / 2)
    have h6 := thetaCuspSourceReflectionJetSix_neg (r / 2)
    have hdet := thetaCuspFullSourceReflectionSecondSixthCurvature_pos (r / 2)
    have hraw : thetaCuspFullSourceReflectionSecondSixthCurvature (r / 2) =
        thetaCuspSourceReflectionJetTwo (r / 2) *
            thetaCuspSourceReflectionJetSix (r / 2) -
          thetaCuspSourceReflectionJetFour (r / 2) ^ (2 : ℕ) := by
      unfold thetaCuspFullSourceReflectionSecondSixthCurvature
        thetaCuspSourceReflectionJetTwo thetaCuspSourceReflectionJetFour
        thetaCuspSourceReflectionJetSix HilbertMetric.reflectedProductSecondJet
        HilbertMetric.reflectedProductFourthJet
      simp only [iteratedDeriv_zero]
    rw [hraw] at hdet
    constructor
    · dsimp only [p0, thetaCuspCenterMixedReflectionJetTwoIntegrand]
      exact neg_pos.mpr (mul_neg_of_pos_of_neg hweight h2)
    · dsimp only [p0, p2, p4,
        thetaCuspCenterMixedReflectionJetTwoIntegrand,
        thetaCuspCenterMixedReflectionJetFourIntegrand,
        thetaCuspCenterMixedReflectionJetSixIntegrand]
      have hsquare : 0 < (r * Real.sinh (a * r)) ^ (2 : ℕ) := sq_pos_of_pos hweight
      nlinarith
  have hmix := GaloisForLFunctions.HilbertMetric.integral_twoByTwo_det_pos
    p0 p2 p4 hp0I hp2I hp4I hmass hpoint
  dsimp only [p0, p2, p4] at hmix
  rw [integral_neg,
    integral_thetaCuspCenterMixedReflectionJetTwoIntegrand ha0.le ha,
    integral_thetaCuspCenterMixedReflectionJetFourIntegrand ha0.le ha,
    integral_neg,
    integral_thetaCuspCenterMixedReflectionJetSixIntegrand ha0.le ha] at hmix
  nlinarith

/-- Literal derivative form of C1. -/
theorem thetaCuspCenterMixedDensity_iteratedDeriv_secondSixthHankel_pos
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    0 < iteratedDeriv 2 (thetaCuspCenterMixedDensity a) 0 *
        iteratedDeriv 6 (thetaCuspCenterMixedDensity a) 0 -
      iteratedDeriv 4 (thetaCuspCenterMixedDensity a) 0 ^ (2 : ℕ) := by
  rw [iteratedDeriv_two_thetaCuspCenterMixedDensity ha0.le ha,
    iteratedDeriv_four_thetaCuspCenterMixedDensity ha0.le ha,
    iteratedDeriv_six_thetaCuspCenterMixedDensity ha0.le ha]
  exact thetaCuspCenterMixedDensity_secondSixthHankel_pos ha0 ha

/-- Closed universal form of the center-mixed sixth Hankel inequality. -/
theorem thetaCuspCenterMixedDensity_iteratedDeriv_secondSixthHankel_pos_all :
    ∀ a : ℝ, 0 < a → a < 1 / 2 →
      0 < iteratedDeriv 2 (thetaCuspCenterMixedDensity a) 0 *
          iteratedDeriv 6 (thetaCuspCenterMixedDensity a) 0 -
        iteratedDeriv 4 (thetaCuspCenterMixedDensity a) 0 ^ (2 : ℕ) := by
  intro a ha0 ha
  exact thetaCuspCenterMixedDensity_iteratedDeriv_secondSixthHankel_pos ha0 ha

end

end RHTower
