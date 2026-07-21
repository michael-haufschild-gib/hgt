import GaloisForLFunctions.RHTower.HedenmalmCenterMixedFourthJetCusp
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionFourthTuran
import GaloisForLFunctions.HilbertMetric.FourthCurvatureMixture

/-!
# Unconditional closure of the center-mixed fourth-jet cusp

The complete theta-source fourth logarithmic Turan law makes the reflected source's pointwise
fourth Hankel matrix strictly positive.  Integrating its quadratic form against the strictly
positive center-mixing weight preserves strictness.  This discharges the last source hypothesis
in the coalesced Hedenmalm cusp theorem.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Weighted zeroth reflected-source jet in the center mixture. -/
def thetaCuspCenterMixedReflectionJetZeroIntegrand (a r : ℝ) : ℝ :=
  r * Real.sinh (a * r) * thetaCuspSourceReflectionJetZero (r / 2)

/-- Weighted second reflected-source jet in the center mixture. -/
def thetaCuspCenterMixedReflectionJetTwoIntegrand (a r : ℝ) : ℝ :=
  r * Real.sinh (a * r) * thetaCuspSourceReflectionJetTwo (r / 2)

/-- Weighted fourth reflected-source jet in the center mixture. -/
def thetaCuspCenterMixedReflectionJetFourIntegrand (a r : ℝ) : ℝ :=
  r * Real.sinh (a * r) * thetaCuspSourceReflectionJetFour (r / 2)

private theorem integrableOn_thetaCuspCenterMixedReflectionJetZeroIntegrand
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    IntegrableOn (thetaCuspCenterMixedReflectionJetZeroIntegrand a) (Ioi 0) := by
  have h00 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 0 0
  exact h00.congr (ae_of_all _ fun r => by
    unfold thetaCuspCenterMixedReflectionJetZeroIntegrand
      thetaCuspSourceReflectionJetZero thetaCuspCenterMixedDerivativeProduct
    simp only [add_zero, sub_zero, iteratedDeriv_zero]
    ring)

private theorem integrableOn_thetaCuspCenterMixedReflectionJetTwoIntegrand
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    IntegrableOn (thetaCuspCenterMixedReflectionJetTwoIntegrand a) (Ioi 0) := by
  have h20 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 2 0
  have h11 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 1 1
  have h02 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 0 2
  have hcomb := (h20.sub (h11.const_mul 2)).add h02
  exact hcomb.congr (ae_of_all _ fun r => by
    unfold thetaCuspCenterMixedReflectionJetTwoIntegrand
      thetaCuspSourceReflectionJetTwo thetaCuspCenterMixedDerivativeProduct
    simp only [add_zero, sub_zero, iteratedDeriv_zero, Pi.add_apply, Pi.sub_apply]
    ring)

private theorem integrableOn_thetaCuspCenterMixedReflectionJetFourIntegrand
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    IntegrableOn (thetaCuspCenterMixedReflectionJetFourIntegrand a) (Ioi 0) := by
  have h40 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 4 0
  have h31 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 3 1
  have h22 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 2 2
  have h13 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 1 3
  have h04 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 0 4
  have hcomb := ((((h40.sub (h31.const_mul 4)).add (h22.const_mul 6)).sub
    (h13.const_mul 4)).add h04)
  exact hcomb.congr (ae_of_all _ fun r => by
    unfold thetaCuspCenterMixedReflectionJetFourIntegrand
      thetaCuspSourceReflectionJetFour thetaCuspCenterMixedDerivativeProduct
    simp only [add_zero, sub_zero, iteratedDeriv_zero, Pi.add_apply, Pi.sub_apply]
    ring)

private theorem integral_thetaCuspCenterMixedReflectionJetZeroIntegrand
    (a : ℝ) :
    (∫ r : ℝ in Ioi 0, thetaCuspCenterMixedReflectionJetZeroIntegrand a r) =
      thetaCuspCenterMixedDensity a 0 := by
  unfold thetaCuspCenterMixedReflectionJetZeroIntegrand thetaCuspSourceReflectionJetZero
    thetaCuspCenterMixedDensity
  apply integral_congr_ae
  filter_upwards with r
  simp only [add_zero, sub_zero]
  ring

private theorem integral_thetaCuspCenterMixedReflectionJetTwoIntegrand
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    (∫ r : ℝ in Ioi 0, thetaCuspCenterMixedReflectionJetTwoIntegrand a r) =
      thetaCuspCenterMixedDensitySecondJet a 0 := by
  have h20 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 2 0
  have h11 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 1 1
  have h02 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 0 2
  calc
    (∫ r : ℝ in Ioi 0, thetaCuspCenterMixedReflectionJetTwoIntegrand a r) =
        ∫ r : ℝ in Ioi 0,
          thetaCuspCenterMixedDerivativeProduct 2 0 a r 0 -
            2 * thetaCuspCenterMixedDerivativeProduct 1 1 a r 0 +
              thetaCuspCenterMixedDerivativeProduct 0 2 a r 0 := by
      apply integral_congr_ae
      filter_upwards with r
      unfold thetaCuspCenterMixedReflectionJetTwoIntegrand
        thetaCuspSourceReflectionJetTwo thetaCuspCenterMixedDerivativeProduct
      simp only [add_zero, sub_zero, iteratedDeriv_zero]
      ring
    _ = thetaCuspCenterMixedDerivativeProductIntegral 2 0 a 0 -
          2 * thetaCuspCenterMixedDerivativeProductIntegral 1 1 a 0 +
            thetaCuspCenterMixedDerivativeProductIntegral 0 2 a 0 := by
      calc
        (∫ r : ℝ in Ioi 0,
            thetaCuspCenterMixedDerivativeProduct 2 0 a r 0 -
                2 * thetaCuspCenterMixedDerivativeProduct 1 1 a r 0 +
              thetaCuspCenterMixedDerivativeProduct 0 2 a r 0) =
            (∫ r : ℝ in Ioi 0,
              thetaCuspCenterMixedDerivativeProduct 2 0 a r 0 -
                2 * thetaCuspCenterMixedDerivativeProduct 1 1 a r 0) +
              ∫ r : ℝ in Ioi 0,
                thetaCuspCenterMixedDerivativeProduct 0 2 a r 0 := by
          exact integral_add (h20.sub (h11.const_mul 2)) h02
        _ = ((∫ r : ℝ in Ioi 0, thetaCuspCenterMixedDerivativeProduct 2 0 a r 0) -
              ∫ r : ℝ in Ioi 0, 2 * thetaCuspCenterMixedDerivativeProduct 1 1 a r 0) +
              ∫ r : ℝ in Ioi 0, thetaCuspCenterMixedDerivativeProduct 0 2 a r 0 := by
          rw [integral_sub h20 (h11.const_mul 2)]
        _ = _ := by
          rw [integral_const_mul]
          rfl
    _ = thetaCuspCenterMixedDensitySecondJet a 0 := by
      rfl

private theorem integral_thetaCuspCenterMixedReflectionJetFourIntegrand
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    (∫ r : ℝ in Ioi 0, thetaCuspCenterMixedReflectionJetFourIntegrand a r) =
      thetaCuspCenterMixedDensityFourthJet a 0 := by
  have h40 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 4 0
  have h31 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 3 1
  have h22 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 2 2
  have h13 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 1 3
  have h04 := integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0 ha 0 4
  calc
    (∫ r : ℝ in Ioi 0, thetaCuspCenterMixedReflectionJetFourIntegrand a r) =
        ∫ r : ℝ in Ioi 0,
          thetaCuspCenterMixedDerivativeProduct 4 0 a r 0 -
            4 * thetaCuspCenterMixedDerivativeProduct 3 1 a r 0 +
              6 * thetaCuspCenterMixedDerivativeProduct 2 2 a r 0 -
                4 * thetaCuspCenterMixedDerivativeProduct 1 3 a r 0 +
                  thetaCuspCenterMixedDerivativeProduct 0 4 a r 0 := by
      apply integral_congr_ae
      filter_upwards with r
      unfold thetaCuspCenterMixedReflectionJetFourIntegrand
        thetaCuspSourceReflectionJetFour thetaCuspCenterMixedDerivativeProduct
      simp only [add_zero, sub_zero, iteratedDeriv_zero]
      ring
    _ = thetaCuspCenterMixedDerivativeProductIntegral 4 0 a 0 -
          4 * thetaCuspCenterMixedDerivativeProductIntegral 3 1 a 0 +
            6 * thetaCuspCenterMixedDerivativeProductIntegral 2 2 a 0 -
              4 * thetaCuspCenterMixedDerivativeProductIntegral 1 3 a 0 +
                thetaCuspCenterMixedDerivativeProductIntegral 0 4 a 0 := by
      calc
        (∫ r : ℝ in Ioi 0,
            (((thetaCuspCenterMixedDerivativeProduct 4 0 a r 0 -
                4 * thetaCuspCenterMixedDerivativeProduct 3 1 a r 0) +
              6 * thetaCuspCenterMixedDerivativeProduct 2 2 a r 0) -
              4 * thetaCuspCenterMixedDerivativeProduct 1 3 a r 0) +
              thetaCuspCenterMixedDerivativeProduct 0 4 a r 0) =
            (∫ r : ℝ in Ioi 0,
              ((thetaCuspCenterMixedDerivativeProduct 4 0 a r 0 -
                  4 * thetaCuspCenterMixedDerivativeProduct 3 1 a r 0) +
                6 * thetaCuspCenterMixedDerivativeProduct 2 2 a r 0) -
                4 * thetaCuspCenterMixedDerivativeProduct 1 3 a r 0) +
              ∫ r : ℝ in Ioi 0,
                thetaCuspCenterMixedDerivativeProduct 0 4 a r 0 := by
          exact integral_add
            (((h40.sub (h31.const_mul 4)).add (h22.const_mul 6)).sub
              (h13.const_mul 4)) h04
        _ = (∫ r : ℝ in Ioi 0,
              (thetaCuspCenterMixedDerivativeProduct 4 0 a r 0 -
                  4 * thetaCuspCenterMixedDerivativeProduct 3 1 a r 0) +
                6 * thetaCuspCenterMixedDerivativeProduct 2 2 a r 0) -
              (∫ r : ℝ in Ioi 0,
                4 * thetaCuspCenterMixedDerivativeProduct 1 3 a r 0) +
              (∫ r : ℝ in Ioi 0,
                thetaCuspCenterMixedDerivativeProduct 0 4 a r 0) := by
          apply congrArg (fun z => z +
            ∫ r : ℝ in Ioi 0, thetaCuspCenterMixedDerivativeProduct 0 4 a r 0)
          exact integral_sub ((h40.sub (h31.const_mul 4)).add (h22.const_mul 6))
            (h13.const_mul 4)
        _ = (∫ r : ℝ in Ioi 0,
              thetaCuspCenterMixedDerivativeProduct 4 0 a r 0) -
              (∫ r : ℝ in Ioi 0,
                4 * thetaCuspCenterMixedDerivativeProduct 3 1 a r 0) +
              (∫ r : ℝ in Ioi 0,
                6 * thetaCuspCenterMixedDerivativeProduct 2 2 a r 0) -
              (∫ r : ℝ in Ioi 0,
                4 * thetaCuspCenterMixedDerivativeProduct 1 3 a r 0) +
              (∫ r : ℝ in Ioi 0,
                thetaCuspCenterMixedDerivativeProduct 0 4 a r 0) := by
          apply congrArg (fun z => (z -
            (∫ r : ℝ in Ioi 0,
              4 * thetaCuspCenterMixedDerivativeProduct 1 3 a r 0)) +
            ∫ r : ℝ in Ioi 0, thetaCuspCenterMixedDerivativeProduct 0 4 a r 0)
          calc
            (∫ r : ℝ in Ioi 0,
                (thetaCuspCenterMixedDerivativeProduct 4 0 a r 0 -
                    4 * thetaCuspCenterMixedDerivativeProduct 3 1 a r 0) +
                  6 * thetaCuspCenterMixedDerivativeProduct 2 2 a r 0) =
                (∫ r : ℝ in Ioi 0,
                  thetaCuspCenterMixedDerivativeProduct 4 0 a r 0 -
                    4 * thetaCuspCenterMixedDerivativeProduct 3 1 a r 0) +
                  ∫ r : ℝ in Ioi 0,
                    6 * thetaCuspCenterMixedDerivativeProduct 2 2 a r 0 :=
              integral_add (h40.sub (h31.const_mul 4)) (h22.const_mul 6)
            _ = (∫ r : ℝ in Ioi 0,
                  thetaCuspCenterMixedDerivativeProduct 4 0 a r 0) -
                  (∫ r : ℝ in Ioi 0,
                    4 * thetaCuspCenterMixedDerivativeProduct 3 1 a r 0) +
                  (∫ r : ℝ in Ioi 0,
                    6 * thetaCuspCenterMixedDerivativeProduct 2 2 a r 0) := by
              apply congrArg (fun z => z +
                ∫ r : ℝ in Ioi 0,
                  6 * thetaCuspCenterMixedDerivativeProduct 2 2 a r 0)
              exact integral_sub h40 (h31.const_mul 4)
        _ = _ := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul]
          rfl
    _ = thetaCuspCenterMixedDensityFourthJet a 0 := by
      rfl

/-- The fourth center Hankel determinant of the actual center-mixed theta density is strictly
positive throughout the critical aperture. -/
theorem thetaCuspCenterMixedDensity_fourthHankel_pos
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    0 < thetaCuspCenterMixedDensity a 0 *
        thetaCuspCenterMixedDensityFourthJet a 0 -
      thetaCuspCenterMixedDensitySecondJet a 0 ^ 2 := by
  have hI0 := integrableOn_thetaCuspCenterMixedReflectionJetZeroIntegrand ha0.le ha
  have hI2 := integrableOn_thetaCuspCenterMixedReflectionJetTwoIntegrand ha0.le ha
  have hI4 := integrableOn_thetaCuspCenterMixedReflectionJetFourIntegrand ha0.le ha
  have hmass : 0 < ∫ r : ℝ in Ioi 0,
      thetaCuspCenterMixedReflectionJetZeroIntegrand a r := by
    rw [integral_thetaCuspCenterMixedReflectionJetZeroIntegrand]
    exact thetaCuspCenterMixedDensity_pos ha0 ha 0
  have hpoint : ∀ᵐ r : ℝ ∂volume.restrict (Ioi 0),
      0 < thetaCuspCenterMixedReflectionJetZeroIntegrand a r ∧
        0 < thetaCuspCenterMixedReflectionJetZeroIntegrand a r *
            thetaCuspCenterMixedReflectionJetFourIntegrand a r -
          thetaCuspCenterMixedReflectionJetTwoIntegrand a r ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hweight : 0 < r * Real.sinh (a * r) :=
      mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha0 hr))
    have hp0 : 0 < thetaCuspSourceReflectionJetZero (r / 2) := by
      unfold thetaCuspSourceReflectionJetZero
      exact sq_pos_of_pos (thetaCuspFullSource_pos_of_pos (half_pos hr))
    have hdet := thetaCuspSourceReflectionFourthHankel_pos
      (x := r / 2) (half_pos hr)
    constructor
    · unfold thetaCuspCenterMixedReflectionJetZeroIntegrand
      exact mul_pos hweight hp0
    · have hfactor :
          thetaCuspCenterMixedReflectionJetZeroIntegrand a r *
              thetaCuspCenterMixedReflectionJetFourIntegrand a r -
            thetaCuspCenterMixedReflectionJetTwoIntegrand a r ^ 2 =
          (r * Real.sinh (a * r)) ^ 2 *
            (thetaCuspSourceReflectionJetZero (r / 2) *
                thetaCuspSourceReflectionJetFour (r / 2) -
              thetaCuspSourceReflectionJetTwo (r / 2) ^ 2) := by
        unfold thetaCuspCenterMixedReflectionJetZeroIntegrand
          thetaCuspCenterMixedReflectionJetTwoIntegrand
          thetaCuspCenterMixedReflectionJetFourIntegrand
        ring
      rw [hfactor]
      exact mul_pos (sq_pos_of_pos hweight) hdet
  have hmix :=
    GaloisForLFunctions.HilbertMetric.integral_twoByTwo_det_pos
      (thetaCuspCenterMixedReflectionJetZeroIntegrand a)
      (thetaCuspCenterMixedReflectionJetTwoIntegrand a)
      (thetaCuspCenterMixedReflectionJetFourIntegrand a)
      hI0 hI2 hI4 hmass hpoint
  rw [integral_thetaCuspCenterMixedReflectionJetZeroIntegrand,
    integral_thetaCuspCenterMixedReflectionJetTwoIntegrand ha0.le ha,
    integral_thetaCuspCenterMixedReflectionJetFourIntegrand ha0.le ha] at hmix
  exact hmix

/-- **Unconditional center-mixed coalesced cusp.**  Every critical aperture has a nested
positive-definite three-point cusp for the actual theta density, with no fourth-jet hypothesis. -/
theorem exists_thetaCuspCenterMixed_coalescedCusp_posDef
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, 0 < y → y < δ →
      ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, 0 < x → x < ε →
        Matrix.PosDef (thetaCuspCenterMixedThreePointMatrix a x y) := by
  exact exists_thetaCuspCenterMixed_coalescedCusp_posDef_of_fourthJet
    ha0 ha (thetaCuspCenterMixedDensity_fourthHankel_pos ha0 ha)

end

end RHTower
