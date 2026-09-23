import GaloisForLFunctions.RHTower.PrimeArchThetaLikelihoodOrderedTailTransfer
import GaloisForLFunctions.RHTower.PrimeArchThetaWardLaplaceHalfDensity

/-!
# Reflected-budget transfer from the first theta atom to the completed source

The reflected half-density value fixes the complete higher-atom budget.  Combining its first two
positive Taylor terms with the exact first/higher likelihood order replaces the uniform tail
factor in both live low-degree susceptibility gates by the closed reflected budget.
-/

namespace RHTower

noncomputable section

/-- The first two weighted first-atom moments occurring in the reflected half-density budget. -/
def thetaCuspFirstAtomHalfDensityPairBudget : ℝ :=
  thetaCuspAtomRawEvenMoment 0 1 + thetaCuspAtomRawEvenMoment 1 1 / 8

theorem thetaCuspFirstAtomHalfDensityPairBudget_pos :
    0 < thetaCuspFirstAtomHalfDensityPairBudget := by
  have h0 := thetaCuspAtomRawEvenMoment_nonneg 0 1
  have h1 : 0 < thetaCuspAtomRawEvenMoment 1 1 :=
    thetaCuspAtomRawEvenMoment_pos_of_nat_pos 1 (by norm_num)
  rw [thetaCuspFirstAtomHalfDensityPairBudget]
  positivity

/-- The likelihood order between the higher tail and first atom persists after adding the first
atom back to the tail. -/
theorem thetaCuspRawFirst_rawEvenMoment_cross_le (k n : ℕ) :
    thetaCuspRawEvenMoment (k + n) * thetaCuspAtomRawEvenMoment k 1 ≤
      thetaCuspAtomRawEvenMoment (k + n) 1 * thetaCuspRawEvenMoment k := by
  have htail := thetaCuspHigherFirst_rawEvenMoment_cross_le k n
  rw [thetaCuspRawEvenMoment_eq_one_add_higher,
    thetaCuspRawEvenMoment_eq_one_add_higher]
  nlinarith

/-- The exact reflected budget bounds the first relative higher-tail moment in division-free
form. -/
theorem thetaCuspHigherFirst_firstMoment_mul_pairBudget_le :
    thetaCuspHigherAtomRawEvenMoment 1 *
        thetaCuspFirstAtomHalfDensityPairBudget ≤
      thetaCuspAtomRawEvenMoment 1 1 * thetaCuspHigherHalfDensityBudget := by
  have hcross := thetaCuspHigherFirst_rawEvenMoment_cross_le 0 1
  norm_num at hcross
  have hpair := thetaCuspHigherAtomMomentPair_le_halfDensityBudget
  have ha1 : 0 ≤ thetaCuspAtomRawEvenMoment 1 1 :=
    thetaCuspAtomRawEvenMoment_nonneg 1 1
  rw [thetaCuspFirstAtomHalfDensityPairBudget]
  calc
    thetaCuspHigherAtomRawEvenMoment 1 *
          (thetaCuspAtomRawEvenMoment 0 1 +
            thetaCuspAtomRawEvenMoment 1 1 / 8) =
        thetaCuspHigherAtomRawEvenMoment 1 *
            thetaCuspAtomRawEvenMoment 0 1 +
          thetaCuspAtomRawEvenMoment 1 1 *
            thetaCuspHigherAtomRawEvenMoment 1 / 8 := by ring
    _ ≤ thetaCuspAtomRawEvenMoment 1 1 *
          thetaCuspHigherAtomRawEvenMoment 0 +
        thetaCuspAtomRawEvenMoment 1 1 *
          thetaCuspHigherAtomRawEvenMoment 1 / 8 :=
      add_le_add hcross (le_refl _)
    _ = thetaCuspAtomRawEvenMoment 1 1 *
        (thetaCuspHigherAtomRawEvenMoment 0 +
          thetaCuspHigherAtomRawEvenMoment 1 / 8) := by ring
    _ ≤ thetaCuspAtomRawEvenMoment 1 1 * thetaCuspHigherHalfDensityBudget :=
      mul_le_mul_of_nonneg_left hpair ha1

/-- The completed second raw moment pays exactly the reflected first/higher budget, with no
uniform atom-domination factor. -/
theorem thetaCuspRawEvenMoment_one_mul_pairBudget_le :
    thetaCuspRawEvenMoment 1 * thetaCuspFirstAtomHalfDensityPairBudget ≤
      thetaCuspAtomRawEvenMoment 1 1 *
        (thetaCuspFirstAtomHalfDensityPairBudget +
          thetaCuspHigherHalfDensityBudget) := by
  have htail := thetaCuspHigherFirst_firstMoment_mul_pairBudget_le
  rw [thetaCuspRawEvenMoment_eq_one_add_higher]
  calc
    (thetaCuspAtomRawEvenMoment 1 1 + thetaCuspHigherAtomRawEvenMoment 1) *
          thetaCuspFirstAtomHalfDensityPairBudget =
        thetaCuspAtomRawEvenMoment 1 1 *
            thetaCuspFirstAtomHalfDensityPairBudget +
          thetaCuspHigherAtomRawEvenMoment 1 *
            thetaCuspFirstAtomHalfDensityPairBudget := by ring
    _ ≤ thetaCuspAtomRawEvenMoment 1 1 *
          thetaCuspFirstAtomHalfDensityPairBudget +
        thetaCuspAtomRawEvenMoment 1 1 * thetaCuspHigherHalfDensityBudget :=
      add_le_add (le_refl _) htail
    _ = thetaCuspAtomRawEvenMoment 1 1 *
        (thetaCuspFirstAtomHalfDensityPairBudget +
          thetaCuspHigherHalfDensityBudget) := by ring

/-- The exact reflected-budget first-atom condition implies the completed lower susceptibility
gate. -/
theorem thetaCuspUpperAdjacentRatioSeparation_of_reflectedBudget
    (hfirst :
      14 * (thetaCuspFirstAtomHalfDensityPairBudget +
          thetaCuspHigherHalfDensityBudget) *
          thetaCuspAtomRawEvenMoment 2 1 ^ (2 : ℕ) ≤
        9 * thetaCuspFirstAtomHalfDensityPairBudget *
          thetaCuspAtomRawEvenMoment 1 1 *
            thetaCuspAtomRawEvenMoment 3 1) :
    ThetaCuspUpperAdjacentRatioSeparation := by
  rw [ThetaCuspUpperAdjacentRatioSeparation]
  let W := thetaCuspFirstAtomHalfDensityPairBudget
  let H := thetaCuspHigherHalfDensityBudget
  let a1 := thetaCuspAtomRawEvenMoment 1 1
  let a2 := thetaCuspAtomRawEvenMoment 2 1
  let a3 := thetaCuspAtomRawEvenMoment 3 1
  let m1 := thetaCuspRawEvenMoment 1
  let m2 := thetaCuspRawEvenMoment 2
  let m3 := thetaCuspRawEvenMoment 3
  have hW : 0 < W := thetaCuspFirstAtomHalfDensityPairBudget_pos
  have ha1 : 0 < a1 := thetaCuspAtomRawEvenMoment_pos_of_nat_pos 1 (by norm_num)
  have ha2 : 0 ≤ a2 := thetaCuspAtomRawEvenMoment_nonneg 2 1
  have hm1 : 0 ≤ m1 := thetaCuspRawEvenMoment_nonneg 1
  have hm2 : 0 ≤ m2 := thetaCuspRawEvenMoment_nonneg 2
  have hm1W : m1 * W ≤ a1 * (W + H) := by
    simpa only [m1, W, a1, H] using thetaCuspRawEvenMoment_one_mul_pairBudget_le
  have hcross : m2 * a1 ≤ a2 * m1 := by
    simpa only [m1, m2, a1, a2] using
      thetaCuspRawFirst_rawEvenMoment_cross_le 1 1
  have hcrossSq : (m2 * a1) ^ (2 : ℕ) ≤ (a2 * m1) ^ (2 : ℕ) :=
    (sq_le_sq₀ (mul_nonneg hm2 ha1.le) (mul_nonneg ha2 hm1)).2 hcross
  have ha3m3 : a3 ≤ m3 := by
    simpa only [a3, m3] using thetaCuspAtomRawEvenMoment_one_le_raw 3
  have hfirst' : 14 * (W + H) * a2 ^ (2 : ℕ) ≤ 9 * W * a1 * a3 := by
    simpa only [W, H, a1, a2, a3] using hfirst
  have hfactor : 0 < W * a1 ^ (2 : ℕ) := mul_pos hW (sq_pos_of_pos ha1)
  apply (mul_le_mul_iff_of_pos_left hfactor).mp
  calc
    (W * a1 ^ (2 : ℕ)) * (14 * m2 ^ (2 : ℕ)) = 14 * W * (m2 * a1) ^ (2 : ℕ) := by ring
    _ ≤ 14 * W * (a2 * m1) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hcrossSq (by positivity)
    _ = (14 * a2 ^ (2 : ℕ) * m1) * (m1 * W) := by ring
    _ ≤ (14 * a2 ^ (2 : ℕ) * m1) * (a1 * (W + H)) :=
      mul_le_mul_of_nonneg_left hm1W (by positivity)
    _ = (14 * (W + H) * a2 ^ (2 : ℕ)) * (a1 * m1) := by ring
    _ ≤ (9 * W * a1 * a3) * (a1 * m1) :=
      mul_le_mul_of_nonneg_right hfirst' (mul_nonneg ha1.le hm1)
    _ = (W * a1 ^ (2 : ℕ)) * (9 * m1 * a3) := by ring
    _ ≤ (W * a1 ^ (2 : ℕ)) * (9 * m1 * m3) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ha3m3 (mul_nonneg (by norm_num) hm1))
        hfactor.le

/-- The exact reflected-budget zeroth-tail condition implies the completed upper susceptibility
gate. -/
theorem thetaCuspRelaxedFourthMomentConcentration_of_reflectedBudget
    (hfirst :
      16 * (thetaCuspAtomRawEvenMoment 0 1 +
          thetaCuspHigherHalfDensityBudget) *
          thetaCuspAtomRawEvenMoment 2 1 ≤
        45 * thetaCuspAtomRawEvenMoment 1 1 ^ (2 : ℕ)) :
    ThetaCuspRelaxedFourthMomentConcentration := by
  rw [ThetaCuspRelaxedFourthMomentConcentration]
  let H := thetaCuspHigherHalfDensityBudget
  let a0 := thetaCuspAtomRawEvenMoment 0 1
  let a1 := thetaCuspAtomRawEvenMoment 1 1
  let a2 := thetaCuspAtomRawEvenMoment 2 1
  let m0 := thetaCuspRawEvenMoment 0
  let m1 := thetaCuspRawEvenMoment 1
  let m2 := thetaCuspRawEvenMoment 2
  have ha1 : 0 < a1 := thetaCuspAtomRawEvenMoment_pos_of_nat_pos 1 (by norm_num)
  have ha2 : 0 ≤ a2 := thetaCuspAtomRawEvenMoment_nonneg 2 1
  have hm0 : 0 ≤ m0 := thetaCuspRawEvenMoment_nonneg 0
  have hm1 : 0 ≤ m1 := thetaCuspRawEvenMoment_nonneg 1
  have hm0Upper : m0 ≤ a0 + H := by
    simpa only [m0, a0, H] using
      thetaCuspRawEvenMoment_zero_le_first_add_higherHalfDensityBudget
  have ha1m1 : a1 ≤ m1 := by
    simpa only [a1, m1] using thetaCuspAtomRawEvenMoment_one_le_raw 1
  have hcross : m2 * a1 ≤ a2 * m1 := by
    simpa only [m1, m2, a1, a2] using
      thetaCuspRawFirst_rawEvenMoment_cross_le 1 1
  have hfirst' : 16 * (a0 + H) * a2 ≤ 45 * a1 ^ (2 : ℕ) := by
    simpa only [H, a0, a1, a2] using hfirst
  apply (mul_le_mul_iff_of_pos_left ha1).mp
  calc
    a1 * (16 * m0 * m2) = 16 * m0 * (m2 * a1) := by ring
    _ ≤ 16 * m0 * (a2 * m1) :=
      mul_le_mul_of_nonneg_left hcross (mul_nonneg (by norm_num) hm0)
    _ ≤ 16 * (a0 + H) * (a2 * m1) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hm0Upper (by norm_num))
        (mul_nonneg ha2 hm1)
    _ = (16 * (a0 + H) * a2) * m1 := by ring
    _ ≤ (45 * a1 ^ (2 : ℕ)) * m1 :=
      mul_le_mul_of_nonneg_right hfirst' hm1
    _ ≤ a1 * (45 * m1 ^ (2 : ℕ)) := by
      have hfactor : 0 ≤ 45 * a1 * m1 :=
        mul_nonneg (mul_nonneg (by norm_num) ha1.le) hm1
      convert mul_le_mul_of_nonneg_left ha1m1 hfactor using 1 <;> first | rfl | ring

/-- The two reflected-budget first-atom conditions discharge every real linear prime--Gamma
Hankel test. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_reflectedBudget
    (hupper :
      14 * (thetaCuspFirstAtomHalfDensityPairBudget +
          thetaCuspHigherHalfDensityBudget) *
          thetaCuspAtomRawEvenMoment 2 1 ^ (2 : ℕ) ≤
        9 * thetaCuspFirstAtomHalfDensityPairBudget *
          thetaCuspAtomRawEvenMoment 1 1 *
            thetaCuspAtomRawEvenMoment 3 1)
    (hrelaxed :
      16 * (thetaCuspAtomRawEvenMoment 0 1 +
          thetaCuspHigherHalfDensityBudget) *
          thetaCuspAtomRawEvenMoment 2 1 ≤
        45 * thetaCuspAtomRawEvenMoment 1 1 ^ (2 : ℕ)) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (Polynomial.C a + Polynomial.C b * Polynomial.X)).re :=
  forall_primeArchSourceTraceHankel_linear_nonneg_of_ratioSplit
    (thetaCuspUpperAdjacentRatioSeparation_of_reflectedBudget hupper)
    (thetaCuspRelaxedFourthMomentConcentration_of_reflectedBudget hrelaxed)

/-- RH-facing reflected-budget reduction.  Only the two finite first-atom inequalities and the
unchanged degree-two prime--Gamma tail remain. -/
theorem riemannHypothesis_of_reflectedBudget_of_primeArchDegreeTwoTail
    (hupper :
      14 * (thetaCuspFirstAtomHalfDensityPairBudget +
          thetaCuspHigherHalfDensityBudget) *
          thetaCuspAtomRawEvenMoment 2 1 ^ (2 : ℕ) ≤
        9 * thetaCuspFirstAtomHalfDensityPairBudget *
          thetaCuspAtomRawEvenMoment 1 1 *
            thetaCuspAtomRawEvenMoment 3 1)
    (hrelaxed :
      16 * (thetaCuspAtomRawEvenMoment 0 1 +
          thetaCuspHigherHalfDensityBudget) *
          thetaCuspAtomRawEvenMoment 2 1 ≤
        45 * thetaCuspAtomRawEvenMoment 1 1 ^ (2 : ℕ))
    (htail : PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative) :
    RiemannHypothesis :=
  riemannHypothesis_of_thetaCuspRatioSplit_of_primeArchDegreeTwoTail
    (thetaCuspUpperAdjacentRatioSeparation_of_reflectedBudget hupper)
    (thetaCuspRelaxedFourthMomentConcentration_of_reflectedBudget hrelaxed)
    htail

end

end RHTower
