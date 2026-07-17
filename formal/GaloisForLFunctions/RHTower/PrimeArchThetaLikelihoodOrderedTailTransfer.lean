import GaloisForLFunctions.RHTower.PrimeArchThetaSourceAtomDomination
import GaloisForLFunctions.RHTower.PrimeArchThetaAtomLikelihoodRatio

/-!
# Single-loss transfer from the first theta atom to the completed source

Write the completed even theta moments as `m_j = a_j + r_j`, where `a_j` is the first-atom
moment.  Coordinatewise domination gives `m_j ≤ c a_j`, with `c = 3005 / 2997`.  Applying
that enclosure independently to two factors costs `c²`.

The source supplies more: its exact monotone-likelihood-ratio order gives
`m₂ a₁ ≤ a₂ m₁`.  Combining this cross inequality with one coordinatewise enclosure transfers
each of the two live susceptibility gates with only one factor `c`.  The result is source-pure and
unconditional; the two sharpened first-atom inequalities themselves remain separate analytic
inputs.
-/

open Polynomial

namespace RHTower

noncomputable section

private theorem lower_ratio_single_loss
    {c a1 a2 a3 m1 m2 m3 : ℝ}
    (hc : 0 < c) (ha1 : 0 < a1)
    (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3)
    (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hcross : m2 * a1 ≤ a2 * m1)
    (hm1_le : m1 ≤ c * a1) (ha3_le : a3 ≤ m3)
    (hfirst : 14 * c * a2 ^ 2 ≤ 9 * a1 * a3) :
    14 * m2 ^ 2 ≤ 9 * m1 * m3 := by
  have hm1sq_le : m1 ^ 2 ≤ (c * a1) * m1 := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hm1_le hm1
  have hsq : (m2 * a1) ^ 2 ≤ (a2 * m1) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hm2 ha1.le) (mul_nonneg ha2 hm1)).2 hcross
  have hfactor : 0 < c * a1 ^ 2 := mul_pos hc (sq_pos_of_pos ha1)
  apply (mul_le_mul_iff_of_pos_left hfactor).mp
  calc
    (c * a1 ^ 2) * (14 * m2 ^ 2) =
        (14 * c) * (m2 * a1) ^ 2 := by ring
    _ ≤ (14 * c) * (a2 * m1) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (14 * c * a2 ^ 2) * m1 ^ 2 := by ring
    _ ≤ (9 * a1 * a3) * m1 ^ 2 := by
      exact mul_le_mul_of_nonneg_right hfirst (sq_nonneg m1)
    _ ≤ (9 * a1 * a3) * ((c * a1) * m1) := by
      exact mul_le_mul_of_nonneg_left hm1sq_le
        (mul_nonneg (mul_nonneg (by positivity) ha1.le) ha3)
    _ = (9 * c * a1 ^ 2 * m1) * a3 := by ring
    _ ≤ (9 * c * a1 ^ 2 * m1) * m3 := by
      exact mul_le_mul_of_nonneg_left ha3_le
        (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hc.le)
          (sq_nonneg a1)) hm1)
    _ = (c * a1 ^ 2) * (9 * m1 * m3) := by ring

private theorem upper_ratio_single_loss
    {c a0 a1 a2 m0 m1 m2 : ℝ}
    (hc : 0 < c) (ha1 : 0 < a1)
    (ha2 : 0 ≤ a2)
    (hm0 : 0 ≤ m0) (hm1 : 0 ≤ m1)
    (hcross : m2 * a1 ≤ a2 * m1)
    (hm0_le : m0 ≤ c * a0) (ha1_le : a1 ≤ m1)
    (hfirst : 16 * c * a0 * a2 ≤ 45 * a1 ^ 2) :
    16 * m0 * m2 ≤ 45 * m1 ^ 2 := by
  apply (mul_le_mul_iff_of_pos_left ha1).mp
  calc
    a1 * (16 * m0 * m2) = 16 * m0 * (m2 * a1) := by ring
    _ ≤ 16 * m0 * (a2 * m1) := by
      exact mul_le_mul_of_nonneg_left hcross (mul_nonneg (by positivity) hm0)
    _ ≤ 16 * (c * a0) * (a2 * m1) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hm0_le (by positivity))
        (mul_nonneg ha2 hm1)
    _ = (16 * c * a0 * a2) * m1 := by ring
    _ ≤ (45 * a1 ^ 2) * m1 := by
      exact mul_le_mul_of_nonneg_right hfirst hm1
    _ ≤ a1 * (45 * m1 ^ 2) := by
      have h := mul_le_mul_of_nonneg_left ha1_le
        (mul_nonneg (mul_nonneg (by positivity) ha1.le) hm1)
      nlinarith

/-- Adjacent relative-tail weights are ordered in division-free form. -/
theorem thetaCuspHigherFirst_relativeTail_adjacent (k : ℕ) :
    thetaCuspHigherAtomRawEvenMoment (k + 1) *
        thetaCuspAtomRawEvenMoment k 1 ≤
      thetaCuspAtomRawEvenMoment (k + 1) 1 *
        thetaCuspHigherAtomRawEvenMoment k :=
  thetaCuspHigherFirst_rawEvenMoment_cross_le k 1

/-- The full first/second-moment cross inequality inherited from the exact likelihood order of
the higher theta tail relative to the first atom. -/
private theorem thetaCusp_full_cross_le :
    thetaCuspRawEvenMoment 2 * thetaCuspAtomRawEvenMoment 1 1 ≤
      thetaCuspAtomRawEvenMoment 2 1 * thetaCuspRawEvenMoment 1 := by
  have htail := thetaCuspHigherFirst_rawEvenMoment_cross_le 1 1
  norm_num at htail
  rw [thetaCuspRawEvenMoment_eq_one_add_higher 2,
    thetaCuspRawEvenMoment_eq_one_add_higher 1]
  nlinarith

/-- Likelihood order removes one enclosure loss from the first-atom sufficient condition for the
upper adjacent-ratio separation gate. -/
theorem thetaCuspUpperAdjacentRatioSeparation_of_first_atom_singleLoss
    (hfirst :
      14 * (3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 2 1 ^ 2 ≤
        9 * thetaCuspAtomRawEvenMoment 1 1 *
          thetaCuspAtomRawEvenMoment 3 1) :
    ThetaCuspUpperAdjacentRatioSeparation := by
  rw [ThetaCuspUpperAdjacentRatioSeparation]
  exact lower_ratio_single_loss
    (c := (3005 / 2997 : ℝ))
    (a1 := thetaCuspAtomRawEvenMoment 1 1)
    (a2 := thetaCuspAtomRawEvenMoment 2 1)
    (a3 := thetaCuspAtomRawEvenMoment 3 1)
    (m1 := thetaCuspRawEvenMoment 1)
    (m2 := thetaCuspRawEvenMoment 2)
    (m3 := thetaCuspRawEvenMoment 3)
    (by norm_num) (thetaCuspAtomRawEvenMoment_pos_of_nat_pos 1 (by norm_num))
    (thetaCuspAtomRawEvenMoment_nonneg 2 1)
    (thetaCuspAtomRawEvenMoment_nonneg 3 1)
    (thetaCuspRawEvenMoment_nonneg 1)
    (thetaCuspRawEvenMoment_nonneg 2)
    thetaCusp_full_cross_le
    (thetaCuspRawEvenMoment_le_first_atom_factor 1)
    (thetaCuspAtomRawEvenMoment_one_le_raw 3)
    hfirst

/-- Likelihood order removes one enclosure loss from the first-atom sufficient condition for the
relaxed fourth-moment concentration gate. -/
theorem thetaCuspRelaxedFourthMomentConcentration_of_first_atom_singleLoss
    (hfirst :
      16 * (3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 0 1 *
          thetaCuspAtomRawEvenMoment 2 1 ≤
        45 * thetaCuspAtomRawEvenMoment 1 1 ^ 2) :
    ThetaCuspRelaxedFourthMomentConcentration := by
  rw [ThetaCuspRelaxedFourthMomentConcentration]
  exact upper_ratio_single_loss
    (c := (3005 / 2997 : ℝ))
    (a0 := thetaCuspAtomRawEvenMoment 0 1)
    (a1 := thetaCuspAtomRawEvenMoment 1 1)
    (a2 := thetaCuspAtomRawEvenMoment 2 1)
    (m0 := thetaCuspRawEvenMoment 0)
    (m1 := thetaCuspRawEvenMoment 1)
    (m2 := thetaCuspRawEvenMoment 2)
    (by norm_num) (thetaCuspAtomRawEvenMoment_pos_of_nat_pos 1 (by norm_num))
    (thetaCuspAtomRawEvenMoment_nonneg 2 1)
    (thetaCuspRawEvenMoment_nonneg 0)
    (thetaCuspRawEvenMoment_nonneg 1)
    thetaCusp_full_cross_le
    (thetaCuspRawEvenMoment_le_first_atom_factor 0)
    (thetaCuspAtomRawEvenMoment_one_le_raw 1)
    hfirst

/-- The two one-loss first-atom conditions discharge every real linear prime--Gamma Hankel test. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_first_atom_singleLoss
    (hupper :
      14 * (3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 2 1 ^ 2 ≤
        9 * thetaCuspAtomRawEvenMoment 1 1 *
          thetaCuspAtomRawEvenMoment 3 1)
    (hrelaxed :
      16 * (3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 0 1 *
          thetaCuspAtomRawEvenMoment 2 1 ≤
        45 * thetaCuspAtomRawEvenMoment 1 1 ^ 2) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re :=
  forall_primeArchSourceTraceHankel_linear_nonneg_of_ratioSplit
    (thetaCuspUpperAdjacentRatioSeparation_of_first_atom_singleLoss hupper)
    (thetaCuspRelaxedFourthMomentConcentration_of_first_atom_singleLoss hrelaxed)

/-- Exact RH-facing form of the improvement: the two one-loss first-atom conditions, together
with the unchanged degree-two prime--Gamma tail, imply the Riemann hypothesis. -/
theorem riemannHypothesis_of_first_atom_singleLoss_of_primeArchDegreeTwoTail
    (hupper :
      14 * (3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 2 1 ^ 2 ≤
        9 * thetaCuspAtomRawEvenMoment 1 1 *
          thetaCuspAtomRawEvenMoment 3 1)
    (hrelaxed :
      16 * (3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 0 1 *
          thetaCuspAtomRawEvenMoment 2 1 ≤
        45 * thetaCuspAtomRawEvenMoment 1 1 ^ 2)
    (htail : PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative) :
    RiemannHypothesis :=
  riemannHypothesis_of_thetaCuspRatioSplit_of_primeArchDegreeTwoTail
    (thetaCuspUpperAdjacentRatioSeparation_of_first_atom_singleLoss hupper)
    (thetaCuspRelaxedFourthMomentConcentration_of_first_atom_singleLoss hrelaxed)
    htail

end

end RHTower
