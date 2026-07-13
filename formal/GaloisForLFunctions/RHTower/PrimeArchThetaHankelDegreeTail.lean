import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantRatioSplit
import GaloisForLFunctions.RHTower.PrimeArchThetaAllOrderCumulant
import GaloisForLFunctions.RHTower.PrimeArchHankelDeterminantCriterion
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailMomentLogConvex

/-!
# Theta discharge of the constant and linear prime--Gamma Hankel faces

The countable prime--Gamma source criterion asks for nonnegativity on every integer polynomial.
The constant face is unconditional, and the two theta-cusp ratio inequalities already force
nonnegativity on every real linear polynomial.  Consequently the genuinely remaining countable
tail starts at degree two.

This is a top-down interface reduction.  It does not assert the two theta-cusp ratio inequalities
or the degree-two-and-above tail positivity.
-/

open Polynomial

namespace RHTower

noncomputable section

/-- Source Hankel nonnegativity restricted to integer polynomials of degree at least two. -/
def PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative : Prop :=
  ∀ p : Polynomial ℤ, 2 ≤ p.natDegree →
    0 ≤ (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re

/-- The two theta-cusp ratio inequalities discharge every omitted constant or linear integer
test.  Thus positivity only on the degree-`>= 2` tail upgrades to the complete countable
prime--Gamma source cone. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_ratioSplit_of_degreeTwoTail
    (hupper : ThetaCuspUpperAdjacentRatioSeparation)
    (hrelaxed : ThetaCuspRelaxedFourthMomentConcentration)
    (htail : PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  by_cases hp : 2 ≤ p.natDegree
  · exact htail p hp
  · have hdeg : p.natDegree ≤ 1 := by omega
    have hdegree : p.degree ≤ 1 :=
      Polynomial.natDegree_le_iff_degree_le.mp hdeg
    have hpform := Polynomial.eq_X_add_C_of_degree_le_one hdegree
    have hmap := congrArg (Polynomial.map (Int.castRingHom ℝ)) hpform
    have hpoly : p.map (Int.castRingHom ℝ) =
        C ((p.coeff 0 : ℤ) : ℝ) + C ((p.coeff 1 : ℤ) : ℝ) * X := by
      simpa [add_comm] using hmap
    rw [hpoly]
    exact forall_primeArchSourceTraceHankel_linear_nonneg_of_ratioSplit
      hupper hrelaxed _ _

/-- **Degree-two-tail chain to RH.**  Two explicit source-pure theta moment-ratio inequalities,
together with prime--Gamma Hankel nonnegativity only for integer polynomials of degree at least
two, imply the Riemann hypothesis. -/
theorem riemannHypothesis_of_thetaCuspRatioSplit_of_primeArchDegreeTwoTail
    (hupper : ThetaCuspUpperAdjacentRatioSeparation)
    (hrelaxed : ThetaCuspRelaxedFourthMomentConcentration)
    (htail : PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_ratioSplit_of_degreeTwoTail
      hupper hrelaxed htail)

/-! ## Strict low block and the scalar determinant tail -/

/-- If both source ratio inequalities hold and at least one has strict margin, then the first
nonconstant (`2 x 2`) prime--Gamma moment determinant is strictly positive. -/
theorem det_primeArchSourceMomentHankelMatrix_two_pos_of_ratioSplit_of_one_strict
    (hupper : ThetaCuspUpperAdjacentRatioSeparation)
    (hrelaxed : ThetaCuspRelaxedFourthMomentConcentration)
    (hstrict :
      14 * thetaCuspRawEvenMoment 2 ^ 2 <
          9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 ∨
        16 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 <
          45 * thetaCuspRawEvenMoment 1 ^ 2) :
    0 < (primeArchSourceMomentHankelMatrix 2).det := by
  have hA : 0 ≤ 9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 -
      14 * thetaCuspRawEvenMoment 2 ^ 2 := by
    exact sub_nonneg.mpr hupper
  have hB : 0 ≤ 45 * thetaCuspRawEvenMoment 1 ^ 2 -
      16 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 := by
    exact sub_nonneg.mpr hrelaxed
  have h0 := thetaCuspRawEvenMoment_pos 0
  have h2 := thetaCuspRawEvenMoment_pos 2
  have hAw : 0 ≤ thetaCuspRawEvenMoment 0 *
      (9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 -
        14 * thetaCuspRawEvenMoment 2 ^ 2) := mul_nonneg h0.le hA
  have hBw : 0 ≤ thetaCuspRawEvenMoment 2 *
      (45 * thetaCuspRawEvenMoment 1 ^ 2 -
        16 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2) :=
    mul_nonneg h2.le hB
  have hsum : 0 < thetaCuspRawEvenMoment 0 *
        (9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 -
          14 * thetaCuspRawEvenMoment 2 ^ 2) +
      thetaCuspRawEvenMoment 2 *
        (45 * thetaCuspRawEvenMoment 1 ^ 2 -
          16 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2) := by
    rcases hstrict with hAstr | hBstr
    · have : 0 < thetaCuspRawEvenMoment 0 *
          (9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 -
            14 * thetaCuspRawEvenMoment 2 ^ 2) :=
        mul_pos h0 (sub_pos.mpr hAstr)
      linarith
    · have : 0 < thetaCuspRawEvenMoment 2 *
          (45 * thetaCuspRawEvenMoment 1 ^ 2 -
            16 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2) :=
        mul_pos h2 (sub_pos.mpr hBstr)
      linarith
  have hid := thetaCusp_ratioSplit_exact_identity
  have hraw : 0 <
      3 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
          thetaCuspRawEvenMoment 3 +
        15 * thetaCuspRawEvenMoment 1 ^ 2 * thetaCuspRawEvenMoment 2 -
        10 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ^ 2 := by
    nlinarith [hid]
  have hnorm : 0 <
      3 * thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 +
        15 * thetaCuspNormalizedEvenMoment 1 ^ 2 * thetaCuspNormalizedEvenMoment 2 -
        10 * thetaCuspNormalizedEvenMoment 2 ^ 2 := by
    simp only [thetaCuspNormalizedEvenMoment]
    field_simp [h0.ne']
    nlinarith [hraw]
  rw [det_primeArchSourceMomentHankelMatrix_two]
  have hscaled := normalizedPrimeArch_firstHankelMinor_scaled_eq_thetaCuspMoments
  nlinarith [hscaled]

/-- The genuinely cofinal scalar tail: strict positivity of one leading prime--Gamma moment
determinant in every size at least three. -/
def PrimeArchSourceMomentHankelDeterminantTailFromThreePositive : Prop :=
  ∀ n : ℕ, 3 ≤ n → 0 < (primeArchSourceMomentHankelMatrix n).det

/-- **Scalar determinant-tail chain to RH.**  The strict two-ratio low block discharges sizes
`0`, `1`, and `2`; only one scalar leading determinant in each size `n >= 3` remains. -/
theorem riemannHypothesis_of_strictThetaCuspRatioSplit_of_primeArchDeterminantTailFromThree
    (hupper : ThetaCuspUpperAdjacentRatioSeparation)
    (hrelaxed : ThetaCuspRelaxedFourthMomentConcentration)
    (hstrict :
      14 * thetaCuspRawEvenMoment 2 ^ 2 <
          9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 ∨
        16 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 <
          45 * thetaCuspRawEvenMoment 1 ^ 2)
    (htail : PrimeArchSourceMomentHankelDeterminantTailFromThreePositive) :
    RiemannHypothesis := by
  apply primeArchSourceMomentHankelDeterminantsPositive_iff_riemannHypothesis.mp
  intro n
  rcases lt_trichotomy n 2 with hn | rfl | hn
  · interval_cases n
    · simp
    · exact det_primeArchSourceMomentHankelMatrix_one_pos
  · exact det_primeArchSourceMomentHankelMatrix_two_pos_of_ratioSplit_of_one_strict
      hupper hrelaxed hstrict
  · exact htail n (by omega)

end

end RHTower
