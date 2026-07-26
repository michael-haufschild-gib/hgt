import GaloisForLFunctions.HTGeometry.PolynomialCoefficientSignMomentCone
import GaloisForLFunctions.RHTower.PrimeArchValuationSectorCones
import GaloisForLFunctions.RHTower.XiCenteredOrderFourteenSourcePositivity
import GaloisForLFunctions.RHTower.XiCenteredOrdersFifteenSixteenSourcePositivity
import GaloisForLFunctions.RHTower.XiCenteredOrdersSeventeenEighteenSourcePositivity

/-!
# Low-degree coefficient cones for the prime--Gamma source

The normalized prime--archimedean moments are unconditionally positive through index eighteen.
Therefore every integer polynomial of degree at most nine whose real self-convolution
coefficients are nonnegative has nonnegative prime--Gamma trace--Hankel value.

The exact fourteenth-power sector margin proves that moment thirteen strictly dominates moment
fourteen in absolute value. A separate centered order-fifteen corner exclusion proves moment
fourteen itself strictly positive. Centered order-sixteen and order-seventeen exclusions prove
positivity of moments fifteen and sixteen, closing the full degree-eight square-coefficient cone.
Centered order-eighteen and order-nineteen exclusions similarly close the full degree-nine cone.
-/

open Polynomial

namespace RHTower

noncomputable section

/-- Every reciprocal-square Xi atom retains more than the endpoint-radius fraction of its
fourteenth absolute power. -/
theorem re_xiZeroCopyReciprocalSquare_pow_fourteen_gt_two_over_fortyOne_norm_pow
    (q : XiZeroCopy) :
    (2 / 41 : ℝ) * ‖xiZeroCopyReciprocalSquare q‖ ^ 14 <
      (xiZeroCopyReciprocalSquare q ^ 14).re := by
  apply
    GaloisForLFunctions.HTGeometry.re_pow_fourteen_gt_two_over_fortyOne_norm_pow_of_sector
  · simpa only [xiThermalNode] using xiThermalNode_pos q
  · simpa only [xiThermalNode] using
      xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q

/-- The thirteenth normalized source moment exceeds the endpoint-radius fraction of its absolute
fourteenth mass. -/
theorem two_over_fortyOne_mul_xiShiftAbsoluteMass_thirteen_lt_normalizedPrimeArchMoment :
    (2 / 41 : ℝ) * xiShiftAbsoluteMass 13 <
      normalizedPrimeArchMoment 13 := by
  let q₀ : XiZeroCopy := Classical.choice nonempty_xiZeroCopy
  have hpow := summable_xiZeroCopyReciprocalSquare_pow 13
  have hleft :
      Summable (fun q : XiZeroCopy =>
        (2 / 41 : ℝ) * ‖xiZeroCopyReciprocalSquare q‖ ^ 14) :=
    (summable_xiShiftAbsoluteMass 13).mul_left (2 / 41 : ℝ)
  have hright :
      Summable (fun q : XiZeroCopy =>
        (xiZeroCopyReciprocalSquare q ^ 14).re) :=
    Complex.reCLM.summable hpow
  have hlt :
      (∑' q : XiZeroCopy,
          (2 / 41 : ℝ) * ‖xiZeroCopyReciprocalSquare q‖ ^ 14) <
        ∑' q : XiZeroCopy,
          (xiZeroCopyReciprocalSquare q ^ 14).re :=
    hleft.tsum_lt_tsum (i := q₀)
      (fun q =>
        (re_xiZeroCopyReciprocalSquare_pow_fourteen_gt_two_over_fortyOne_norm_pow
          q).le)
      (re_xiZeroCopyReciprocalSquare_pow_fourteen_gt_two_over_fortyOne_norm_pow q₀)
      hright
  rw [xiShiftAbsoluteMass, ← tsum_mul_left,
    normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment,
    ← tsum_xiZeroCopyReciprocalSquare_pow, Complex.re_tsum hpow]
  exact hlt

/-- The thirteenth normalized source moment strictly dominates the fourteenth in absolute value. -/
theorem abs_normalizedPrimeArchMoment_fourteen_lt_thirteen :
    |normalizedPrimeArchMoment 14| < normalizedPrimeArchMoment 13 := by
  exact
    (abs_normalizedPrimeArchMoment_add_le_xiShiftAbsoluteMass 13 1).trans_lt
      (by
        norm_num
        exact
          two_over_fortyOne_mul_xiShiftAbsoluteMass_thirteen_lt_normalizedPrimeArchMoment)

/-- Every normalized prime--archimedean source moment through index thirteen is strictly
positive. -/
theorem normalizedPrimeArchMoment_pos_of_le_thirteen
    (s : ℕ) (hs : s ≤ 13) :
    0 < normalizedPrimeArchMoment s := by
  by_cases hs12 : s ≤ 12
  · exact normalizedPrimeArchMoment_pos_of_le_twelve s hs12
  · have hs13 : s = 13 := by omega
    subst s
    have hmass : 0 < xiShiftAbsoluteMass 13 :=
      xiShiftAbsoluteMass_pos 13
    have hlower :=
      two_over_fortyOne_mul_xiShiftAbsoluteMass_thirteen_lt_normalizedPrimeArchMoment
    nlinarith

/-- Every normalized prime--archimedean source moment through index fourteen is strictly
positive. -/
theorem normalizedPrimeArchMoment_pos_of_le_fourteen
    (s : ℕ) (hs : s ≤ 14) :
    0 < normalizedPrimeArchMoment s := by
  by_cases hs13 : s ≤ 13
  · exact normalizedPrimeArchMoment_pos_of_le_thirteen s hs13
  · have hs14 : s = 14 := by omega
    subst s
    exact normalizedPrimeArchMoment_fourteen_pos

/-- Every normalized prime--archimedean source moment through index sixteen is strictly
positive. -/
theorem normalizedPrimeArchMoment_pos_of_le_sixteen
    (s : ℕ) (hs : s ≤ 16) :
    0 < normalizedPrimeArchMoment s := by
  by_cases hs14 : s ≤ 14
  · exact normalizedPrimeArchMoment_pos_of_le_fourteen s hs14
  · by_cases hs15 : s ≤ 15
    · have hsEq : s = 15 := by omega
      subst s
      exact normalizedPrimeArchMoment_fifteen_pos
    · have hsEq : s = 16 := by omega
      subst s
      exact normalizedPrimeArchMoment_sixteen_pos

/-- Every normalized prime--archimedean source moment through index eighteen is strictly
positive. -/
theorem normalizedPrimeArchMoment_pos_of_le_eighteen
    (s : ℕ) (hs : s ≤ 18) :
    0 < normalizedPrimeArchMoment s := by
  by_cases hs16 : s ≤ 16
  · exact normalizedPrimeArchMoment_pos_of_le_sixteen s hs16
  · by_cases hs17 : s ≤ 17
    · have hsEq : s = 17 := by omega
      subst s
      exact normalizedPrimeArchMoment_seventeen_pos
    · have hsEq : s = 18 := by omega
      subst s
      exact normalizedPrimeArchMoment_eighteen_pos

/-- Degree-at-most-six integer polynomials whose coefficients all have one weak sign. -/
def PrimeArchDegreeSixCoefficientSignCone (p : Polynomial ℤ) : Prop :=
  p.natDegree ≤ 6 ∧
    ((∀ k : ℕ, 0 ≤ p.coeff k) ∨ (∀ k : ℕ, p.coeff k ≤ 0))

/-- Degree-at-most-six integer polynomials whose real self-convolution coefficients are
nonnegative. -/
def PrimeArchDegreeSixSquareCoeffCone (p : Polynomial ℤ) : Prop :=
  p.natDegree ≤ 6 ∧
    HTGeometry.PolynomialSquareCoeffNonnegative
      (p.map (Int.castRingHom ℝ))

/-- Degree-at-most-seven integer polynomials whose real self-convolution coefficients are
nonnegative. -/
def PrimeArchDegreeSevenSquareCoeffCone (p : Polynomial ℤ) : Prop :=
  p.natDegree ≤ 7 ∧
    HTGeometry.PolynomialSquareCoeffNonnegative
      (p.map (Int.castRingHom ℝ))

/-- Degree-at-most-eight integer polynomials whose real self-convolution coefficients are
nonnegative. -/
def PrimeArchDegreeEightSquareCoeffCone (p : Polynomial ℤ) : Prop :=
  p.natDegree ≤ 8 ∧
    HTGeometry.PolynomialSquareCoeffNonnegative
      (p.map (Int.castRingHom ℝ))

/-- Degree-at-most-nine integer polynomials whose real self-convolution coefficients are
nonnegative. -/
def PrimeArchDegreeNineSquareCoeffCone (p : Polynomial ℤ) : Prop :=
  p.natDegree ≤ 9 ∧
    HTGeometry.PolynomialSquareCoeffNonnegative
      (p.map (Int.castRingHom ℝ))

/-- Degree-at-most-seven integer polynomials with nonnegative real self-convolution and an
endpoint coefficient dominated by the penultimate coefficient. -/
def PrimeArchDegreeSevenEndpointPairCone (p : Polynomial ℤ) : Prop :=
  p.natDegree ≤ 7 ∧
    HTGeometry.PolynomialSquareCoeffNonnegative
      (p.map (Int.castRingHom ℝ)) ∧
      ((p.map (Int.castRingHom ℝ)) ^ 2).coeff 14 ≤
        ((p.map (Int.castRingHom ℝ)) ^ 2).coeff 13

/-- The degree-six coefficient-sign cone maps into the corresponding real cone. -/
theorem polynomialCoeffwiseOneSign_map_intCast
    {p : Polynomial ℤ}
    (hp : (∀ k : ℕ, 0 ≤ p.coeff k) ∨ (∀ k : ℕ, p.coeff k ≤ 0)) :
    HTGeometry.PolynomialCoeffwiseOneSign
      (p.map (Int.castRingHom ℝ)) := by
  rcases hp with hp | hp
  · left
    intro k
    rw [Polynomial.coeff_map]
    change (0 : ℝ) ≤ (p.coeff k : ℝ)
    exact_mod_cast hp k
  · right
    intro k
    rw [Polynomial.coeff_map]
    change ((p.coeff k : ℤ) : ℝ) ≤ 0
    exact_mod_cast hp k

/-- The coefficient-sign cone maps into the square-coefficient cone. -/
theorem primeArchDegreeSixSquareCoeffCone_of_coefficientSignCone
    {p : Polynomial ℤ} (hp : PrimeArchDegreeSixCoefficientSignCone p) :
    PrimeArchDegreeSixSquareCoeffCone p :=
  ⟨hp.1, HTGeometry.polynomialSquareCoeffNonnegative_of_coeffwiseOneSign
    (polynomialCoeffwiseOneSign_map_intCast hp.2)⟩

/-- Every polynomial in the degree-six square-coefficient cone has nonnegative source
trace--Hankel value. -/
theorem re_primeArchSourceTraceHankel_nonneg_of_degreeSixSquareCoeffCone
    (p : Polynomial ℤ) (hp : PrimeArchDegreeSixSquareCoeffCone p) :
    0 ≤ (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re := by
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  apply
    HTGeometry.momentFunctional_sq_nonneg_of_squareCoeffNonnegative
      normalizedPrimeArchMoment
      ((Polynomial.natDegree_map_le).trans hp.1)
      hp.2
  intro k hk
  exact (normalizedPrimeArchMoment_pos_of_le_twelve k (by omega)).le

/-- Every polynomial in the degree-six coefficient-sign cone has nonnegative source
trace--Hankel value. -/
theorem re_primeArchSourceTraceHankel_nonneg_of_degreeSixCoefficientSignCone
    (p : Polynomial ℤ) (hp : PrimeArchDegreeSixCoefficientSignCone p) :
    0 ≤ (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re :=
  re_primeArchSourceTraceHankel_nonneg_of_degreeSixSquareCoeffCone p
    (primeArchDegreeSixSquareCoeffCone_of_coefficientSignCone hp)

/-- Every nonzero polynomial in the degree-six square-coefficient cone has strictly positive
source trace--Hankel value. -/
theorem re_primeArchSourceTraceHankel_pos_of_degreeSixSquareCoeffCone
    (p : Polynomial ℤ) (hp : PrimeArchDegreeSixSquareCoeffCone p)
    (hpne : p ≠ 0) :
    0 < (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re := by
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  apply
    HTGeometry.momentFunctional_sq_pos_of_squareCoeffNonnegative
      normalizedPrimeArchMoment
      ((Polynomial.natDegree_map_le).trans hp.1)
      hp.2
      ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr hpne)
  intro k hk
  exact normalizedPrimeArchMoment_pos_of_le_twelve k (by omega)

/-- Every nonzero polynomial in the degree-six coefficient-sign cone has strictly positive
source trace--Hankel value. -/
theorem re_primeArchSourceTraceHankel_pos_of_degreeSixCoefficientSignCone
    (p : Polynomial ℤ) (hp : PrimeArchDegreeSixCoefficientSignCone p)
    (hpne : p ≠ 0) :
    0 < (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re :=
  re_primeArchSourceTraceHankel_pos_of_degreeSixSquareCoeffCone p
    (primeArchDegreeSixSquareCoeffCone_of_coefficientSignCone hp) hpne

/-- Every degree-six square-coefficient test belongs to the degree-seven endpoint-pair cone. -/
theorem primeArchDegreeSevenEndpointPairCone_of_degreeSixSquareCoeffCone
    {p : Polynomial ℤ} (hp : PrimeArchDegreeSixSquareCoeffCone p) :
    PrimeArchDegreeSevenEndpointPairCone p := by
  let q : Polynomial ℝ := p.map (Int.castRingHom ℝ)
  have hqdegree : q.natDegree ≤ 6 :=
    (Polynomial.natDegree_map_le).trans hp.1
  have hq2degree : (q ^ 2).natDegree ≤ 12 := by
    rw [Polynomial.natDegree_pow]
    omega
  refine ⟨hp.1.trans (by omega), hp.2, ?_⟩
  have h14 : (q ^ 2).coeff 14 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (hq2degree.trans_lt (by omega))
  have h13 : (q ^ 2).coeff 13 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (hq2degree.trans_lt (by omega))
  change (q ^ 2).coeff 14 ≤ (q ^ 2).coeff 13
  rw [h14, h13]

/-- Every endpoint-pair test belongs to the full degree-seven square-coefficient cone. -/
theorem primeArchDegreeSevenSquareCoeffCone_of_endpointPair
    {p : Polynomial ℤ} (hp : PrimeArchDegreeSevenEndpointPairCone p) :
    PrimeArchDegreeSevenSquareCoeffCone p :=
  ⟨hp.1, hp.2.1⟩

/-- Every degree-six square-coefficient test belongs to the full degree-seven cone. -/
theorem primeArchDegreeSevenSquareCoeffCone_of_degreeSixSquareCoeffCone
    {p : Polynomial ℤ} (hp : PrimeArchDegreeSixSquareCoeffCone p) :
    PrimeArchDegreeSevenSquareCoeffCone p :=
  primeArchDegreeSevenSquareCoeffCone_of_endpointPair
    (primeArchDegreeSevenEndpointPairCone_of_degreeSixSquareCoeffCone hp)

/-- Every degree-seven square-coefficient test belongs to the degree-eight cone. -/
theorem primeArchDegreeEightSquareCoeffCone_of_degreeSevenSquareCoeffCone
    {p : Polynomial ℤ} (hp : PrimeArchDegreeSevenSquareCoeffCone p) :
    PrimeArchDegreeEightSquareCoeffCone p :=
  ⟨hp.1.trans (by omega), hp.2⟩

/-- Every degree-eight square-coefficient test belongs to the degree-nine cone. -/
theorem primeArchDegreeNineSquareCoeffCone_of_degreeEightSquareCoeffCone
    {p : Polynomial ℤ} (hp : PrimeArchDegreeEightSquareCoeffCone p) :
    PrimeArchDegreeNineSquareCoeffCone p :=
  ⟨hp.1.trans (by omega), hp.2⟩

/-- Every polynomial in the degree-seven square-coefficient cone has nonnegative source
trace--Hankel value. -/
theorem re_primeArchSourceTraceHankel_nonneg_of_degreeSevenSquareCoeffCone
    (p : Polynomial ℤ) (hp : PrimeArchDegreeSevenSquareCoeffCone p) :
    0 ≤ (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re := by
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  apply
    HTGeometry.momentFunctional_sq_nonneg_of_squareCoeffNonnegative
      normalizedPrimeArchMoment
      ((Polynomial.natDegree_map_le).trans hp.1)
      hp.2
  intro k hk
  exact (normalizedPrimeArchMoment_pos_of_le_fourteen k hk).le

/-- Every nonzero polynomial in the degree-seven square-coefficient cone has strictly positive
source trace--Hankel value. -/
theorem re_primeArchSourceTraceHankel_pos_of_degreeSevenSquareCoeffCone
    (p : Polynomial ℤ) (hp : PrimeArchDegreeSevenSquareCoeffCone p)
    (hpne : p ≠ 0) :
    0 < (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re := by
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  apply
    HTGeometry.momentFunctional_sq_pos_of_squareCoeffNonnegative
      normalizedPrimeArchMoment
      ((Polynomial.natDegree_map_le).trans hp.1)
      hp.2
      ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr hpne)
  intro k hk
  exact normalizedPrimeArchMoment_pos_of_le_fourteen k hk

/-- Every polynomial in the degree-eight square-coefficient cone has nonnegative source
trace--Hankel value. -/
theorem re_primeArchSourceTraceHankel_nonneg_of_degreeEightSquareCoeffCone
    (p : Polynomial ℤ) (hp : PrimeArchDegreeEightSquareCoeffCone p) :
    0 ≤ (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re := by
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  apply
    HTGeometry.momentFunctional_sq_nonneg_of_squareCoeffNonnegative
      normalizedPrimeArchMoment
      ((Polynomial.natDegree_map_le).trans hp.1)
      hp.2
  intro k hk
  exact (normalizedPrimeArchMoment_pos_of_le_sixteen k hk).le

/-- Every nonzero polynomial in the degree-eight square-coefficient cone has strictly positive
source trace--Hankel value. -/
theorem re_primeArchSourceTraceHankel_pos_of_degreeEightSquareCoeffCone
    (p : Polynomial ℤ) (hp : PrimeArchDegreeEightSquareCoeffCone p)
    (hpne : p ≠ 0) :
    0 < (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re := by
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  apply
    HTGeometry.momentFunctional_sq_pos_of_squareCoeffNonnegative
      normalizedPrimeArchMoment
      ((Polynomial.natDegree_map_le).trans hp.1)
      hp.2
      ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr hpne)
  intro k hk
  exact normalizedPrimeArchMoment_pos_of_le_sixteen k hk

/-- Every polynomial in the degree-nine square-coefficient cone has nonnegative source
trace--Hankel value. -/
theorem re_primeArchSourceTraceHankel_nonneg_of_degreeNineSquareCoeffCone
    (p : Polynomial ℤ) (hp : PrimeArchDegreeNineSquareCoeffCone p) :
    0 ≤ (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re := by
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  apply
    HTGeometry.momentFunctional_sq_nonneg_of_squareCoeffNonnegative
      normalizedPrimeArchMoment
      ((Polynomial.natDegree_map_le).trans hp.1)
      hp.2
  intro k hk
  exact (normalizedPrimeArchMoment_pos_of_le_eighteen k hk).le

/-- Every nonzero polynomial in the degree-nine square-coefficient cone has strictly positive
source trace--Hankel value. -/
theorem re_primeArchSourceTraceHankel_pos_of_degreeNineSquareCoeffCone
    (p : Polynomial ℤ) (hp : PrimeArchDegreeNineSquareCoeffCone p)
    (hpne : p ≠ 0) :
    0 < (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re := by
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  apply
    HTGeometry.momentFunctional_sq_pos_of_squareCoeffNonnegative
      normalizedPrimeArchMoment
      ((Polynomial.natDegree_map_le).trans hp.1)
      hp.2
      ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr hpne)
  intro k hk
  exact normalizedPrimeArchMoment_pos_of_le_eighteen k hk

/-- Every test in the degree-seven endpoint-pair cone has nonnegative source trace--Hankel
value. -/
theorem re_primeArchSourceTraceHankel_nonneg_of_degreeSevenEndpointPairCone
    (p : Polynomial ℤ) (hp : PrimeArchDegreeSevenEndpointPairCone p) :
    0 ≤ (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re :=
  re_primeArchSourceTraceHankel_nonneg_of_degreeSevenSquareCoeffCone p
    (primeArchDegreeSevenSquareCoeffCone_of_endpointPair hp)

/-- Complement of the unconditional degree-six coefficient-sign cone. -/
def PrimeArchDegreeSixCoefficientSignResidual (p : Polynomial ℤ) : Prop :=
  ¬ PrimeArchDegreeSixCoefficientSignCone p

/-- Complement of the unconditional degree-six square-coefficient cone. -/
def PrimeArchDegreeSixSquareCoeffResidual (p : Polynomial ℤ) : Prop :=
  ¬ PrimeArchDegreeSixSquareCoeffCone p

/-- Complement of the unconditional degree-seven square-coefficient cone. -/
def PrimeArchDegreeSevenSquareCoeffResidual (p : Polynomial ℤ) : Prop :=
  ¬ PrimeArchDegreeSevenSquareCoeffCone p

/-- Complement of the unconditional degree-eight square-coefficient cone. -/
def PrimeArchDegreeEightSquareCoeffResidual (p : Polynomial ℤ) : Prop :=
  ¬ PrimeArchDegreeEightSquareCoeffCone p

/-- Complement of the unconditional degree-nine square-coefficient cone. -/
def PrimeArchDegreeNineSquareCoeffResidual (p : Polynomial ℤ) : Prop :=
  ¬ PrimeArchDegreeNineSquareCoeffCone p

/-- Complement of the unconditional degree-seven endpoint-pair cone. -/
def PrimeArchDegreeSevenEndpointPairResidual (p : Polynomial ℤ) : Prop :=
  ¬ PrimeArchDegreeSevenEndpointPairCone p

/-- A degree-seven endpoint-pair test with a large penultimate coefficient. -/
def primeArchDegreeSevenEndpointPolynomial : Polynomial ℤ :=
  X ^ 7 + C 2 + C 12 * X ^ 6

/-- The endpoint-pair test has exact degree seven. -/
theorem primeArchDegreeSevenEndpointPolynomial_natDegree :
    primeArchDegreeSevenEndpointPolynomial.natDegree = 7 := by
  let lower : Polynomial ℤ := C 2 + C 12 * X ^ 6
  have hlow : lower.natDegree < 7 := by
    apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
    rw [max_lt_iff]
    constructor
    · simp
    · rw [Polynomial.natDegree_C_mul_X_pow 6 12 (by norm_num)]
      omega
  have hlow' : lower.natDegree < (X ^ 7 : Polynomial ℤ).natDegree := by
    simpa only [Polynomial.natDegree_X_pow] using hlow
  unfold primeArchDegreeSevenEndpointPolynomial
  rw [add_assoc]
  change (X ^ 7 + lower).natDegree = 7
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlow',
    Polynomial.natDegree_X_pow]

theorem primeArchDegreeSevenEndpointPolynomial_coeff_nonneg
    (k : ℕ) :
    0 ≤ primeArchDegreeSevenEndpointPolynomial.coeff k := by
  cases k with
  | zero =>
      norm_num [primeArchDegreeSevenEndpointPolynomial]
  | succ k =>
      simp [primeArchDegreeSevenEndpointPolynomial, coeff_add, coeff_X_pow]
      split_ifs <;> norm_num

/-- Exact self-convolution of the endpoint-pair test. -/
theorem primeArchDegreeSevenEndpointPolynomial_map_sq :
    (primeArchDegreeSevenEndpointPolynomial.map
      (Int.castRingHom ℝ)) ^ 2 =
        X ^ 14 + C 24 * X ^ 13 + C 144 * X ^ 12 +
          C 4 * X ^ 7 + C 48 * X ^ 6 + C 4 := by
  simp [primeArchDegreeSevenEndpointPolynomial,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.C_ofNat]
  ring

/-- The degree-seven test belongs to the endpoint-pair cone. -/
theorem primeArchDegreeSevenEndpointPolynomial_mem :
    PrimeArchDegreeSevenEndpointPairCone
      primeArchDegreeSevenEndpointPolynomial := by
  constructor
  · rw [primeArchDegreeSevenEndpointPolynomial_natDegree]
  constructor
  · apply HTGeometry.polynomialSquareCoeffNonnegative_of_coeffwiseOneSign
    exact polynomialCoeffwiseOneSign_map_intCast
      (Or.inl primeArchDegreeSevenEndpointPolynomial_coeff_nonneg)
  · rw [primeArchDegreeSevenEndpointPolynomial_map_sq]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    norm_num

/-- The endpoint-pair test is not in the earlier degree-six square-coefficient cone. -/
theorem primeArchDegreeSevenEndpointPolynomial_not_degreeSixSquareCoeff :
    ¬ PrimeArchDegreeSixSquareCoeffCone
      primeArchDegreeSevenEndpointPolynomial := by
  intro h
  exact (not_le_of_gt (by
    rw [primeArchDegreeSevenEndpointPolynomial_natDegree]
    omega)) h.1

/-- The new degree-seven test has nonnegative prime--Gamma source trace--Hankel value. -/
theorem re_primeArchSourceTraceHankel_primeArchDegreeSevenEndpointPolynomial_nonneg :
    0 ≤
      (primeArchSourceTraceHankel
        (primeArchDegreeSevenEndpointPolynomial.map
          (Int.castRingHom ℝ))).re :=
  re_primeArchSourceTraceHankel_nonneg_of_degreeSevenEndpointPairCone
    primeArchDegreeSevenEndpointPolynomial
    primeArchDegreeSevenEndpointPolynomial_mem

/-- A genuine degree-eight square-coefficient test with a large penultimate coefficient. -/
def primeArchDegreeEightSquareCoeffPolynomial : Polynomial ℤ :=
  X ^ 8 + C 2 + C 12 * X ^ 7

/-- The degree-eight square-coefficient test has exact degree eight. -/
theorem primeArchDegreeEightSquareCoeffPolynomial_natDegree :
    primeArchDegreeEightSquareCoeffPolynomial.natDegree = 8 := by
  let lower : Polynomial ℤ := C 2 + C 12 * X ^ 7
  have hlow : lower.natDegree < 8 := by
    apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
    rw [max_lt_iff]
    constructor
    · simp
    · rw [Polynomial.natDegree_C_mul_X_pow 7 12 (by norm_num)]
      omega
  have hlow' : lower.natDegree < (X ^ 8 : Polynomial ℤ).natDegree := by
    simpa only [Polynomial.natDegree_X_pow] using hlow
  unfold primeArchDegreeEightSquareCoeffPolynomial
  rw [add_assoc]
  change (X ^ 8 + lower).natDegree = 8
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlow',
    Polynomial.natDegree_X_pow]

theorem primeArchDegreeEightSquareCoeffPolynomial_coeff_nonneg
    (k : ℕ) :
    0 ≤ primeArchDegreeEightSquareCoeffPolynomial.coeff k := by
  cases k with
  | zero =>
      norm_num [primeArchDegreeEightSquareCoeffPolynomial]
  | succ k =>
      simp [primeArchDegreeEightSquareCoeffPolynomial, coeff_add, coeff_X_pow]
      split_ifs <;> norm_num

/-- The degree-eight test belongs to the full square-coefficient cone. -/
theorem primeArchDegreeEightSquareCoeffPolynomial_mem :
    PrimeArchDegreeEightSquareCoeffCone
      primeArchDegreeEightSquareCoeffPolynomial := by
  constructor
  · rw [primeArchDegreeEightSquareCoeffPolynomial_natDegree]
  · apply HTGeometry.polynomialSquareCoeffNonnegative_of_coeffwiseOneSign
    exact polynomialCoeffwiseOneSign_map_intCast
      (Or.inl primeArchDegreeEightSquareCoeffPolynomial_coeff_nonneg)

/-- The degree-eight test is not in the preceding degree-seven square-coefficient cone. -/
theorem primeArchDegreeEightSquareCoeffPolynomial_not_degreeSevenSquareCoeff :
    ¬ PrimeArchDegreeSevenSquareCoeffCone
      primeArchDegreeEightSquareCoeffPolynomial := by
  intro h
  exact (not_le_of_gt (by
    rw [primeArchDegreeEightSquareCoeffPolynomial_natDegree]
    omega)) h.1

/-- The genuine degree-eight test has nonnegative prime--Gamma source trace--Hankel value. -/
theorem re_primeArchSourceTraceHankel_primeArchDegreeEightSquareCoeffPolynomial_nonneg :
    0 ≤
      (primeArchSourceTraceHankel
        (primeArchDegreeEightSquareCoeffPolynomial.map
          (Int.castRingHom ℝ))).re :=
  re_primeArchSourceTraceHankel_nonneg_of_degreeEightSquareCoeffCone
    primeArchDegreeEightSquareCoeffPolynomial
    primeArchDegreeEightSquareCoeffPolynomial_mem

/-- A genuine degree-nine square-coefficient test with a large penultimate coefficient. -/
def primeArchDegreeNineSquareCoeffPolynomial : Polynomial ℤ :=
  X ^ 9 + C 2 + C 12 * X ^ 8

/-- The degree-nine square-coefficient test has exact degree nine. -/
theorem primeArchDegreeNineSquareCoeffPolynomial_natDegree :
    primeArchDegreeNineSquareCoeffPolynomial.natDegree = 9 := by
  let lower : Polynomial ℤ := C 2 + C 12 * X ^ 8
  have hlow : lower.natDegree < 9 := by
    apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
    rw [max_lt_iff]
    constructor
    · simp
    · rw [Polynomial.natDegree_C_mul_X_pow 8 12 (by norm_num)]
      omega
  have hlow' : lower.natDegree < (X ^ 9 : Polynomial ℤ).natDegree := by
    simpa only [Polynomial.natDegree_X_pow] using hlow
  unfold primeArchDegreeNineSquareCoeffPolynomial
  rw [add_assoc]
  change (X ^ 9 + lower).natDegree = 9
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlow',
    Polynomial.natDegree_X_pow]

theorem primeArchDegreeNineSquareCoeffPolynomial_coeff_nonneg
    (k : ℕ) :
    0 ≤ primeArchDegreeNineSquareCoeffPolynomial.coeff k := by
  cases k with
  | zero =>
      norm_num [primeArchDegreeNineSquareCoeffPolynomial]
  | succ k =>
      simp [primeArchDegreeNineSquareCoeffPolynomial, coeff_add, coeff_X_pow]
      split_ifs <;> norm_num

/-- The degree-nine test belongs to the full square-coefficient cone. -/
theorem primeArchDegreeNineSquareCoeffPolynomial_mem :
    PrimeArchDegreeNineSquareCoeffCone
      primeArchDegreeNineSquareCoeffPolynomial := by
  constructor
  · rw [primeArchDegreeNineSquareCoeffPolynomial_natDegree]
  · apply HTGeometry.polynomialSquareCoeffNonnegative_of_coeffwiseOneSign
    exact polynomialCoeffwiseOneSign_map_intCast
      (Or.inl primeArchDegreeNineSquareCoeffPolynomial_coeff_nonneg)

/-- The degree-nine test is not in the preceding degree-eight square-coefficient cone. -/
theorem primeArchDegreeNineSquareCoeffPolynomial_not_degreeEightSquareCoeff :
    ¬ PrimeArchDegreeEightSquareCoeffCone
      primeArchDegreeNineSquareCoeffPolynomial := by
  intro h
  exact (not_le_of_gt (by
    rw [primeArchDegreeNineSquareCoeffPolynomial_natDegree]
    omega)) h.1

/-- The genuine degree-nine test has nonnegative prime--Gamma source trace--Hankel value. -/
theorem re_primeArchSourceTraceHankel_primeArchDegreeNineSquareCoeffPolynomial_nonneg :
    0 ≤
      (primeArchSourceTraceHankel
        (primeArchDegreeNineSquareCoeffPolynomial.map
          (Int.castRingHom ℝ))).re :=
  re_primeArchSourceTraceHankel_nonneg_of_degreeNineSquareCoeffCone
    primeArchDegreeNineSquareCoeffPolynomial
    primeArchDegreeNineSquareCoeffPolynomial_mem

/-- Concrete mixed-sign integer test in the square-coefficient cone. -/
def primeArchMixedSignSquareCoeffPolynomial : Polynomial ℤ :=
  C 1 * X ^ 0 + C 2 * X - C 1 * X ^ 2 + C 2 * X ^ 3 + C 1 * X ^ 4

/-- The concrete mixed-sign test maps to the universal five-term family at scale one. -/
theorem primeArchMixedSignSquareCoeffPolynomial_map :
    primeArchMixedSignSquareCoeffPolynomial.map (Int.castRingHom ℝ) =
      HTGeometry.mixedSignSquareCoeffPolynomial 1 := by
  simp [primeArchMixedSignSquareCoeffPolynomial,
    HTGeometry.mixedSignSquareCoeffPolynomial, Polynomial.C_ofNat]

/-- The concrete mixed-sign test has degree four. -/
theorem primeArchMixedSignSquareCoeffPolynomial_natDegree :
    primeArchMixedSignSquareCoeffPolynomial.natDegree = 4 := by
  unfold primeArchMixedSignSquareCoeffPolynomial
  compute_degree!

/-- The concrete mixed-sign test is nonzero. -/
theorem primeArchMixedSignSquareCoeffPolynomial_ne_zero :
    primeArchMixedSignSquareCoeffPolynomial ≠ 0 := by
  intro h
  have hdegree := primeArchMixedSignSquareCoeffPolynomial_natDegree
  rw [h] at hdegree
  norm_num at hdegree

/-- The concrete mixed-sign test belongs to the unconditional degree-six square-coefficient
cone. -/
theorem primeArchMixedSignSquareCoeffPolynomial_mem :
    PrimeArchDegreeSixSquareCoeffCone
      primeArchMixedSignSquareCoeffPolynomial := by
  constructor
  · rw [primeArchMixedSignSquareCoeffPolynomial_natDegree]
    omega
  · rw [primeArchMixedSignSquareCoeffPolynomial_map]
    exact HTGeometry.polynomialSquareCoeffNonnegative_mixedSign 1

/-- The concrete square-coefficient test is genuinely mixed-sign. -/
theorem primeArchMixedSignSquareCoeffPolynomial_not_coefficientSign :
    ¬ PrimeArchDegreeSixCoefficientSignCone
      primeArchMixedSignSquareCoeffPolynomial := by
  intro h
  have hmapped := polynomialCoeffwiseOneSign_map_intCast h.2
  rw [primeArchMixedSignSquareCoeffPolynomial_map] at hmapped
  exact HTGeometry.not_polynomialCoeffwiseOneSign_mixedSign (by norm_num) hmapped

/-- The concrete mixed-sign test has strictly positive prime--Gamma source trace--Hankel
value. -/
theorem re_primeArchSourceTraceHankel_primeArchMixedSignSquareCoeffPolynomial_pos :
    0 <
      (primeArchSourceTraceHankel
        (primeArchMixedSignSquareCoeffPolynomial.map
          (Int.castRingHom ℝ))).re := by
  apply re_primeArchSourceTraceHankel_pos_of_degreeSixSquareCoeffCone
    primeArchMixedSignSquareCoeffPolynomial
    primeArchMixedSignSquareCoeffPolynomial_mem
  exact primeArchMixedSignSquareCoeffPolynomial_ne_zero

end

end RHTower
