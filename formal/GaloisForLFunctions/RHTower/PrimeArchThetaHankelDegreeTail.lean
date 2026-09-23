import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantRatioSplit
import GaloisForLFunctions.RHTower.PrimeArchThetaAllOrderCumulant
import GaloisForLFunctions.RHTower.PrimeArchHankelDeterminantCriterion
import GaloisForLFunctions.RHTower.PrimeArchMomentMeasureRH
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailMomentLogConvex
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-!
# Theta discharge of the constant and linear prime--Gamma Hankel faces

The countable prime--Gamma source criterion asks for nonnegativity on every integer polynomial.
The constant face is unconditional, and the two theta-cusp ratio inequalities force
nonnegativity on every real linear polynomial.  More strongly, the quadratic degree-raising
identity at the end of this file proves that positivity above any fixed polynomial degree already
forces all omitted degrees and hence RH.  The ratio inputs remain useful quantitative low-block
relations but are not hypotheses of the completed degree-tail criterion.
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
      14 * thetaCuspRawEvenMoment 2 ^ (2 : ℕ) <
          9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 ∨
        16 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 <
          45 * thetaCuspRawEvenMoment 1 ^ (2 : ℕ)) :
    0 < (primeArchSourceMomentHankelMatrix 2).det := by
  have hA : 0 ≤ 9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 -
      14 * thetaCuspRawEvenMoment 2 ^ (2 : ℕ) := by
    exact sub_nonneg.mpr hupper
  have hB : 0 ≤ 45 * thetaCuspRawEvenMoment 1 ^ (2 : ℕ) -
      16 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 := by
    exact sub_nonneg.mpr hrelaxed
  have h0 := thetaCuspRawEvenMoment_pos 0
  have h2 := thetaCuspRawEvenMoment_pos 2
  have hAw : 0 ≤ thetaCuspRawEvenMoment 0 *
      (9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 -
        14 * thetaCuspRawEvenMoment 2 ^ (2 : ℕ)) := mul_nonneg h0.le hA
  have hBw : 0 ≤ thetaCuspRawEvenMoment 2 *
      (45 * thetaCuspRawEvenMoment 1 ^ (2 : ℕ) -
        16 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2) :=
    mul_nonneg h2.le hB
  have hsum : 0 < thetaCuspRawEvenMoment 0 *
        (9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 -
          14 * thetaCuspRawEvenMoment 2 ^ (2 : ℕ)) +
      thetaCuspRawEvenMoment 2 *
        (45 * thetaCuspRawEvenMoment 1 ^ (2 : ℕ) -
          16 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2) := by
    rcases hstrict with hAstr | hBstr
    · have : 0 < thetaCuspRawEvenMoment 0 *
          (9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 -
            14 * thetaCuspRawEvenMoment 2 ^ (2 : ℕ)) :=
        mul_pos h0 (sub_pos.mpr hAstr)
      linarith
    · have : 0 < thetaCuspRawEvenMoment 2 *
          (45 * thetaCuspRawEvenMoment 1 ^ (2 : ℕ) -
            16 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2) :=
        mul_pos h2 (sub_pos.mpr hBstr)
      linarith
  have hid := thetaCusp_ratioSplit_exact_identity
  have hraw : 0 <
      3 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
          thetaCuspRawEvenMoment 3 +
        15 * thetaCuspRawEvenMoment 1 ^ (2 : ℕ) * thetaCuspRawEvenMoment 2 -
        10 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ^ (2 : ℕ) := by
    nlinarith [hid]
  have hnorm : 0 <
      3 * thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 +
        15 * thetaCuspNormalizedEvenMoment 1 ^ (2 : ℕ) * thetaCuspNormalizedEvenMoment 2 -
        10 * thetaCuspNormalizedEvenMoment 2 ^ (2 : ℕ) := by
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

/-- RH discharges the complete scalar determinant tail from size three onward. -/
theorem primeArchSourceMomentHankelDeterminantTailFromThreePositive_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    PrimeArchSourceMomentHankelDeterminantTailFromThreePositive := by
  intro n _
  exact
    (primeArchSourceMomentHankelDeterminantsPositive_iff_riemannHypothesis.2 hRH) n

/-- **Scalar determinant-tail chain to RH.**  The strict two-ratio low block discharges sizes
`0`, `1`, and `2`; only one scalar leading determinant in each size `n >= 3` remains. -/
theorem riemannHypothesis_of_strictThetaCuspRatioSplit_of_primeArchDeterminantTailFromThree
    (hupper : ThetaCuspUpperAdjacentRatioSeparation)
    (hrelaxed : ThetaCuspRelaxedFourthMomentConcentration)
    (hstrict :
      14 * thetaCuspRawEvenMoment 2 ^ (2 : ℕ) <
          9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 ∨
        16 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 <
          45 * thetaCuspRawEvenMoment 1 ^ (2 : ℕ))
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

namespace RHTower

noncomputable section

open Polynomial Filter Topology
open HTGeometry

/-! ## Completion of every fixed polynomial-degree tail -/

/-- Polarization after a real scalar dilation: the two opposite high-degree perturbations cancel
all cross terms and retain only the two diagonal trace--Hankel values. -/
theorem primeArchSourceTraceHankel_smul_add_sub_re
    (c : ℝ) (p q : Polynomial ℝ) :
    (primeArchSourceTraceHankel (c • p + q)).re +
        (primeArchSourceTraceHankel (c • p - q)).re =
      2 * c ^ (2 : ℕ) * (primeArchSourceTraceHankel p).re +
        2 * (primeArchSourceTraceHankel q).re := by
  simp_rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  rw [← momentFunctional_add]
  have hpoly :
      (c • p + q) ^ (2 : ℕ) + (c • p - q) ^ (2 : ℕ) =
        (2 * c ^ (2 : ℕ)) • (p ^ (2 : ℕ)) + (2 : ℝ) • (q ^ (2 : ℕ)) := by
    simp only [Polynomial.smul_eq_C_mul, map_mul, map_pow, map_ofNat]
    ring
  rw [hpoly, momentFunctional_add]
  simp only [momentFunctional_smul]

/-- Integer source trace--Hankel positivity restricted above an arbitrary fixed polynomial degree. -/
def PrimeArchSourceTraceHankelIntDegreeTailNonnegativeFrom (K : ℕ) : Prop :=
  ∀ p : Polynomial ℤ, K ≤ p.natDegree →
    0 ≤ (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re

/-- Positivity above any fixed integer-polynomial degree forces the complete countable source cone.
For an omitted test `p`, apply the tail hypothesis to `N p ± X^d`.  Adding the two quadratic
values cancels the cross terms; the negative quadratic coefficient of a hypothetical `Q(p) < 0`
dominates the fixed `X^d` value for large `N`. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_degreeTail
    (K : ℕ) (htail : PrimeArchSourceTraceHankelIntDegreeTailNonnegativeFrom K) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  let P : Polynomial ℝ := p.map (Int.castRingHom ℝ)
  by_contra hp
  have hpneg : (primeArchSourceTraceHankel P).re < 0 := lt_of_not_ge hp
  let d : ℕ := max K (p.natDegree + 1)
  let Q : Polynomial ℝ := Polynomial.X ^ d
  let A : ℝ := (primeArchSourceTraceHankel Q).re
  let B : ℝ := -(primeArchSourceTraceHankel P).re
  have hB : 0 < B := by
    dsimp only [B]
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (|A| / B))
  have hNgt : |A| / B < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hNone : 1 < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  let pplus : Polynomial ℤ := Polynomial.C (N : ℤ) * p + Polynomial.X ^ d
  let pminus : Polynomial ℤ := Polynomial.C (N : ℤ) * p - Polynomial.X ^ d
  have hlow : (Polynomial.C (N : ℤ) * p).natDegree < d := by
    apply lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _)
    exact lt_of_lt_of_le (Nat.lt_succ_self _)
      (le_max_right K (p.natDegree + 1))
  have hplusdeg : pplus.natDegree = d := by
    dsimp only [pplus]
    have hlow' : (Polynomial.C (N : ℤ) * p).natDegree <
        ((Polynomial.X : Polynomial ℤ) ^ d).natDegree := by
      simpa only [Polynomial.natDegree_X_pow] using hlow
    rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt hlow',
      Polynomial.natDegree_X_pow]
  have hminusdeg : pminus.natDegree = d := by
    dsimp only [pminus]
    have hlow' : (Polynomial.C (N : ℤ) * p).natDegree <
        ((Polynomial.X : Polynomial ℤ) ^ d).natDegree := by
      simpa only [Polynomial.natDegree_X_pow] using hlow
    rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt hlow',
      Polynomial.natDegree_X_pow]
  have hKd : K ≤ d := le_max_left _ _
  have hplus := htail pplus (hplusdeg ▸ hKd)
  have hminus := htail pminus (hminusdeg ▸ hKd)
  have hmapPlus : pplus.map (Int.castRingHom ℝ) = (N : ℝ) • P + Q := by
    simp [pplus, P, Q, Polynomial.smul_eq_C_mul]
  have hmapMinus : pminus.map (Int.castRingHom ℝ) = (N : ℝ) • P - Q := by
    simp [pminus, P, Q, Polynomial.smul_eq_C_mul]
  rw [hmapPlus] at hplus
  rw [hmapMinus] at hminus
  have hsum := add_nonneg hplus hminus
  rw [primeArchSourceTraceHankel_smul_add_sub_re] at hsum
  have hAB : |A| < (N : ℝ) * B := (div_lt_iff₀ hB).mp hNgt
  have hNnonneg : 0 ≤ (N : ℝ) := by linarith
  have hNN : (N : ℝ) ≤ (N : ℝ) ^ (2 : ℕ) := by nlinarith
  have hmul : (N : ℝ) * B ≤ (N : ℝ) ^ (2 : ℕ) * B :=
    mul_le_mul_of_nonneg_right hNN hB.le
  have hAle : A ≤ |A| := le_abs_self A
  dsimp only [A, B] at hsum hAB hmul hAle
  nlinarith

/-- **Arbitrary degree-tail RH law.**  Every fixed cofinal polynomial-degree tail of the
integer prime--Gamma trace cone is already equivalent to RH. -/
theorem primeArchSourceTraceHankelIntDegreeTailNonnegativeFrom_iff_riemannHypothesis
    (K : ℕ) :
    PrimeArchSourceTraceHankelIntDegreeTailNonnegativeFrom K ↔
      RiemannHypothesis := by
  constructor
  · intro htail
    exact riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
      (primeArchSourceTraceHankelIntNonnegative_of_degreeTail K htail)
  · intro hRH
    have hfull := primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis.mpr hRH
    intro p hp
    exact hfull p

/-- The previously isolated degree-two tail proves RH without either low theta-ratio hypothesis. -/
theorem riemannHypothesis_of_primeArchSourceTraceHankelIntDegreeTwoTailNonnegative
    (htail : PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
  apply primeArchSourceTraceHankelIntNonnegative_of_degreeTail 2
  exact htail

/-- The degree-two integer-polynomial tail is itself exactly RH. -/
theorem primeArchSourceTraceHankelIntDegreeTwoTailNonnegative_iff_riemannHypothesis :
    PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative ↔
      RiemannHypothesis := by
  simpa only [PrimeArchSourceTraceHankelIntDegreeTailNonnegativeFrom] using!
    primeArchSourceTraceHankelIntDegreeTailNonnegativeFrom_iff_riemannHypothesis 2

end

end RHTower

namespace RHTower

noncomputable section

open Polynomial Filter Topology

/-! ## Sparse cofinal degree sets -/

/-- Integer source trace--Hankel positivity restricted to tests whose exact degrees lie in `D`. -/
def PrimeArchSourceTraceHankelIntDegreeSetNonnegative (D : Set ℕ) : Prop :=
  ∀ p : Polynomial ℤ, p.natDegree ∈ D →
    0 ≤ (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re

/-- Positivity on any infinite set of exact polynomial degrees forces the complete countable
source cone.  Above the degree of an omitted test, infinitude supplies one admissible degree `d`;
the opposite perturbations `N p ± X^d` then invoke the same quadratic cancellation. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_infiniteDegreeSet
    {D : Set ℕ} (hD : D.Infinite)
    (hset : PrimeArchSourceTraceHankelIntDegreeSetNonnegative D) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  let P : Polynomial ℝ := p.map (Int.castRingHom ℝ)
  by_contra hp
  have hpneg : (primeArchSourceTraceHankel P).re < 0 := lt_of_not_ge hp
  obtain ⟨d, hdD, hpd⟩ := hD.exists_gt p.natDegree
  let Q : Polynomial ℝ := Polynomial.X ^ d
  let A : ℝ := (primeArchSourceTraceHankel Q).re
  let B : ℝ := -(primeArchSourceTraceHankel P).re
  have hB : 0 < B := by
    dsimp only [B]
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (|A| / B))
  have hNgt : |A| / B < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hNone : 1 < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  let pplus : Polynomial ℤ := Polynomial.C (N : ℤ) * p + Polynomial.X ^ d
  let pminus : Polynomial ℤ := Polynomial.C (N : ℤ) * p - Polynomial.X ^ d
  have hlow : (Polynomial.C (N : ℤ) * p).natDegree < d :=
    lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) hpd
  have hplusdeg : pplus.natDegree = d := by
    dsimp only [pplus]
    have hlow' : (Polynomial.C (N : ℤ) * p).natDegree <
        ((Polynomial.X : Polynomial ℤ) ^ d).natDegree := by
      simpa only [Polynomial.natDegree_X_pow] using hlow
    rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt hlow',
      Polynomial.natDegree_X_pow]
  have hminusdeg : pminus.natDegree = d := by
    dsimp only [pminus]
    have hlow' : (Polynomial.C (N : ℤ) * p).natDegree <
        ((Polynomial.X : Polynomial ℤ) ^ d).natDegree := by
      simpa only [Polynomial.natDegree_X_pow] using hlow
    rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt hlow',
      Polynomial.natDegree_X_pow]
  have hplus := hset pplus (hplusdeg ▸ hdD)
  have hminus := hset pminus (hminusdeg ▸ hdD)
  have hmapPlus : pplus.map (Int.castRingHom ℝ) = (N : ℝ) • P + Q := by
    simp [pplus, P, Q, Polynomial.smul_eq_C_mul]
  have hmapMinus : pminus.map (Int.castRingHom ℝ) = (N : ℝ) • P - Q := by
    simp [pminus, P, Q, Polynomial.smul_eq_C_mul]
  rw [hmapPlus] at hplus
  rw [hmapMinus] at hminus
  have hsum := add_nonneg hplus hminus
  rw [primeArchSourceTraceHankel_smul_add_sub_re] at hsum
  have hAB : |A| < (N : ℝ) * B := (div_lt_iff₀ hB).mp hNgt
  have hNnonneg : 0 ≤ (N : ℝ) := by linarith
  have hNN : (N : ℝ) ≤ (N : ℝ) ^ (2 : ℕ) := by nlinarith
  have hmul : (N : ℝ) * B ≤ (N : ℝ) ^ (2 : ℕ) * B :=
    mul_le_mul_of_nonneg_right hNN hB.le
  have hAle : A ≤ |A| := le_abs_self A
  dsimp only [A, B] at hsum hAB hmul hAle
  nlinarith

/-- **Sparse-degree RH law.**  For every infinite set `D` of natural numbers, source positivity
only for integer polynomials whose exact degree belongs to `D` is equivalent to RH. -/
theorem primeArchSourceTraceHankelIntDegreeSetNonnegative_iff_riemannHypothesis
    {D : Set ℕ} (hD : D.Infinite) :
    PrimeArchSourceTraceHankelIntDegreeSetNonnegative D ↔ RiemannHypothesis := by
  constructor
  · intro hset
    exact riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
      (primeArchSourceTraceHankelIntNonnegative_of_infiniteDegreeSet hD hset)
  · intro hRH
    have hfull := primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis.mpr hRH
    intro p hp
    exact hfull p

end

end RHTower

namespace RHTower

noncomputable section

open Polynomial Filter Topology
open HTGeometry

/-! ## Monic sparse degree sets -/

/-- Symmetric polarization around a high-degree centre: opposite scalar perturbations cancel all
cross terms and retain only the two diagonal trace--Hankel values. -/
theorem primeArchSourceTraceHankel_add_sub_smul_re
    (c : ℝ) (p q : Polynomial ℝ) :
    (primeArchSourceTraceHankel (q + c • p)).re +
        (primeArchSourceTraceHankel (q - c • p)).re =
      2 * c ^ (2 : ℕ) * (primeArchSourceTraceHankel p).re +
        2 * (primeArchSourceTraceHankel q).re := by
  simp_rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  rw [← momentFunctional_add]
  have hpoly :
      (q + c • p) ^ (2 : ℕ) + (q - c • p) ^ (2 : ℕ) =
        (2 * c ^ (2 : ℕ)) • (p ^ (2 : ℕ)) + (2 : ℝ) • (q ^ (2 : ℕ)) := by
    simp only [Polynomial.smul_eq_C_mul, map_mul, map_pow, map_ofNat]
    ring
  rw [hpoly, momentFunctional_add]
  simp only [momentFunctional_smul]

/-- Source trace--Hankel positivity restricted simultaneously to monic integer polynomials and to
an exact degree set `D`. -/
def PrimeArchSourceTraceHankelIntMonicDegreeSetNonnegative (D : Set ℕ) : Prop :=
  ∀ p : Polynomial ℤ, p.Monic → p.natDegree ∈ D →
    0 ≤ (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re

/-- Monic tests in any infinite set of exact degrees force the complete integer source cone.  Given
an omitted test `p`, choose `d ∈ D` above its degree.  The probes `X^d + N p` and `X^d - N p` are
both monic of degree `d`; their quadratic values cancel all cross terms, and a hypothetical negative
value at `p` dominates the fixed value at `X^d` as `N` grows. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_monicInfiniteDegreeSet
    {D : Set ℕ} (hD : D.Infinite)
    (hset : PrimeArchSourceTraceHankelIntMonicDegreeSetNonnegative D) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  let P : Polynomial ℝ := p.map (Int.castRingHom ℝ)
  by_contra hp
  have hpneg : (primeArchSourceTraceHankel P).re < 0 := lt_of_not_ge hp
  obtain ⟨d, hdD, hpd⟩ := hD.exists_gt p.natDegree
  let Q : Polynomial ℝ := Polynomial.X ^ d
  let A : ℝ := (primeArchSourceTraceHankel Q).re
  let B : ℝ := -(primeArchSourceTraceHankel P).re
  have hB : 0 < B := by
    dsimp only [B]
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (|A| / B))
  have hNgt : |A| / B < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hNone : 1 < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  let lower : Polynomial ℤ := Polynomial.C (N : ℤ) * p
  let pplus : Polynomial ℤ := Polynomial.X ^ d + lower
  let pminus : Polynomial ℤ := Polynomial.X ^ d - lower
  have hlow : lower.natDegree < d := by
    dsimp only [lower]
    exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) hpd
  have hlowDegree : lower.degree < (d : WithBot ℕ) := by
    by_cases hzero : lower = 0
    · simp [hzero]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mp hlow
  have hplusMonic : pplus.Monic := by
    dsimp only [pplus]
    exact Polynomial.monic_X_pow_add hlowDegree
  have hminusMonic : pminus.Monic := by
    dsimp only [pminus]
    exact Polynomial.monic_X_pow_sub hlowDegree
  have hplusdeg : pplus.natDegree = d := by
    dsimp only [pplus]
    have hlow' : lower.natDegree <
        ((Polynomial.X : Polynomial ℤ) ^ d).natDegree := by
      simpa only [Polynomial.natDegree_X_pow] using hlow
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlow',
      Polynomial.natDegree_X_pow]
  have hminusdeg : pminus.natDegree = d := by
    dsimp only [pminus]
    have hlow' : lower.natDegree <
        ((Polynomial.X : Polynomial ℤ) ^ d).natDegree := by
      simpa only [Polynomial.natDegree_X_pow] using hlow
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlow',
      Polynomial.natDegree_X_pow]
  have hplus := hset pplus hplusMonic (hplusdeg ▸ hdD)
  have hminus := hset pminus hminusMonic (hminusdeg ▸ hdD)
  have hmapPlus : pplus.map (Int.castRingHom ℝ) = Q + (N : ℝ) • P := by
    simp [pplus, lower, P, Q, Polynomial.smul_eq_C_mul]
  have hmapMinus : pminus.map (Int.castRingHom ℝ) = Q - (N : ℝ) • P := by
    simp [pminus, lower, P, Q, Polynomial.smul_eq_C_mul]
  rw [hmapPlus] at hplus
  rw [hmapMinus] at hminus
  have hsum := add_nonneg hplus hminus
  rw [primeArchSourceTraceHankel_add_sub_smul_re] at hsum
  have hAB : |A| < (N : ℝ) * B := (div_lt_iff₀ hB).mp hNgt
  have hNnonneg : 0 ≤ (N : ℝ) := by linarith
  have hNN : (N : ℝ) ≤ (N : ℝ) ^ (2 : ℕ) := by nlinarith
  have hmul : (N : ℝ) * B ≤ (N : ℝ) ^ (2 : ℕ) * B :=
    mul_le_mul_of_nonneg_right hNN hB.le
  have hAle : A ≤ |A| := le_abs_self A
  dsimp only [A, B] at hsum hAB hmul hAle
  nlinarith

/-- **Monic sparse-degree RH law.**  For every infinite set `D` of natural numbers, source
positivity only for monic integer polynomials whose exact degree belongs to `D` is equivalent to
RH. -/
theorem primeArchSourceTraceHankelIntMonicDegreeSetNonnegative_iff_riemannHypothesis
    {D : Set ℕ} (hD : D.Infinite) :
    PrimeArchSourceTraceHankelIntMonicDegreeSetNonnegative D ↔ RiemannHypothesis := by
  constructor
  · intro hset
    exact riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
      (primeArchSourceTraceHankelIntNonnegative_of_monicInfiniteDegreeSet hD hset)
  · intro hRH
    have hfull := primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis.mpr hRH
    intro p hpMonic hpDegree
    exact hfull p

end

end RHTower

namespace RHTower

noncomputable section

open Polynomial Filter Topology

/-! ## Irreducible Eisenstein sparse degree sets -/

/-- The fixed coefficient ideal used by the Eisenstein reduction. -/
def primeArchTwoEisensteinIdeal : Ideal ℤ := Ideal.span {(2 : ℤ)}

/-- The positive high-degree probe `X^d + 2 + 4 N p` is Eisenstein at `2`. -/
theorem primeArch_twoEisenstein_plus (p : Polynomial ℤ) (d N : ℕ)
    (hpd : p.natDegree < d) :
    (Polynomial.X ^ d + Polynomial.C 2 +
      Polynomial.C (4 * (N : ℤ)) * p).IsEisensteinAt primeArchTwoEisensteinIdeal := by
  let lower : Polynomial ℤ := Polynomial.C 2 + Polynomial.C (4 * (N : ℤ)) * p
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hpd
  have hlowNat : lower.natDegree < d := by
    dsimp only [lower]
    apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
    rw [max_lt_iff]
    constructor
    · simpa using hd
    · exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) hpd
  have hlowDegree : lower.degree < (d : WithBot ℕ) := by
    by_cases hzero : lower = 0
    · simp [hzero]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mp hlowNat
  have hmonic : (Polynomial.X ^ d + lower).Monic :=
    Polynomial.monic_X_pow_add hlowDegree
  have hne : primeArchTwoEisensteinIdeal ≠ ⊤ := by
    dsimp only [primeArchTwoEisensteinIdeal]
    exact (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr (by norm_num) |>.ne_top
  have hsumDegree : (Polynomial.X ^ d + lower).natDegree = d := by
    have hlow' : lower.natDegree <
        ((Polynomial.X : Polynomial ℤ) ^ d).natDegree := by
      simpa only [Polynomial.natDegree_X_pow] using hlowNat
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlow',
      Polynomial.natDegree_X_pow]
  have hmem : ∀ {n}, n < (Polynomial.X ^ d + lower).natDegree →
      (Polynomial.X ^ d + lower).coeff n ∈ primeArchTwoEisensteinIdeal := by
    intro n hn
    rw [hsumDegree] at hn
    dsimp only [primeArchTwoEisensteinIdeal]
    rw [Ideal.mem_span_singleton]
    have hnd : n ≠ d := Nat.ne_of_lt hn
    dsimp only [lower]
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg hnd,
      zero_add, Polynomial.coeff_C_mul]
    by_cases hn0 : n = 0
    · subst n
      simp only [Polynomial.coeff_C_zero]
      exact dvd_add (by norm_num) ⟨2 * (N : ℤ) * p.coeff 0, by ring⟩
    · rw [Polynomial.coeff_C, if_neg hn0, zero_add]
      exact ⟨2 * (N : ℤ) * p.coeff n, by ring⟩
  have hnotMem :
      (Polynomial.X ^ d + lower).coeff 0 ∉ primeArchTwoEisensteinIdeal ^ (2 : ℕ) := by
    dsimp only [primeArchTwoEisensteinIdeal]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp only [pow_two]
    dsimp only [lower]
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow,
      if_neg (Nat.ne_of_lt hd), zero_add, Polynomial.coeff_C_zero,
      Polynomial.coeff_C_mul]
    intro hfour
    have hterm : ((2 : ℤ) * 2) ∣ 4 * (N : ℤ) * p.coeff 0 := by
      refine ⟨(N : ℤ) * p.coeff 0, ?_⟩
      ring
    have hdiff := dvd_sub hfour hterm
    have : ((2 : ℤ) * 2) ∣ 2 := by
      simpa only [add_sub_cancel_right] using hdiff
    norm_num at this
  simpa only [lower, add_assoc] using
    hmonic.isEisensteinAt_of_mem_of_notMem hne hmem hnotMem

/-- The negative high-degree probe `X^d + 2 - 4 N p` is Eisenstein at `2`. -/
theorem primeArch_twoEisenstein_minus (p : Polynomial ℤ) (d N : ℕ)
    (hpd : p.natDegree < d) :
    (Polynomial.X ^ d + Polynomial.C 2 -
      Polynomial.C (4 * (N : ℤ)) * p).IsEisensteinAt primeArchTwoEisensteinIdeal := by
  simpa only [Polynomial.natDegree_neg, mul_neg, sub_eq_add_neg] using
    primeArch_twoEisenstein_plus (-p) d N
      (by simpa only [Polynomial.natDegree_neg] using hpd)

/-- A positive-degree monic polynomial Eisenstein at `2` is irreducible over the integers. -/
theorem irreducible_of_monic_primeArchTwoEisenstein {p : Polynomial ℤ}
    (hmonic : p.Monic) (heis : p.IsEisensteinAt primeArchTwoEisensteinIdeal)
    (hdeg : 0 < p.natDegree) : Irreducible p := by
  apply heis.irreducible
  · dsimp only [primeArchTwoEisensteinIdeal]
    exact (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr (by norm_num)
  · exact hmonic.isPrimitive
  · exact hdeg

/-- Source trace--Hankel positivity restricted to monic polynomials Eisenstein at `2` whose exact
degrees lie in `D`. Every test in this family is irreducible when its degree is positive. -/
def PrimeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative (D : Set ℕ) : Prop :=
  ∀ p : Polynomial ℤ, p.Monic → p.IsEisensteinAt primeArchTwoEisensteinIdeal →
    p.natDegree ∈ D →
      0 ≤ (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re

/-- Tests in the fixed `2`-Eisenstein coefficient chamber at any infinite degree set force the
complete integer source cone. The two probes `X^d + 2 ± 4 N p` remain in that chamber and their
quadratic values cancel all cross terms. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_twoEisensteinInfiniteDegreeSet
    {D : Set ℕ} (hD : D.Infinite)
    (hset : PrimeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative D) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  let P : Polynomial ℝ := p.map (Int.castRingHom ℝ)
  by_contra hp
  have hpneg : (primeArchSourceTraceHankel P).re < 0 := lt_of_not_ge hp
  obtain ⟨d, hdD, hpd⟩ := hD.exists_gt p.natDegree
  let qInt : Polynomial ℤ := Polynomial.X ^ d + Polynomial.C 2
  let Q : Polynomial ℝ := qInt.map (Int.castRingHom ℝ)
  let A : ℝ := (primeArchSourceTraceHankel Q).re
  let B : ℝ := -(primeArchSourceTraceHankel P).re
  have hB : 0 < B := by
    dsimp only [B]
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (|A| / B))
  have hNgt : |A| / B < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hNone : 1 < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  let lower : Polynomial ℤ := Polynomial.C (4 * (N : ℤ)) * p
  let pplus : Polynomial ℤ := qInt + lower
  let pminus : Polynomial ℤ := qInt - lower
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hpd
  have hlow : lower.natDegree < d := by
    dsimp only [lower]
    exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) hpd
  have hcenterLower : (Polynomial.C 2 + lower).natDegree < d := by
    apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
    rw [max_lt_iff]
    exact ⟨by simpa using hd, hlow⟩
  have hcenterMinusLower : (Polynomial.C 2 - lower).natDegree < d := by
    apply lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
    rw [max_lt_iff]
    exact ⟨by simpa using hd, hlow⟩
  have hplusdeg : pplus.natDegree = d := by
    dsimp only [pplus, qInt]
    rw [add_assoc]
    have hlow' : (Polynomial.C 2 + lower).natDegree <
        ((Polynomial.X : Polynomial ℤ) ^ d).natDegree := by
      simpa only [Polynomial.natDegree_X_pow] using hcenterLower
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlow',
      Polynomial.natDegree_X_pow]
  have hminusdeg : pminus.natDegree = d := by
    dsimp only [pminus, qInt]
    rw [add_sub_assoc]
    have hlow' : (Polynomial.C 2 - lower).natDegree <
        ((Polynomial.X : Polynomial ℤ) ^ d).natDegree := by
      simpa only [Polynomial.natDegree_X_pow] using hcenterMinusLower
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlow',
      Polynomial.natDegree_X_pow]
  have hplusE : pplus.IsEisensteinAt primeArchTwoEisensteinIdeal := by
    simpa only [pplus, qInt, lower, add_assoc] using primeArch_twoEisenstein_plus p d N hpd
  have hminusE : pminus.IsEisensteinAt primeArchTwoEisensteinIdeal := by
    simpa only [pminus, qInt, lower, add_sub_assoc] using primeArch_twoEisenstein_minus p d N hpd
  have hplusMonic : pplus.Monic := by
    dsimp only [pplus, qInt]
    rw [add_assoc]
    apply Polynomial.monic_X_pow_add
    by_cases hz : Polynomial.C 2 + lower = 0
    · rw [hz]
      simp
    · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mp hcenterLower
  have hminusMonic : pminus.Monic := by
    dsimp only [pminus, qInt]
    rw [add_sub_assoc]
    apply Polynomial.monic_X_pow_add
    by_cases hz : Polynomial.C 2 - lower = 0
    · rw [hz]
      simp
    · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mp hcenterMinusLower
  have hplus := hset pplus hplusMonic hplusE (hplusdeg ▸ hdD)
  have hminus := hset pminus hminusMonic hminusE (hminusdeg ▸ hdD)
  have hmapPlus : pplus.map (Int.castRingHom ℝ) = Q + (4 * (N : ℝ)) • P := by
    dsimp only [pplus, Q]
    rw [Polynomial.map_add]
    congr 1
    dsimp only [lower, P]
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.smul_eq_C_mul]
    congr 1
    norm_num
  have hmapMinus : pminus.map (Int.castRingHom ℝ) = Q - (4 * (N : ℝ)) • P := by
    dsimp only [pminus, Q]
    rw [Polynomial.map_sub]
    congr 1
    dsimp only [lower, P]
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.smul_eq_C_mul]
    congr 1
    norm_num
  rw [hmapPlus] at hplus
  rw [hmapMinus] at hminus
  have hsum := add_nonneg hplus hminus
  rw [primeArchSourceTraceHankel_add_sub_smul_re] at hsum
  have hAB : |A| < (N : ℝ) * B := (div_lt_iff₀ hB).mp hNgt
  have hNnonneg : 0 ≤ (N : ℝ) := by linarith
  have hNN : (N : ℝ) ≤ (4 * (N : ℝ)) ^ (2 : ℕ) := by nlinarith
  have hmul : (N : ℝ) * B ≤ (4 * (N : ℝ)) ^ (2 : ℕ) * B :=
    mul_le_mul_of_nonneg_right hNN hB.le
  have hAle : A ≤ |A| := le_abs_self A
  dsimp only [A, B] at hsum hAB hmul hAle
  nlinarith

/-- **Irreducible Eisenstein sparse-degree RH law.** For every infinite set `D`, RH is equivalent
to source positivity only on monic integer polynomials Eisenstein at `2` whose exact degrees lie in
`D`. Thus one fixed irreducible coefficient chamber on an arbitrarily sparse cofinal degree set is
positivity-complete. -/
theorem primeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative_iff_riemannHypothesis
    {D : Set ℕ} (hD : D.Infinite) :
    PrimeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative D ↔ RiemannHypothesis := by
  constructor
  · intro hset
    exact riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
      (primeArchSourceTraceHankelIntNonnegative_of_twoEisensteinInfiniteDegreeSet hD hset)
  · intro hRH
    have hfull := primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis.mpr hRH
    intro p hpMonic hpEisenstein hpDegree
    exact hfull p

end

end RHTower

namespace RHTower

noncomputable section

open Polynomial Filter Topology

/-- Monomial cap with a positive integer multiple of `p`. -/
def primeArchMonomialCappedPlus (p : Polynomial ℤ) (N : ℕ) : Polynomial ℤ :=
  Polynomial.X ^ (p.natDegree + 1) + Polynomial.C (N : ℤ) * p

/-- Monomial cap with a negative integer multiple of `p`. -/
def primeArchMonomialCappedMinus (p : Polynomial ℤ) (N : ℕ) : Polynomial ℤ :=
  Polynomial.X ^ (p.natDegree + 1) - Polynomial.C (N : ℤ) * p

/-- Cofinal nonnegativity of the sum on one antipodal monomial-capped pair per polynomial. -/
def PrimeArchSourceTraceHankelAntipodalCofinalNonnegative : Prop :=
  ∀ (p : Polynomial ℤ) (M : ℕ), ∃ N : ℕ, M ≤ N ∧
    0 ≤
      (primeArchSourceTraceHankel
        ((primeArchMonomialCappedPlus p N).map (Int.castRingHom ℝ))).re +
      (primeArchSourceTraceHankel
        ((primeArchMonomialCappedMinus p N).map (Int.castRingHom ℝ))).re

/-- Cofinal antipodal-pair nonnegativity is already full integer-polynomial positivity.

The cross terms cancel in the pair sum. If the Hankel form were negative on `p`, sufficiently
large integer scaling would dominate the fixed monomial cap and contradict the cofinal condition.
-/
theorem primeArchSourceTraceHankelAntipodalCofinalNonnegative_iff_full :
    PrimeArchSourceTraceHankelAntipodalCofinalNonnegative ↔
      PrimeArchSourceTraceHankelIntNonnegative := by
  constructor
  · intro hpair p
    let P : Polynomial ℝ := p.map (Int.castRingHom ℝ)
    by_contra hp
    have hpneg : (primeArchSourceTraceHankel P).re < 0 := lt_of_not_ge hp
    let d : ℕ := p.natDegree + 1
    let Q : Polynomial ℝ := Polynomial.X ^ d
    let A : ℝ := (primeArchSourceTraceHankel Q).re
    let B : ℝ := -(primeArchSourceTraceHankel P).re
    have hB : 0 < B := by
      dsimp only [B]
      linarith
    obtain ⟨M, hM⟩ := exists_nat_gt (max 1 (|A| / B))
    obtain ⟨N, hMN, hnonneg⟩ := hpair p M
    have hMNcast : (M : ℝ) ≤ N := by exact_mod_cast hMN
    have hNgt : |A| / B < (N : ℝ) :=
      (lt_of_le_of_lt (le_max_right _ _) hM).trans_le hMNcast
    have hNone : 1 < (N : ℝ) :=
      (lt_of_le_of_lt (le_max_left _ _) hM).trans_le hMNcast
    have hmapPlus :
        (primeArchMonomialCappedPlus p N).map (Int.castRingHom ℝ) =
          Q + (N : ℝ) • P := by
      simp [primeArchMonomialCappedPlus, P, Q, d,
        Polynomial.smul_eq_C_mul]
    have hmapMinus :
        (primeArchMonomialCappedMinus p N).map (Int.castRingHom ℝ) =
          Q - (N : ℝ) • P := by
      simp [primeArchMonomialCappedMinus, P, Q, d,
        Polynomial.smul_eq_C_mul]
    rw [hmapPlus, hmapMinus,
      primeArchSourceTraceHankel_add_sub_smul_re] at hnonneg
    have hAB : |A| < (N : ℝ) * B := (div_lt_iff₀ hB).mp hNgt
    have hNN : (N : ℝ) ≤ (N : ℝ) ^ (2 : ℕ) := by nlinarith
    have hmul : (N : ℝ) * B ≤ (N : ℝ) ^ (2 : ℕ) * B :=
      mul_le_mul_of_nonneg_right hNN hB.le
    have hAle : A ≤ |A| := le_abs_self A
    dsimp only [A, B] at hnonneg hAB hmul hAle
    nlinarith
  · intro hfull p M
    refine ⟨M, le_rfl, ?_⟩
    exact add_nonneg
      (hfull (primeArchMonomialCappedPlus p M))
      (hfull (primeArchMonomialCappedMinus p M))

/-- **Cofinal antipodal monomial-pair RH law.** RH is equivalent to one cofinal nonnegative
antipodal pair sum for each integer polynomial. -/
theorem primeArchSourceTraceHankelAntipodalCofinalNonnegative_iff_riemannHypothesis :
    PrimeArchSourceTraceHankelAntipodalCofinalNonnegative ↔
      RiemannHypothesis :=
  primeArchSourceTraceHankelAntipodalCofinalNonnegative_iff_full.trans
    primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis

/-- Sum of the source Hankel form on the two antipodal monomial-capped perturbations. -/
def primeArchSourceTraceHankelAntipodalPairSum
    (p : Polynomial ℤ) (N : ℕ) : ℝ :=
  (primeArchSourceTraceHankel
      ((primeArchMonomialCappedPlus p N).map (Int.castRingHom ℝ))).re +
    (primeArchSourceTraceHankel
      ((primeArchMonomialCappedMinus p N).map (Int.castRingHom ℝ))).re

/-- No integer-polynomial antipodal pair-sum sequence diverges to negative infinity. -/
def PrimeArchSourceTraceHankelAntipodalPairNondivergent : Prop :=
  ∀ p : Polynomial ℤ,
    ¬ Tendsto (primeArchSourceTraceHankelAntipodalPairSum p) atTop atBot

/-- Antipodal pair sum is a quadratic whose leading coefficient is the Hankel value on `p`. -/
theorem primeArchSourceTraceHankelAntipodalPairSum_eq
    (p : Polynomial ℤ) (N : ℕ) :
    primeArchSourceTraceHankelAntipodalPairSum p N =
      2 * (N : ℝ) ^ (2 : ℕ) *
          (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re +
        2 * (primeArchSourceTraceHankel
          (Polynomial.X ^ (p.natDegree + 1) : Polynomial ℝ)).re := by
  have hmapPlus :
      (primeArchMonomialCappedPlus p N).map (Int.castRingHom ℝ) =
        Polynomial.X ^ (p.natDegree + 1) +
          (N : ℝ) • p.map (Int.castRingHom ℝ) := by
    simp [primeArchMonomialCappedPlus, Polynomial.smul_eq_C_mul]
  have hmapMinus :
      (primeArchMonomialCappedMinus p N).map (Int.castRingHom ℝ) =
        Polynomial.X ^ (p.natDegree + 1) -
          (N : ℝ) • p.map (Int.castRingHom ℝ) := by
    simp [primeArchMonomialCappedMinus, Polynomial.smul_eq_C_mul]
  unfold primeArchSourceTraceHankelAntipodalPairSum
  rw [hmapPlus, hmapMinus,
    primeArchSourceTraceHankel_add_sub_smul_re]

/-- Antipodal pair nondivergence is exactly full integer-polynomial source positivity. -/
theorem primeArchSourceTraceHankelAntipodalPairNondivergent_iff_full :
    PrimeArchSourceTraceHankelAntipodalPairNondivergent ↔
      PrimeArchSourceTraceHankelIntNonnegative := by
  constructor
  · intro hnondiv p
    by_contra hp
    have hpneg :
        (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re < 0 :=
      lt_of_not_ge hp
    have hsq : Tendsto (fun N : ℕ => (N : ℝ) ^ (2 : ℕ)) atTop atTop :=
      (tendsto_pow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    have hscaled :
        Tendsto
          (fun N : ℕ =>
            (2 * (primeArchSourceTraceHankel
              (p.map (Int.castRingHom ℝ))).re) * (N : ℝ) ^ (2 : ℕ))
          atTop atBot :=
      hsq.const_mul_atTop_of_neg (by linarith)
    have hlim :
        Tendsto (primeArchSourceTraceHankelAntipodalPairSum p) atTop atBot := by
      have hadd := tendsto_atBot_add_const_right _
        (2 * (primeArchSourceTraceHankel
          (Polynomial.X ^ (p.natDegree + 1) : Polynomial ℝ)).re) hscaled
      convert hadd using 1
      ext N
      rw [primeArchSourceTraceHankelAntipodalPairSum_eq]
      ring
    exact (hnondiv p) hlim
  · intro hfull p hlim
    obtain ⟨N, hN⟩ := (tendsto_atBot.1 hlim (-1)).exists
    have hnonneg : 0 ≤ primeArchSourceTraceHankelAntipodalPairSum p N := by
      unfold primeArchSourceTraceHankelAntipodalPairSum
      exact add_nonneg
        (hfull (primeArchMonomialCappedPlus p N))
        (hfull (primeArchMonomialCappedMinus p N))
    linarith

/-- **Antipodal pair nondivergence RH law.** RH is equivalent to excluding negative-infinite
quadratic escape on every integer-polynomial antipodal pair sequence. -/
theorem primeArchSourceTraceHankelAntipodalPairNondivergent_iff_riemannHypothesis :
    PrimeArchSourceTraceHankelAntipodalPairNondivergent ↔ RiemannHypothesis :=
  primeArchSourceTraceHankelAntipodalPairNondivergent_iff_full.trans
    primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis

/-- Fixed integer-polynomial encoding through the finite graph of nonzero coefficients. -/
@[implicit_reducible]
noncomputable def primeArchIntegerPolynomialEncodable :
    Encodable (Polynomial ℤ) :=
  Encodable.ofInj
    (fun p : Polynomial ℤ => p.toFinsupp.coeff.graph)
    ((Finsupp.graph_injective ℕ ℤ).comp
      (AddMonoidAlgebra.coeff_injective.comp Polynomial.toFinsupp_injective))

/-- Code assigned to an integer polynomial by the fixed encoding. -/
noncomputable def primeArchIntegerPolynomialCode (p : Polynomial ℤ) : ℕ :=
  @Encodable.encode _ primeArchIntegerPolynomialEncodable p

/-- Integer polynomial decoded at a natural index; invalid codes default to zero. -/
noncomputable def primeArchIntegerPolynomialAt (k : ℕ) : Polynomial ℤ :=
  (@Encodable.decode _ primeArchIntegerPolynomialEncodable k).getD 0

/-- The fixed integer-polynomial enumeration hits every polynomial at its assigned code. -/
theorem primeArchIntegerPolynomialAt_code (p : Polynomial ℤ) :
    primeArchIntegerPolynomialAt (primeArchIntegerPolynomialCode p) = p := by
  change
    (@Encodable.decode _ primeArchIntegerPolynomialEncodable
      (@Encodable.encode _ primeArchIntegerPolynomialEncodable p)).getD 0 = p
  rw [@Encodable.encodek _ primeArchIntegerPolynomialEncodable p]
  rfl

/-- Running sum of negative antipodal pair values over all polynomial codes exposed so far. -/
noncomputable def primeArchSourceTraceHankelAntipodalGlobalNegativeSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1),
    min (primeArchSourceTraceHankelAntipodalPairSum
      (primeArchIntegerPolynomialAt k) N) 0

/-- The single enumerated running negative sum does not diverge to negative infinity. -/
def PrimeArchSourceTraceHankelAntipodalGlobalNondivergent : Prop :=
  ¬ Tendsto primeArchSourceTraceHankelAntipodalGlobalNegativeSum atTop atBot

/-- Nondivergence of one enumerated global negative-sum sequence is already full positivity. -/
theorem primeArchSourceTraceHankelAntipodalGlobalNondivergent_iff_full :
    PrimeArchSourceTraceHankelAntipodalGlobalNondivergent ↔
      PrimeArchSourceTraceHankelIntNonnegative := by
  constructor
  · intro hglobal p
    by_contra hp
    have hpneg :
        (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re < 0 :=
      lt_of_not_ge hp
    have hsq : Tendsto (fun N : ℕ => (N : ℝ) ^ (2 : ℕ)) atTop atTop :=
      (tendsto_pow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    have hscaled :
        Tendsto
          (fun N : ℕ =>
            (2 * (primeArchSourceTraceHankel
              (p.map (Int.castRingHom ℝ))).re) * (N : ℝ) ^ (2 : ℕ))
          atTop atBot :=
      hsq.const_mul_atTop_of_neg (by linarith)
    have hpair :
        Tendsto (primeArchSourceTraceHankelAntipodalPairSum p) atTop atBot := by
      have hadd := tendsto_atBot_add_const_right _
        (2 * (primeArchSourceTraceHankel
          (Polynomial.X ^ (p.natDegree + 1) : Polynomial ℝ)).re) hscaled
      convert hadd using 1
      ext N
      rw [primeArchSourceTraceHankelAntipodalPairSum_eq]
      ring
    apply hglobal
    rw [tendsto_atBot]
    intro b
    filter_upwards [tendsto_atBot.1 hpair b,
      eventually_ge_atTop (primeArchIntegerPolynomialCode p)] with N hpairN hcodeN
    have hcodeMem :
        primeArchIntegerPolynomialCode p ∈ Finset.range (N + 1) := by
      simp only [Finset.mem_range]
      omega
    have hsumErase :
        (∑ k ∈ (Finset.range (N + 1)).erase
          (primeArchIntegerPolynomialCode p),
            min (primeArchSourceTraceHankelAntipodalPairSum
              (primeArchIntegerPolynomialAt k) N) 0) ≤ 0 := by
      exact Finset.sum_nonpos fun k hk => min_le_right _ _
    calc
      primeArchSourceTraceHankelAntipodalGlobalNegativeSum N =
          (∑ k ∈ (Finset.range (N + 1)).erase
            (primeArchIntegerPolynomialCode p),
              min (primeArchSourceTraceHankelAntipodalPairSum
                (primeArchIntegerPolynomialAt k) N) 0) +
            min (primeArchSourceTraceHankelAntipodalPairSum
              (primeArchIntegerPolynomialAt
                (primeArchIntegerPolynomialCode p)) N) 0 := by
        unfold primeArchSourceTraceHankelAntipodalGlobalNegativeSum
        rw [Finset.sum_erase_add _ _ hcodeMem]
      _ ≤ min (primeArchSourceTraceHankelAntipodalPairSum
            (primeArchIntegerPolynomialAt
              (primeArchIntegerPolynomialCode p)) N) 0 :=
        add_le_of_nonpos_left hsumErase
      _ = min (primeArchSourceTraceHankelAntipodalPairSum p N) 0 := by
        rw [primeArchIntegerPolynomialAt_code]
      _ ≤ primeArchSourceTraceHankelAntipodalPairSum p N := min_le_left _ _
      _ ≤ b := hpairN
  · intro hfull hlim
    obtain ⟨N, hN⟩ := (tendsto_atBot.1 hlim (-1)).exists
    have hzero : primeArchSourceTraceHankelAntipodalGlobalNegativeSum N = 0 := by
      unfold primeArchSourceTraceHankelAntipodalGlobalNegativeSum
      apply Finset.sum_eq_zero
      intro k hk
      rw [min_eq_right]
      unfold primeArchSourceTraceHankelAntipodalPairSum
      exact add_nonneg
        (hfull (primeArchMonomialCappedPlus
          (primeArchIntegerPolynomialAt k) N))
        (hfull (primeArchMonomialCappedMinus
          (primeArchIntegerPolynomialAt k) N))
    rw [hzero] at hN
    norm_num at hN

/-- **One-sequence antipodal RH law.** RH is equivalent to nondivergence of a single running
negative-sum sequence over the fixed enumeration of integer polynomials. -/
theorem primeArchSourceTraceHankelAntipodalGlobalNondivergent_iff_riemannHypothesis :
    PrimeArchSourceTraceHankelAntipodalGlobalNondivergent ↔ RiemannHypothesis :=
  primeArchSourceTraceHankelAntipodalGlobalNondivergent_iff_full.trans
    primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis

end

end RHTower
