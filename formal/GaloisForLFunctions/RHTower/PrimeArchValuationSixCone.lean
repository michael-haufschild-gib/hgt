import GaloisForLFunctions.HTGeometry.PolynomialHankelTailCone
import GaloisForLFunctions.RHTower.PrimeArchShiftThirteenCircleCone
import GaloisForLFunctions.RHTower.PrimeArchCofinalHausdorffQuadrantRH
import GaloisForLFunctions.RHTower.SoninCoupledPrimeArchGramTransfer

/-!
# Unconditional valuation-six prime--Gamma Hankel cone

The thirteenth reciprocal-square Xi mass and endpoint radius control the absolute tail beginning
at normalized prime--archimedean moment twelve.  Combined with the generic polynomial
coefficient-energy estimate, this proves nonnegativity of the source Hankel form on every test
`X⁶ q` satisfying

`32 * E_tail(q) ≤ 7 * q(0)²`.

The final declarations remove the coupled-Sonin variational premise on this entire explicit
integer-polynomial family: only its strict complement remains as an assumption in the resulting
RH implication.
-/

open scoped BigOperators
open Polynomial

namespace RHTower

noncomputable section

/-- Normalized prime--archimedean moment tail beginning at moment twelve. -/
def primeArchShiftTwelveMoment (n : ℕ) : ℝ :=
  normalizedPrimeArchMoment (12 + n)

theorem xiShiftThirteenAbsoluteMass_nonneg :
    0 ≤ xiShiftThirteenAbsoluteMass := by
  exact tsum_nonneg fun q => pow_nonneg (norm_nonneg _) 13

theorem summable_abs_primeArchShiftTwelveMoment_tail :
    Summable (fun n : ℕ => |primeArchShiftTwelveMoment (n + 1)|) := by
  have hgeo :
      Summable (fun n : ℕ =>
        (2 / 41 : ℝ) ^ (n + 1) * xiShiftThirteenAbsoluteMass) := by
    have hbase :
        Summable (fun n : ℕ => (2 / 41 : ℝ) ^ n) :=
      summable_geometric_of_norm_lt_one (by norm_num)
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
      (hbase.mul_left (2 / 41 : ℝ)).mul_right xiShiftThirteenAbsoluteMass
  apply Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) hgeo
  simpa only [primeArchShiftTwelveMoment] using
    abs_normalizedPrimeArchMoment_twelve_add_le (n + 1)

/-- The absolute moment tail after moment twelve is at most `2/39` of the thirteenth Xi mass. -/
theorem tsum_abs_primeArchShiftTwelveMoment_tail_le :
    (∑' n : ℕ, |primeArchShiftTwelveMoment (n + 1)|) ≤
      (2 / 39 : ℝ) * xiShiftThirteenAbsoluteMass := by
  have hgeo :
      HasSum (fun n : ℕ =>
        (2 / 41 : ℝ) ^ (n + 1) * xiShiftThirteenAbsoluteMass)
        ((2 / 39 : ℝ) * xiShiftThirteenAbsoluteMass) := by
    have hbase :
        HasSum (fun n : ℕ => (2 / 41 : ℝ) ^ n) (1 - (2 / 41 : ℝ))⁻¹ :=
      hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
    have hvalue :
        (2 / 41 : ℝ) * (1 - (2 / 41 : ℝ))⁻¹ *
            xiShiftThirteenAbsoluteMass =
          (2 / 39 : ℝ) * xiShiftThirteenAbsoluteMass := by
      norm_num
    rw [← hvalue]
    apply HasSum.congr_fun
      ((hbase.mul_left (2 / 41 : ℝ)).mul_right xiShiftThirteenAbsoluteMass)
    intro n
    rw [pow_succ]
    ring
  calc
    (∑' n : ℕ, |primeArchShiftTwelveMoment (n + 1)|) ≤
        ∑' n : ℕ,
          (2 / 41 : ℝ) ^ (n + 1) * xiShiftThirteenAbsoluteMass :=
      summable_abs_primeArchShiftTwelveMoment_tail.tsum_le_tsum
        (fun n => by
          simpa only [primeArchShiftTwelveMoment] using
            abs_normalizedPrimeArchMoment_twelve_add_le (n + 1))
        hgeo.summable
    _ = (2 / 39 : ℝ) * xiShiftThirteenAbsoluteMass := hgeo.tsum_eq

/-- The shifted moment-twelve Hankel form is nonnegative on the explicit coefficient cone. -/
theorem momentFunctional_primeArchShiftTwelveMoment_sq_nonneg
    (p : Polynomial ℝ)
    (hcone : 32 * HTGeometry.polynomialNonconstantCoeffSqEnergy p ≤
      7 * (p.coeff 0) ^ 2) :
    0 ≤ HTGeometry.momentFunctional primeArchShiftTwelveMoment (p ^ 2) := by
  let E : ℝ := HTGeometry.polynomialCoeffSqEnergy p
  let A : ℝ := xiShiftThirteenAbsoluteMass
  let m0 : ℝ := normalizedPrimeArchMoment 12
  have hA : 0 ≤ A := by
    simpa only [A] using xiShiftThirteenAbsoluteMass_nonneg
  have hm0 : 0 ≤ m0 := by
    have hmass := one_eighth_xiShiftThirteenAbsoluteMass_le_normalizedPrimeArchMoment_twelve
    dsimp only [A, m0] at hA ⊢
    nlinarith
  have hA8 : A ≤ 8 * m0 := by
    have hmass := one_eighth_xiShiftThirteenAbsoluteMass_le_normalizedPrimeArchMoment_twelve
    dsimp only [A, m0]
    nlinarith
  have hE : 0 ≤ E := by
    simpa only [E] using HTGeometry.polynomialCoeffSqEnergy_nonneg p
  have htotal : 32 * E ≤ 39 * (p.coeff 0) ^ 2 := by
    dsimp only [E, HTGeometry.polynomialCoeffSqEnergy]
    nlinarith
  have herr := HTGeometry.abs_momentFunctional_sq_sub_vacuum_le
    primeArchShiftTwelveMoment p
    summable_abs_primeArchShiftTwelveMoment_tail
    tsum_abs_primeArchShiftTwelveMoment_tail_le
  have herr' :
      |HTGeometry.momentFunctional primeArchShiftTwelveMoment (p ^ 2) -
          (p.coeff 0) ^ 2 * m0| ≤
        m0 * (p.coeff 0) ^ 2 := by
    have hmiddle :
        2 * E * ((2 / 39 : ℝ) * A) ≤
          (32 * E) * m0 / 39 := by
      calc
        2 * E * ((2 / 39 : ℝ) * A) ≤
            2 * E * ((2 / 39 : ℝ) * (8 * m0)) := by
          gcongr
        _ = (32 * E) * m0 / 39 := by ring
    have hlast :
        (32 * E) * m0 / 39 ≤ m0 * (p.coeff 0) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right htotal hm0
      nlinarith
    exact (herr.trans hmiddle).trans hlast
  have hneg := neg_abs_le
    (HTGeometry.momentFunctional primeArchShiftTwelveMoment (p ^ 2) -
      (p.coeff 0) ^ 2 * m0)
  nlinarith

/-- Every real test `X⁶ p` in the coefficient cone has nonnegative canonical prime--Gamma
trace-Hankel value. -/
theorem re_primeArchSourceTraceHankel_X_pow_six_mul_nonneg
    (p : Polynomial ℝ)
    (hcone : 32 * HTGeometry.polynomialNonconstantCoeffSqEnergy p ≤
      7 * (p.coeff 0) ^ 2) :
    0 ≤ (primeArchSourceTraceHankel
      ((Polynomial.X : Polynomial ℝ) ^ 6 * p)).re := by
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  have hshift :
      HTGeometry.momentFunctional normalizedPrimeArchMoment
          (((Polynomial.X : Polynomial ℝ) ^ 6 * p) ^ 2) =
        HTGeometry.momentFunctional primeArchShiftTwelveMoment (p ^ 2) := by
    calc
      HTGeometry.momentFunctional normalizedPrimeArchMoment
          (((Polynomial.X : Polynomial ℝ) ^ 6 * p) ^ 2) =
          HTGeometry.momentFunctional normalizedPrimeArchMoment
            ((p ^ 2) * (((Polynomial.X : Polynomial ℝ) ^ 6) ^ 2)) := by
        congr 1
        ring
      _ = HTGeometry.momentFunctional
          (momentPolynomialTransform normalizedPrimeArchMoment
            (((Polynomial.X : Polynomial ℝ) ^ 6) ^ 2)) (p ^ 2) := by
        rw [momentFunctional_momentPolynomialTransform]
      _ = HTGeometry.momentFunctional primeArchShiftTwelveMoment (p ^ 2) := by
        apply HTGeometry.momentFunctional_congr
        intro n
        unfold momentPolynomialTransform primeArchShiftTwelveMoment
        have hpoly :
            (Polynomial.X : Polynomial ℝ) ^ n *
                ((Polynomial.X : Polynomial ℝ) ^ 6) ^ 2 =
              Polynomial.X ^ (12 + n) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          omega
        rw [hpoly, HTGeometry.momentFunctional_X_pow]
  rw [hshift]
  exact momentFunctional_primeArchShiftTwelveMoment_sq_nonneg p hcone

/-- Integer-polynomial family covered by the unconditional valuation-six cone. -/
def PrimeArchValuationSixCoefficientCone (p : Polynomial ℤ) : Prop :=
  ∃ q : Polynomial ℤ,
    p = (Polynomial.X : Polynomial ℤ) ^ 6 * q ∧
      32 * HTGeometry.polynomialNonconstantCoeffSqEnergy
          (q.map (Int.castRingHom ℝ)) ≤
        7 * ((q.coeff 0 : ℤ) : ℝ) ^ 2

theorem re_primeArchSourceTraceHankel_nonneg_of_valuationSixCoefficientCone
    (p : Polynomial ℤ) (hp : PrimeArchValuationSixCoefficientCone p) :
    0 ≤ (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re := by
  obtain ⟨q, rfl, hq⟩ := hp
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  apply re_primeArchSourceTraceHankel_X_pow_six_mul_nonneg
  simpa using hq

/-- Strict complement of the unconditional valuation-six coefficient cone. -/
def PrimeArchValuationSixCoefficientResidual (p : Polynomial ℤ) : Prop :=
  ¬ PrimeArchValuationSixCoefficientCone p

/-- Coupled-Sonin variational comparison restricted to tests not already covered by the
valuation-six coefficient cone. -/
def SoninCoupledPrimeArchValuationSixResidualVariationalUpperBound : Prop :=
  ∀ (p : Polynomial ℤ), PrimeArchValuationSixCoefficientResidual p →
    ∀ ε : ℝ, 0 < ε →
      ∃ a : SoninCoupledNondegenerateAperture,
        soninAllPrimeCoupledNormalizedPolynomialGramValue a
            (p.map (Int.castRingHom ℝ)) ≤
          (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re + ε

/-- The unrestricted coupled-Sonin per-test comparison automatically supplies its
valuation-six residual restriction. -/
theorem
    soninCoupledPrimeArchValuationSixResidualVariationalUpperBound_of_perTest
    (h : SoninCoupledPrimeArchPerTestVariationalUpperBound) :
    SoninCoupledPrimeArchValuationSixResidualVariationalUpperBound := by
  intro p _ ε hε
  exact h p ε hε

/-- Exact normalized-value closure supplies the valuation-six residual comparison. -/
theorem
    soninCoupledPrimeArchValuationSixResidualVariationalUpperBound_of_valueClosure
    (h : SoninCoupledPrimeArchPerTestNormalizedValueClosure) :
    SoninCoupledPrimeArchValuationSixResidualVariationalUpperBound :=
  soninCoupledPrimeArchValuationSixResidualVariationalUpperBound_of_perTest
    (soninCoupledPrimeArchPerTestVariationalUpperBound_of_valueClosure h)

/-- Residual coupled-Sonin comparison plus the unconditional cone restores every integer
prime--Gamma Hankel inequality. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_valuationSixResidualVariationalUpperBound
    (h : SoninCoupledPrimeArchValuationSixResidualVariationalUpperBound) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  by_cases hp : PrimeArchValuationSixCoefficientCone p
  · exact re_primeArchSourceTraceHankel_nonneg_of_valuationSixCoefficientCone p hp
  · let q : Polynomial ℝ := p.map (Int.castRingHom ℝ)
    let target : ℝ := (primeArchSourceTraceHankel q).re
    by_contra htarget
    have htargetNeg : target < 0 := lt_of_not_ge htarget
    let ε : ℝ := -target / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    obtain ⟨a, ha⟩ := h p hp ε hε
    have hsource :
        0 ≤ soninAllPrimeCoupledNormalizedPolynomialGramValue a q :=
      soninAllPrimeCoupledNormalizedPolynomialGramValue_nonneg a q
    have htargetε : target + ε < 0 := by
      dsimp [ε]
      linarith
    change soninAllPrimeCoupledNormalizedPolynomialGramValue a q ≤ target + ε at ha
    linarith

/-- **Residual Sonin chain.**  Comparison on the complement of the valuation-six cone implies
RH; no Sonin premise remains on the discharged cone. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchValuationSixResidualVariationalUpperBound
    (h : SoninCoupledPrimeArchValuationSixResidualVariationalUpperBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_valuationSixResidualVariationalUpperBound h)

end

end RHTower
