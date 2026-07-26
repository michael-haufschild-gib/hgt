import GaloisForLFunctions.RHTower.PrimeArchCenteredEisensteinResidual
import GaloisForLFunctions.RHTower.PrimeArchCoefficientSignCone
import GaloisForLFunctions.RHTower.PrimeArchValuationSectorCones

/-!
# Combined prime--Gamma residual Sonin criterion

Three source-positive families are available unconditionally:

* the valuation-zero-through-six sector coefficient cones;
* degree-at-most-nine polynomials with nonnegative self-convolution coefficients;
* tests whose vacuum tail lies in the centered analytic `l1` cone.

The sparse-degree Eisenstein reduction can be applied after removing all three families. Thus the
coupled-Sonin comparison is needed only for monic `2`-Eisenstein tests in an arbitrary infinite
degree set which simultaneously avoid every valuation cone and the degree-nine
square-coefficient cone, and whose vacuum tails lie in the strict centered residual.

The counterexample theorem records the corresponding source fact: if RH fails, every infinite
degree set contains a negative prime--Gamma Hankel test in this combined residual.

Under emptiness of the two explicit centered source annuli, the square-coefficient family extends
to degree ten. The corresponding smaller residual criterion and its RH equivalence are recorded
without replacing the unconditional degree-nine result.
-/

open Polynomial

namespace RHTower

noncomputable section

/-- A single-test coupled-Sonin variational upper bound transfers positivity to that test. -/
theorem re_primeArchSourceTraceHankel_map_nonneg_of_soninCoupledVariationalUpper
    (p : Polynomial ℤ)
    (hupper : ∀ ε : ℝ, 0 < ε →
      ∃ a : SoninCoupledNondegenerateAperture,
        soninAllPrimeCoupledNormalizedPolynomialGramValue a
            (p.map (Int.castRingHom ℝ)) ≤
          (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re + ε) :
    0 ≤ (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re := by
  let q : Polynomial ℝ := p.map (Int.castRingHom ℝ)
  let target : ℝ := (primeArchSourceTraceHankel q).re
  by_contra htarget
  have htargetNeg : target < 0 := lt_of_not_ge htarget
  let ε : ℝ := -target / 2
  have hε : 0 < ε := by
    dsimp only [ε]
    linarith
  obtain ⟨a, ha⟩ := hupper ε hε
  have hsource :
      0 ≤ soninAllPrimeCoupledNormalizedPolynomialGramValue a q :=
    soninAllPrimeCoupledNormalizedPolynomialGramValue_nonneg a q
  have htargetε : target + ε < 0 := by
    dsimp only [ε]
    linarith
  change soninAllPrimeCoupledNormalizedPolynomialGramValue a q ≤ target + ε at ha
  linarith

/-- Tests outside all three unconditional source-positive coefficient families. -/
def PrimeArchCombinedCoefficientResidual (p : Polynomial ℤ) : Prop :=
  PrimeArchDegreeNineSquareCoeffResidual p ∧
    PrimeArchCenteredAnalyticTailResidual (HTGeometry.polynomialVacuumTail p) ∧
      PrimeArchValuationAtMostSixCoefficientResidual p

/-- Tests outside all three source-positive families after the explicit centered annuli have
extended the square-coefficient cone through degree ten. -/
def PrimeArchDegreeTenCombinedCoefficientResidual (p : Polynomial ℤ) : Prop :=
  PrimeArchDegreeTenSquareCoeffResidual p ∧
    PrimeArchCenteredAnalyticTailResidual (HTGeometry.polynomialVacuumTail p) ∧
      PrimeArchValuationAtMostSixCoefficientResidual p

/-- The degree-ten combined residual is contained in the unconditional degree-nine residual. -/
theorem primeArchCombinedCoefficientResidual_of_degreeTenCombined
    {p : Polynomial ℤ} (hp : PrimeArchDegreeTenCombinedCoefficientResidual p) :
    PrimeArchCombinedCoefficientResidual p := by
  refine ⟨?_, hp.2⟩
  intro h9
  exact hp.1 (primeArchDegreeTenSquareCoeffCone_of_degreeNineSquareCoeffCone h9)

/-- The concrete degree-seven endpoint-pair test is monic. -/
theorem primeArchDegreeSevenEndpointPolynomial_monic :
    primeArchDegreeSevenEndpointPolynomial.Monic := by
  let lower : Polynomial ℤ := C 2 + C 12 * X ^ 6
  have hlow : lower.natDegree < 7 := by
    apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
    rw [max_lt_iff]
    constructor
    · simp
    · rw [Polynomial.natDegree_C_mul_X_pow 6 12 (by norm_num)]
      omega
  have hlowDegree : lower.degree < (7 : WithBot ℕ) := by
    by_cases hzero : lower = 0
    · rw [hzero, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe 7
    · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mp hlow
  unfold primeArchDegreeSevenEndpointPolynomial
  rw [add_assoc]
  change (X ^ 7 + lower).Monic
  exact Polynomial.monic_X_pow_add hlowDegree

/-- The concrete degree-seven endpoint-pair test is Eisenstein at two. -/
theorem primeArchDegreeSevenEndpointPolynomial_twoEisenstein :
    primeArchDegreeSevenEndpointPolynomial.IsEisensteinAt
      primeArchTwoEisensteinIdeal := by
  simpa only [primeArchDegreeSevenEndpointPolynomial,
    show (4 * (3 : ℤ)) = 12 by norm_num] using
      primeArch_twoEisenstein_plus (X ^ 6 : Polynomial ℤ) 7 3 (by simp)

/-- The new source theorem removes a genuine monic two-Eisenstein degree-seven test from the
combined Sonin residual. -/
theorem primeArchDegreeSevenEndpointPolynomial_not_combinedResidual :
    ¬ PrimeArchCombinedCoefficientResidual
      primeArchDegreeSevenEndpointPolynomial := by
  intro h
  exact h.1
    (primeArchDegreeNineSquareCoeffCone_of_degreeEightSquareCoeffCone
      (primeArchDegreeEightSquareCoeffCone_of_degreeSevenSquareCoeffCone
        (primeArchDegreeSevenSquareCoeffCone_of_endpointPair
          primeArchDegreeSevenEndpointPolynomial_mem)))

/-- The concrete degree-eight square-coefficient test is monic. -/
theorem primeArchDegreeEightSquareCoeffPolynomial_monic :
    primeArchDegreeEightSquareCoeffPolynomial.Monic := by
  let lower : Polynomial ℤ := C 2 + C 12 * X ^ 7
  have hlow : lower.natDegree < 8 := by
    apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
    rw [max_lt_iff]
    constructor
    · simp
    · rw [Polynomial.natDegree_C_mul_X_pow 7 12 (by norm_num)]
      omega
  have hlowDegree : lower.degree < (8 : WithBot ℕ) := by
    by_cases hzero : lower = 0
    · rw [hzero, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe 8
    · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mp hlow
  unfold primeArchDegreeEightSquareCoeffPolynomial
  rw [add_assoc]
  change (X ^ 8 + lower).Monic
  exact Polynomial.monic_X_pow_add hlowDegree

/-- The concrete degree-eight square-coefficient test is Eisenstein at two. -/
theorem primeArchDegreeEightSquareCoeffPolynomial_twoEisenstein :
    primeArchDegreeEightSquareCoeffPolynomial.IsEisensteinAt
      primeArchTwoEisensteinIdeal := by
  simpa only [primeArchDegreeEightSquareCoeffPolynomial,
    show (4 * (3 : ℤ)) = 12 by norm_num] using
      primeArch_twoEisenstein_plus (X ^ 7 : Polynomial ℤ) 8 3 (by simp)

/-- The source theorem removes a genuine monic two-Eisenstein degree-eight test from the
combined Sonin residual. -/
theorem primeArchDegreeEightSquareCoeffPolynomial_not_combinedResidual :
    ¬ PrimeArchCombinedCoefficientResidual
      primeArchDegreeEightSquareCoeffPolynomial := by
  intro h
  exact h.1
    (primeArchDegreeNineSquareCoeffCone_of_degreeEightSquareCoeffCone
      primeArchDegreeEightSquareCoeffPolynomial_mem)

/-- The concrete degree-nine square-coefficient test is monic. -/
theorem primeArchDegreeNineSquareCoeffPolynomial_monic :
    primeArchDegreeNineSquareCoeffPolynomial.Monic := by
  let lower : Polynomial ℤ := C 2 + C 12 * X ^ 8
  have hlow : lower.natDegree < 9 := by
    apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
    rw [max_lt_iff]
    constructor
    · simp
    · rw [Polynomial.natDegree_C_mul_X_pow 8 12 (by norm_num)]
      omega
  have hlowDegree : lower.degree < (9 : WithBot ℕ) := by
    by_cases hzero : lower = 0
    · rw [hzero, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe 9
    · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mp hlow
  unfold primeArchDegreeNineSquareCoeffPolynomial
  rw [add_assoc]
  change (X ^ 9 + lower).Monic
  exact Polynomial.monic_X_pow_add hlowDegree

/-- The concrete degree-nine square-coefficient test is Eisenstein at two. -/
theorem primeArchDegreeNineSquareCoeffPolynomial_twoEisenstein :
    primeArchDegreeNineSquareCoeffPolynomial.IsEisensteinAt
      primeArchTwoEisensteinIdeal := by
  simpa only [primeArchDegreeNineSquareCoeffPolynomial,
    show (4 * (3 : ℤ)) = 12 by norm_num] using
      primeArch_twoEisenstein_plus (X ^ 8 : Polynomial ℤ) 9 3 (by simp)

/-- The source theorem removes a genuine monic two-Eisenstein degree-nine test from the
combined Sonin residual. -/
theorem primeArchDegreeNineSquareCoeffPolynomial_not_combinedResidual :
    ¬ PrimeArchCombinedCoefficientResidual
      primeArchDegreeNineSquareCoeffPolynomial := by
  intro h
  exact h.1 primeArchDegreeNineSquareCoeffPolynomial_mem

/-- The concrete degree-ten square-coefficient test is monic. -/
theorem primeArchDegreeTenSquareCoeffPolynomial_monic :
    primeArchDegreeTenSquareCoeffPolynomial.Monic := by
  let lower : Polynomial ℤ := C 2 + C 12 * X ^ 9
  have hlow : lower.natDegree < 10 := by
    apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
    rw [max_lt_iff]
    constructor
    · simp
    · rw [Polynomial.natDegree_C_mul_X_pow 9 12 (by norm_num)]
      omega
  have hlowDegree : lower.degree < (10 : WithBot ℕ) := by
    by_cases hzero : lower = 0
    · rw [hzero, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe 10
    · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mp hlow
  unfold primeArchDegreeTenSquareCoeffPolynomial
  rw [add_assoc]
  change (X ^ 10 + lower).Monic
  exact Polynomial.monic_X_pow_add hlowDegree

/-- The concrete degree-ten square-coefficient test is Eisenstein at two. -/
theorem primeArchDegreeTenSquareCoeffPolynomial_twoEisenstein :
    primeArchDegreeTenSquareCoeffPolynomial.IsEisensteinAt
      primeArchTwoEisensteinIdeal := by
  simpa only [primeArchDegreeTenSquareCoeffPolynomial,
    show (4 * (3 : ℤ)) = 12 by norm_num] using
      primeArch_twoEisenstein_plus (X ^ 9 : Polynomial ℤ) 10 3 (by simp)

/-- The source-annulus result removes a genuine monic two-Eisenstein degree-ten test from the
degree-ten combined Sonin residual. -/
theorem primeArchDegreeTenSquareCoeffPolynomial_not_degreeTenCombinedResidual :
    ¬ PrimeArchDegreeTenCombinedCoefficientResidual
      primeArchDegreeTenSquareCoeffPolynomial := by
  intro h
  exact h.1 primeArchDegreeTenSquareCoeffPolynomial_mem

/-- Prime--Gamma positivity restricted to the combined residual inside one sparse
monic-`2`-Eisenstein degree family. -/
def PrimeArchCombinedResidualTwoEisensteinDegreeSetNonnegative
    (D : Set ℕ) : Prop :=
  ∀ p : Polynomial ℤ, p.Monic →
    p.IsEisensteinAt primeArchTwoEisensteinIdeal →
    p.natDegree ∈ D →
    PrimeArchCombinedCoefficientResidual p →
      0 ≤ (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re

/-- Positivity on the combined residual restores positivity on the full selected
monic-`2`-Eisenstein family. -/
theorem primeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative_of_combinedResidual
    {D : Set ℕ}
    (h : PrimeArchCombinedResidualTwoEisensteinDegreeSetNonnegative D) :
    PrimeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative D := by
  intro p hmonic heis hdeg
  by_cases hsquare : PrimeArchDegreeNineSquareCoeffCone p
  · exact re_primeArchSourceTraceHankel_nonneg_of_degreeNineSquareCoeffCone p hsquare
  · by_cases hvaluation : PrimeArchValuationAtMostSixCoefficientCone p
    · exact
        re_primeArchSourceTraceHankel_nonneg_of_valuationAtMostSixCoefficientCone
          p hvaluation
    · let q : Polynomial ℤ := HTGeometry.polynomialVacuumTail p
      by_cases hcentered : PrimeArchCenteredAnalyticTailResidual q
      · exact h p hmonic heis hdeg ⟨hsquare, hcentered, hvaluation⟩
      · apply re_primeArchSourceTraceHankel_map_nonneg_of_vacuumTail_variance_nonneg p
        apply primeArchNormalizedVariance_nonneg_of_centeredTailL1 q
          (HTGeometry.polynomialVacuumTail_coeff_zero p)
        exact le_of_not_gt hcentered

/-- On every infinite degree set, positivity only on the combined residual is equivalent to RH. -/
theorem primeArchCombinedResidualTwoEisensteinDegreeSetNonnegative_iff_riemannHypothesis
    {D : Set ℕ} (hD : D.Infinite) :
    PrimeArchCombinedResidualTwoEisensteinDegreeSetNonnegative D ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact
      (primeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative_iff_riemannHypothesis
        hD).mp
        (primeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative_of_combinedResidual h)
  · intro hRH p _hmonic _heis _hdeg _hresidual
    exact
      (primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis.mpr hRH) p

/-- Failure of RH produces a negative source-Hankel test in the combined residual inside every
infinite prescribed degree set. -/
theorem exists_combinedResidualTwoEisenstein_negativeTraceHankel_of_not_riemannHypothesis
    {D : Set ℕ} (hD : D.Infinite) (hRH : ¬ RiemannHypothesis) :
    ∃ p : Polynomial ℤ,
      p.Monic ∧
        p.IsEisensteinAt primeArchTwoEisensteinIdeal ∧
          p.natDegree ∈ D ∧
            PrimeArchCombinedCoefficientResidual p ∧
              (primeArchSourceTraceHankel
                (p.map (Int.castRingHom ℝ))).re < 0 := by
  have hnot :
      ¬ PrimeArchCombinedResidualTwoEisensteinDegreeSetNonnegative D := by
    intro h
    exact hRH
      ((primeArchCombinedResidualTwoEisensteinDegreeSetNonnegative_iff_riemannHypothesis
        hD).mp h)
  simp only [PrimeArchCombinedResidualTwoEisensteinDegreeSetNonnegative] at hnot
  push Not at hnot
  exact hnot

/-- Coupled-Sonin comparison restricted to the combined residual inside one selected sparse
monic-`2`-Eisenstein degree family. -/
def SoninCoupledPrimeArchCombinedResidualVariationalUpperBound
    (D : Set ℕ) : Prop :=
  ∀ p : Polynomial ℤ, p.Monic →
    p.IsEisensteinAt primeArchTwoEisensteinIdeal →
    p.natDegree ∈ D →
    PrimeArchCombinedCoefficientResidual p →
    ∀ ε : ℝ, 0 < ε →
      ∃ a : SoninCoupledNondegenerateAperture,
        soninAllPrimeCoupledNormalizedPolynomialGramValue a
            (p.map (Int.castRingHom ℝ)) ≤
          (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re + ε

/-- The original per-test coupled-Sonin interface supplies the combined residual interface. -/
theorem soninCoupledPrimeArchCombinedResidualVariationalUpperBound_of_perTest
    {D : Set ℕ}
    (h : SoninCoupledPrimeArchPerTestVariationalUpperBound) :
    SoninCoupledPrimeArchCombinedResidualVariationalUpperBound D := by
  intro p _hmonic _heis _hdeg _hresidual ε hε
  exact h p ε hε

/-- The valuation-residual coupled-Sonin interface also supplies the combined residual
interface. -/
theorem soninCoupledPrimeArchCombinedResidualVariationalUpperBound_of_valuationResidual
    {D : Set ℕ}
    (h : SoninCoupledPrimeArchValuationAtMostSixResidualVariationalUpperBound) :
    SoninCoupledPrimeArchCombinedResidualVariationalUpperBound D := by
  intro p _hmonic _heis _hdeg hresidual ε hε
  exact h p hresidual.2.2 ε hε

/-- Combined-residual Sonin comparison supplies positivity on every retained test. -/
theorem primeArchCombinedResidualTwoEisensteinDegreeSetNonnegative_of_soninCoupledUpper
    {D : Set ℕ}
    (h : SoninCoupledPrimeArchCombinedResidualVariationalUpperBound D) :
    PrimeArchCombinedResidualTwoEisensteinDegreeSetNonnegative D := by
  intro p hmonic heis hdeg hresidual
  exact re_primeArchSourceTraceHankel_map_nonneg_of_soninCoupledVariationalUpper
    p (h p hmonic heis hdeg hresidual)

/-- The structured centered-variance Sonin interface supplies positivity on the smaller combined
residual family directly. -/
theorem primeArchCombinedResidualTwoEisensteinDegreeSetNonnegative_of_centeredVarianceUpper
    {D : Set ℕ}
    (h : SoninCoupledPrimeArchCenteredTwoEisensteinResidualNormalizedVarianceUpperBound D) :
    PrimeArchCombinedResidualTwoEisensteinDegreeSetNonnegative D := by
  intro p hmonic heis hdeg hresidual
  apply re_primeArchSourceTraceHankel_map_nonneg_of_vacuumTail_variance_nonneg p
  exact primeArchNormalizedVariance_nonneg_of_soninCoupledUpper
    (HTGeometry.polynomialVacuumTail p)
    (h p hmonic heis hdeg hresidual.2.1)

/-- The unrestricted centered-residual Sonin interface also supplies every test in the combined
residual family. -/
theorem primeArchCombinedResidualTwoEisensteinDegreeSetNonnegative_of_centeredResidualUpper
    {D : Set ℕ}
    (h : SoninCoupledPrimeArchCenteredResidualNormalizedVarianceUpperBound) :
    PrimeArchCombinedResidualTwoEisensteinDegreeSetNonnegative D := by
  intro p _hmonic _heis _hdeg hresidual
  apply re_primeArchSourceTraceHankel_map_nonneg_of_vacuumTail_variance_nonneg p
  exact primeArchNormalizedVariance_nonneg_of_soninCoupledUpper
    (HTGeometry.polynomialVacuumTail p)
    (h (HTGeometry.polynomialVacuumTail p)
      (HTGeometry.polynomialVacuumTail_coeff_zero p) hresidual.2.1)

/-- Coupled-Sonin comparison only on the combined residual in any infinite degree set implies
RH. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchCombinedResidualVariationalUpperBound
    {D : Set ℕ} (hD : D.Infinite)
    (h : SoninCoupledPrimeArchCombinedResidualVariationalUpperBound D) :
    RiemannHypothesis :=
  (primeArchCombinedResidualTwoEisensteinDegreeSetNonnegative_iff_riemannHypothesis hD).mp
    (primeArchCombinedResidualTwoEisensteinDegreeSetNonnegative_of_soninCoupledUpper h)

/-- Prime--Gamma positivity restricted to the degree-ten combined residual inside one sparse
monic-`2`-Eisenstein degree family. -/
def PrimeArchDegreeTenCombinedResidualTwoEisensteinDegreeSetNonnegative
    (D : Set ℕ) : Prop :=
  ∀ p : Polynomial ℤ, p.Monic →
    p.IsEisensteinAt primeArchTwoEisensteinIdeal →
    p.natDegree ∈ D →
    PrimeArchDegreeTenCombinedCoefficientResidual p →
      0 ≤ (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re

/-- Under the exact source-annulus premise, positivity on the smaller degree-ten combined
residual restores positivity on the full selected monic-`2`-Eisenstein family. -/
theorem primeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative_of_degreeTenCombinedResidual
    {D : Set ℕ}
    (hannuli : XiCenteredDegreeTenResidualAnnuliEmpty)
    (h : PrimeArchDegreeTenCombinedResidualTwoEisensteinDegreeSetNonnegative D) :
    PrimeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative D := by
  intro p hmonic heis hdeg
  by_cases hsquare : PrimeArchDegreeTenSquareCoeffCone p
  · exact
      re_primeArchSourceTraceHankel_nonneg_of_degreeTenSquareCoeffCone
        hannuli p hsquare
  · by_cases hvaluation : PrimeArchValuationAtMostSixCoefficientCone p
    · exact
        re_primeArchSourceTraceHankel_nonneg_of_valuationAtMostSixCoefficientCone
          p hvaluation
    · let q : Polynomial ℤ := HTGeometry.polynomialVacuumTail p
      by_cases hcentered : PrimeArchCenteredAnalyticTailResidual q
      · exact h p hmonic heis hdeg ⟨hsquare, hcentered, hvaluation⟩
      · apply re_primeArchSourceTraceHankel_map_nonneg_of_vacuumTail_variance_nonneg p
        apply primeArchNormalizedVariance_nonneg_of_centeredTailL1 q
          (HTGeometry.polynomialVacuumTail_coeff_zero p)
        exact le_of_not_gt hcentered

/-- Under the exact source-annulus premise, positivity on the degree-ten combined residual in
every infinite degree set is equivalent to RH. -/
theorem
    primeArchDegreeTenCombinedResidualTwoEisensteinDegreeSetNonnegative_iff_riemannHypothesis
    {D : Set ℕ} (hannuli : XiCenteredDegreeTenResidualAnnuliEmpty)
    (hD : D.Infinite) :
    PrimeArchDegreeTenCombinedResidualTwoEisensteinDegreeSetNonnegative D ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact
      (primeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative_iff_riemannHypothesis
        hD).mp
        (primeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative_of_degreeTenCombinedResidual
          hannuli h)
  · intro hRH p _hmonic _heis _hdeg _hresidual
    exact
      (primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis.mpr hRH) p

/-- Failure of RH produces a negative source-Hankel test in the degree-ten combined residual
inside every infinite prescribed degree set, assuming the exact source annuli are empty. -/
theorem exists_degreeTenCombinedResidualTwoEisenstein_negativeTraceHankel_of_not_riemannHypothesis
    {D : Set ℕ} (hannuli : XiCenteredDegreeTenResidualAnnuliEmpty)
    (hD : D.Infinite) (hRH : ¬ RiemannHypothesis) :
    ∃ p : Polynomial ℤ,
      p.Monic ∧
        p.IsEisensteinAt primeArchTwoEisensteinIdeal ∧
          p.natDegree ∈ D ∧
            PrimeArchDegreeTenCombinedCoefficientResidual p ∧
              (primeArchSourceTraceHankel
                (p.map (Int.castRingHom ℝ))).re < 0 := by
  have hnot :
      ¬ PrimeArchDegreeTenCombinedResidualTwoEisensteinDegreeSetNonnegative D := by
    intro h
    exact hRH
      ((primeArchDegreeTenCombinedResidualTwoEisensteinDegreeSetNonnegative_iff_riemannHypothesis
        hannuli hD).mp h)
  simp only [PrimeArchDegreeTenCombinedResidualTwoEisensteinDegreeSetNonnegative] at hnot
  push Not at hnot
  exact hnot

/-- Coupled-Sonin comparison restricted to the degree-ten combined residual inside one selected
sparse monic-`2`-Eisenstein degree family. -/
def SoninCoupledPrimeArchDegreeTenCombinedResidualVariationalUpperBound
    (D : Set ℕ) : Prop :=
  ∀ p : Polynomial ℤ, p.Monic →
    p.IsEisensteinAt primeArchTwoEisensteinIdeal →
    p.natDegree ∈ D →
    PrimeArchDegreeTenCombinedCoefficientResidual p →
    ∀ ε : ℝ, 0 < ε →
      ∃ a : SoninCoupledNondegenerateAperture,
        soninAllPrimeCoupledNormalizedPolynomialGramValue a
            (p.map (Int.castRingHom ℝ)) ≤
          (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re + ε

/-- The unconditional combined-residual Sonin interface supplies the smaller degree-ten
combined-residual interface. -/
theorem soninCoupledPrimeArchDegreeTenCombinedResidualVariationalUpperBound_of_combinedResidual
    {D : Set ℕ}
    (h : SoninCoupledPrimeArchCombinedResidualVariationalUpperBound D) :
    SoninCoupledPrimeArchDegreeTenCombinedResidualVariationalUpperBound D := by
  intro p hmonic heis hdeg hresidual ε hε
  exact h p hmonic heis hdeg
    (primeArchCombinedCoefficientResidual_of_degreeTenCombined hresidual) ε hε

/-- Degree-ten combined-residual Sonin comparison supplies positivity on every retained test. -/
theorem
    primeArchDegreeTenCombinedResidualTwoEisensteinDegreeSetNonnegative_of_soninCoupledUpper
    {D : Set ℕ}
    (h : SoninCoupledPrimeArchDegreeTenCombinedResidualVariationalUpperBound D) :
    PrimeArchDegreeTenCombinedResidualTwoEisensteinDegreeSetNonnegative D := by
  intro p hmonic heis hdeg hresidual
  exact re_primeArchSourceTraceHankel_map_nonneg_of_soninCoupledVariationalUpper
    p (h p hmonic heis hdeg hresidual)

/-- Under the exact source-annulus premise, coupled-Sonin comparison only on the degree-ten
combined residual in any infinite degree set implies RH. -/
theorem
    riemannHypothesis_of_soninCoupledPrimeArchDegreeTenCombinedResidualVariationalUpperBound
    {D : Set ℕ} (hannuli : XiCenteredDegreeTenResidualAnnuliEmpty)
    (hD : D.Infinite)
    (h : SoninCoupledPrimeArchDegreeTenCombinedResidualVariationalUpperBound D) :
    RiemannHypothesis :=
  (primeArchDegreeTenCombinedResidualTwoEisensteinDegreeSetNonnegative_iff_riemannHypothesis
    hannuli hD).mp
    (primeArchDegreeTenCombinedResidualTwoEisensteinDegreeSetNonnegative_of_soninCoupledUpper h)

end

end RHTower
