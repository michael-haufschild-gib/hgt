import GaloisForLFunctions.RHTower.PrimeArchCenteredAnalyticTailVacuumCone
import GaloisForLFunctions.RHTower.PrimeArchThetaHankelDegreeTail

/-!
# Centered Eisenstein residual RH law

The monic `2`-Eisenstein sparse-degree criterion and the centered analytic-tail cone can be
intersected without losing any RH information.  For every infinite set of degrees, it is enough
to prove target normalized-variance nonnegativity only on strict centered residuals which arise as
vacuum tails of monic integer polynomials Eisenstein at `2`.

Consequently any failure of RH produces such a negative-variance residual witness in every
prescribed infinite degree set.  The coupled-Sonin comparison may likewise be restricted to this
same arithmetic residual family.
-/

open Complex Polynomial Filter Topology

namespace RHTower

noncomputable section

/-- Target variance positivity restricted simultaneously to the centered analytic-tail residual
and to vacuum tails of monic `2`-Eisenstein tests in a prescribed degree set. -/
def PrimeArchCenteredTwoEisensteinResidualVarianceNonnegative (D : Set ℕ) : Prop :=
  ∀ P : Polynomial ℤ, P.Monic →
    P.IsEisensteinAt primeArchTwoEisensteinIdeal →
    P.natDegree ∈ D →
    PrimeArchCenteredAnalyticTailResidual (HTGeometry.polynomialVacuumTail P) →
    0 ≤ HTGeometry.momentNormalizedVariance normalizedPrimeArchMoment
      ((HTGeometry.polynomialVacuumTail P).map (Int.castRingHom ℝ))

/-- Nonnegative target variance of an integer polynomial's vacuum tail restores nonnegativity of
the original uncentered trace--Hankel square. -/
theorem re_primeArchSourceTraceHankel_map_nonneg_of_vacuumTail_variance_nonneg
    (P : Polynomial ℤ)
    (hvar : 0 ≤ HTGeometry.momentNormalizedVariance normalizedPrimeArchMoment
      ((HTGeometry.polynomialVacuumTail P).map (Int.castRingHom ℝ))) :
    0 ≤ (primeArchSourceTraceHankel (P.map (Int.castRingHom ℝ))).re := by
  let qz : Polynomial ℤ := HTGeometry.polynomialVacuumTail P
  let q : Polynomial ℝ := qz.map (Int.castRingHom ℝ)
  let c : ℝ := ((P.coeff 0 : ℤ) : ℝ)
  have hrem :
      0 ≤ HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment q := by
    apply (HTGeometry.momentNormalizedVariance_nonneg_iff_feshbach
      normalizedPrimeArchMoment normalizedPrimeArchMoment_zero_pos q).1
    simpa only [q, qz] using hvar
  have hmap : P.map (Int.castRingHom ℝ) = C c + q := by
    have hsplit := congrArg (Polynomial.map (Int.castRingHom ℝ))
      (HTGeometry.C_coeff_zero_add_polynomialVacuumTail P)
    simpa [qz, q, c] using hsplit.symm
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq, hmap,
    HTGeometry.momentFunctional_C_add_sq_eq_vacuumSquare_add_feshbach
      normalizedPrimeArchMoment normalizedPrimeArchMoment_zero_pos.ne']
  exact add_nonneg
    (mul_nonneg normalizedPrimeArchMoment_zero_pos.le (sq_nonneg _)) hrem

/-- The centered residual variance condition restores the uncentered trace--Hankel sign on the
entire selected monic `2`-Eisenstein family. -/
theorem primeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative_of_centeredResidualVariance
    {D : Set ℕ}
    (h : PrimeArchCenteredTwoEisensteinResidualVarianceNonnegative D) :
    PrimeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative D := by
  intro P hmonic heis hdeg
  apply re_primeArchSourceTraceHankel_map_nonneg_of_vacuumTail_variance_nonneg P
  let q : Polynomial ℤ := HTGeometry.polynomialVacuumTail P
  by_cases hres : PrimeArchCenteredAnalyticTailResidual q
  · exact h P hmonic heis hdeg hres
  · apply primeArchNormalizedVariance_nonneg_of_centeredTailL1 q
      (HTGeometry.polynomialVacuumTail_coeff_zero P)
    exact le_of_not_gt hres

/-- On any infinite selected degree set, structured centered residual variance positivity restores
the complete integer prime--Gamma trace--Hankel cone. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_centeredTwoEisensteinResidualVariance
    {D : Set ℕ} (hD : D.Infinite)
    (h : PrimeArchCenteredTwoEisensteinResidualVarianceNonnegative D) :
    PrimeArchSourceTraceHankelIntNonnegative :=
  primeArchSourceTraceHankelIntNonnegative_of_twoEisensteinInfiniteDegreeSet hD
    (primeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative_of_centeredResidualVariance h)

/-- Structured residual variance positivity discharges the complete integer-polynomial
squared-Euler transverse charge. -/
theorem xiSquaredEulerApertureIntChargeDominated_of_centeredTwoEisensteinResidualVariance
    {D : Set ℕ} (hD : D.Infinite)
    (h : PrimeArchCenteredTwoEisensteinResidualVarianceNonnegative D) :
    XiSquaredEulerApertureIntChargeDominated :=
  xiSquaredEulerApertureIntChargeDominated_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_centeredTwoEisensteinResidualVariance hD h)

/-- Structured residual variance positivity discharges complete square-summable Xi Weil
positivity through the all-degree squared-Euler charge connector. -/
theorem xiWeilPolarization_nonneg_of_centeredTwoEisensteinResidualVariance
    {D : Set ℕ} (hD : D.Infinite)
    (h : PrimeArchCenteredTwoEisensteinResidualVarianceNonnegative D) :
    ∀ F : ℂ → ℂ, XiWeilSquareSummable F →
      0 ≤ (xiWeilPolarization F F).re :=
  xiWeilPolarization_nonneg_of_xiSquaredEulerApertureIntChargeDominated
    (xiSquaredEulerApertureIntChargeDominated_of_centeredTwoEisensteinResidualVariance hD h)

/-- Explicit backward chain from the structured centered residual condition through the complete
integer source cone and all-degree squared-Euler charge to RH. -/
theorem riemannHypothesis_of_primeArchCenteredTwoEisensteinResidualVarianceNonnegative
    {D : Set ℕ} (hD : D.Infinite)
    (h : PrimeArchCenteredTwoEisensteinResidualVarianceNonnegative D) :
    RiemannHypothesis :=
  xiSquaredEulerApertureIntChargeDominated_iff_riemannHypothesis.mp
    (xiSquaredEulerApertureIntChargeDominated_of_centeredTwoEisensteinResidualVariance hD h)

/-- **Centered Eisenstein residual RH law.**  For every infinite degree set, the strict centered
residuals of monic `2`-Eisenstein polynomials retain the complete RH obstruction. -/
theorem primeArchCenteredTwoEisensteinResidualVarianceNonnegative_iff_riemannHypothesis
    {D : Set ℕ} (hD : D.Infinite) :
    PrimeArchCenteredTwoEisensteinResidualVarianceNonnegative D ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact
      riemannHypothesis_of_primeArchCenteredTwoEisensteinResidualVarianceNonnegative hD h
  · intro hRH P _hmonic _heis _hdeg _hres
    apply (HTGeometry.momentNormalizedVariance_nonneg_iff_feshbach
      normalizedPrimeArchMoment normalizedPrimeArchMoment_zero_pos _).2
    exact (primeArchVacuumFeshbachIntNonnegative_iff_riemannHypothesis.mpr hRH)
      (HTGeometry.polynomialVacuumTail P)
      (HTGeometry.polynomialVacuumTail_coeff_zero P)

/-- **Structured counterexample replication.**  If RH fails, every prescribed infinite degree
set contains a monic `2`-Eisenstein test whose vacuum tail lies in the strict centered residual and
has negative target normalized variance. -/
theorem exists_centeredTwoEisensteinResidual_negativeVariance_of_not_riemannHypothesis
    {D : Set ℕ} (hD : D.Infinite) (hRH : ¬ RiemannHypothesis) :
    ∃ P : Polynomial ℤ,
      P.Monic ∧
        P.IsEisensteinAt primeArchTwoEisensteinIdeal ∧
          P.natDegree ∈ D ∧
            PrimeArchCenteredAnalyticTailResidual (HTGeometry.polynomialVacuumTail P) ∧
              HTGeometry.momentNormalizedVariance normalizedPrimeArchMoment
                ((HTGeometry.polynomialVacuumTail P).map (Int.castRingHom ℝ)) < 0 := by
  have hnot : ¬ PrimeArchCenteredTwoEisensteinResidualVarianceNonnegative D := by
    intro h
    exact hRH
      ((primeArchCenteredTwoEisensteinResidualVarianceNonnegative_iff_riemannHypothesis hD).mp h)
  simp only [PrimeArchCenteredTwoEisensteinResidualVarianceNonnegative] at hnot
  push Not at hnot
  obtain ⟨P, hmonic, heis, hdeg, hres, hvar⟩ := hnot
  exact ⟨P, hmonic, heis, hdeg, hres, hvar⟩

/-- Degrees which carry a monic `2`-Eisenstein polynomial whose vacuum tail is a strict centered
residual with negative target normalized variance. -/
def primeArchCenteredTwoEisensteinResidualNegativeDegreeSet : Set ℕ :=
  {d | ∃ P : Polynomial ℤ,
    P.Monic ∧
      P.IsEisensteinAt primeArchTwoEisensteinIdeal ∧
        P.natDegree = d ∧
          PrimeArchCenteredAnalyticTailResidual (HTGeometry.polynomialVacuumTail P) ∧
            HTGeometry.momentNormalizedVariance normalizedPrimeArchMoment
              ((HTGeometry.polynomialVacuumTail P).map (Int.castRingHom ℝ)) < 0}

/-- **Cofinite structured counterexample replication.**  If RH fails, all but finitely many
degrees carry a monic `2`-Eisenstein negative centered-residual witness. -/
theorem finite_compl_primeArchCenteredTwoEisensteinResidualNegativeDegreeSet_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    (primeArchCenteredTwoEisensteinResidualNegativeDegreeSetᶜ).Finite := by
  by_contra hfinite
  have hD : (primeArchCenteredTwoEisensteinResidualNegativeDegreeSetᶜ).Infinite := hfinite
  obtain ⟨P, hmonic, heis, hdeg, hres, hvar⟩ :=
    exists_centeredTwoEisensteinResidual_negativeVariance_of_not_riemannHypothesis hD hRH
  have hbad : P.natDegree ∈ primeArchCenteredTwoEisensteinResidualNegativeDegreeSet := by
    exact ⟨P, hmonic, heis, rfl, hres, hvar⟩
  exact hdeg hbad

/-- A per-test coupled-Sonin normalized-variance upper approximation forces target normalized
variance nonnegativity.  No constant-term or source-mass hypothesis is needed. -/
theorem primeArchNormalizedVariance_nonneg_of_soninCoupledUpper
    (q : Polynomial ℤ)
    (hupper : ∀ ε : ℝ, 0 < ε →
      ∃ a : SoninCoupledNondegenerateAperture,
        normalizedPrimeArchMoment 0 *
            HTGeometry.momentNormalizedVariance
              (soninAllPrimeCoupledRealTraceMoment a.1)
              (q.map (Int.castRingHom ℝ)) ≤
          normalizedPrimeArchMoment 0 *
              HTGeometry.momentNormalizedVariance normalizedPrimeArchMoment
                (q.map (Int.castRingHom ℝ)) + ε) :
    0 ≤ HTGeometry.momentNormalizedVariance normalizedPrimeArchMoment
      (q.map (Int.castRingHom ℝ)) := by
  let p : Polynomial ℝ := q.map (Int.castRingHom ℝ)
  let targetVar : ℝ :=
    HTGeometry.momentNormalizedVariance normalizedPrimeArchMoment p
  by_contra htarget
  have htargetNeg : targetVar < 0 := lt_of_not_ge htarget
  let ε : ℝ := -(normalizedPrimeArchMoment 0 * targetVar) / 2
  have hε : 0 < ε := by
    dsimp only [ε]
    linarith [mul_neg_of_pos_of_neg normalizedPrimeArchMoment_zero_pos htargetNeg]
  obtain ⟨a, ha⟩ := hupper ε hε
  have hsourceVar :
      0 ≤ HTGeometry.momentNormalizedVariance
        (soninAllPrimeCoupledRealTraceMoment a.1) p := by
    apply (HTGeometry.momentNormalizedVariance_nonneg_iff_feshbach
      (soninAllPrimeCoupledRealTraceMoment a.1)
      (soninAllPrimeCoupledRealTraceMoment_zero_pos a) p).2
    exact soninAllPrimeCoupledSourceFeshbach_nonneg a p
  have hleft : 0 ≤ normalizedPrimeArchMoment 0 *
      HTGeometry.momentNormalizedVariance
        (soninAllPrimeCoupledRealTraceMoment a.1) p :=
    mul_nonneg normalizedPrimeArchMoment_zero_pos.le hsourceVar
  have hright : normalizedPrimeArchMoment 0 * targetVar + ε < 0 := by
    dsimp only [ε]
    linarith [mul_neg_of_pos_of_neg normalizedPrimeArchMoment_zero_pos htargetNeg]
  change normalizedPrimeArchMoment 0 *
      HTGeometry.momentNormalizedVariance
        (soninAllPrimeCoupledRealTraceMoment a.1) p ≤
    normalizedPrimeArchMoment 0 * targetVar + ε at ha
  linarith

/-- Rightmost coupled-Sonin comparison restricted to structured centered residuals in a selected
degree set. -/
def SoninCoupledPrimeArchCenteredTwoEisensteinResidualNormalizedVarianceUpperBound
    (D : Set ℕ) : Prop :=
  ∀ P : Polynomial ℤ, P.Monic →
    P.IsEisensteinAt primeArchTwoEisensteinIdeal →
    P.natDegree ∈ D →
    PrimeArchCenteredAnalyticTailResidual (HTGeometry.polynomialVacuumTail P) →
    ∀ ε : ℝ, 0 < ε →
      ∃ a : SoninCoupledNondegenerateAperture,
        normalizedPrimeArchMoment 0 *
            HTGeometry.momentNormalizedVariance
              (soninAllPrimeCoupledRealTraceMoment a.1)
              ((HTGeometry.polynomialVacuumTail P).map (Int.castRingHom ℝ)) ≤
          normalizedPrimeArchMoment 0 *
              HTGeometry.momentNormalizedVariance normalizedPrimeArchMoment
                ((HTGeometry.polynomialVacuumTail P).map (Int.castRingHom ℝ)) + ε

/-- The structured coupled-Sonin upper comparison supplies the complete restricted target
variance condition. -/
theorem primeArchCenteredTwoEisensteinResidualVarianceNonnegative_of_soninCoupledUpper
    {D : Set ℕ}
    (h : SoninCoupledPrimeArchCenteredTwoEisensteinResidualNormalizedVarianceUpperBound D) :
    PrimeArchCenteredTwoEisensteinResidualVarianceNonnegative D := by
  intro P hmonic heis hdeg hres
  exact primeArchNormalizedVariance_nonneg_of_soninCoupledUpper
    (HTGeometry.polynomialVacuumTail P) (h P hmonic heis hdeg hres)

/-- **Structured centered-residual Sonin chain to RH.**  For any infinite chosen degree set, no
source comparison is required outside monic `2`-Eisenstein vacuum tails in the strict residual. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchCenteredTwoEisensteinResidualUpper
    {D : Set ℕ} (hD : D.Infinite)
    (h : SoninCoupledPrimeArchCenteredTwoEisensteinResidualNormalizedVarianceUpperBound D) :
    RiemannHypothesis :=
  (primeArchCenteredTwoEisensteinResidualVarianceNonnegative_iff_riemannHypothesis hD).mp
    (primeArchCenteredTwoEisensteinResidualVarianceNonnegative_of_soninCoupledUpper h)

end

end RHTower
