import GaloisForLFunctions.RHTower.XiShiftedAdaptiveOrthogonalSourceJacobiEnergy

/-!
# Corrected null-gauge arithmetic producer for moving shifted-Xi admission

This module joins three already source-native objects before any reflection aggregation:

* the full inverse-null-gauge contact germ;
* its explicit lower-contact memory;
* the rational--Gamma minus von Mangoldt mixed-amplitude formation.

For the current monic orthogonal admission, the corrected coefficient is exactly a positive
odd-contact factor times the Jacobi source energy.  Thus a negative frozen-flag event can occur
only after higher-block positivity fails or after the frozen flag ceases to be the current
admission.  No orientation map or fixed linear reporter occurs.
-/

open Complex Matrix MeasureTheory Set Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Full source-first null-gauge producer after removing only its intrinsic lower-contact memory. -/
def xiShiftedAdaptiveNullGaugeCorrectedArithmeticProducer
    (w : ℝ) (A : Polynomial ℝ) (N : ℕ) : ℝ :=
  2 * PowerSeries.coeff 2
        (xiShiftedAdaptiveNullGaugeSourceSeries
          (xiShiftedRealMomentSequence w) A N) -
    2 * HTGeometry.momentFunctional
      (xiShiftedRealMomentSequence w)
      (xiShiftedAdaptiveNullGaugeLowerResidualPolynomial A N)

/-- The corrected null-gauge coefficient is literally the completed arithmetic source formed from
the same admitted amplitude, multiplied by the forced odd-contact factor. -/
theorem xiShiftedAdaptiveNullGaugeCorrectedArithmeticProducer_eq_arithmeticSource
    {w : ℝ} (hw : 1 / 2 < w) {A : Polynomial ℝ} {N : ℕ}
    (hA : A.Monic) (hAdeg : A.natDegree = N) :
    xiShiftedAdaptiveNullGaugeCorrectedArithmeticProducer w A N =
      ((2 * N + 1 : ℕ) : ℝ) *
        xiShiftedAdaptiveMixedCompletedArithmeticSource w A := by
  rw [xiShiftedAdaptiveNullGaugeCorrectedArithmeticProducer]
  change
    2 * PowerSeries.coeff 2
          (xiShiftedAdaptiveNullGaugeSourceSeries
            (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) A N) -
        2 * HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re)
          (xiShiftedAdaptiveNullGaugeLowerResidualPolynomial A N) = _
  rw [
    two_mul_coeff_two_xiShiftedAdaptiveNullGaugeMomentSourceSeries_sub_lowerResidual_eq_completedPacket
      (sq_pos_of_pos (by linarith : 0 < w)) hA hAdeg,
    xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_arithmeticSource hw]

/-- Exact finite-face producer law for the moving monic admission.  Only the `(n+2)` Hankel block
is assumed positive; no global measure or positive moment form is used. -/
theorem xiShiftedAdaptiveNullGaugeCorrectedArithmeticProducer_monicOrtho_eq_jacobiEnergy_of_hankelPosDef
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    xiShiftedAdaptiveNullGaugeCorrectedArithmeticProducer w
        (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n) n =
      ((2 * n + 1 : ℕ) : ℝ) *
        (2 * HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n *
          HTGeometry.adaptiveOrthoJacobiEnergy (xiShiftedRealMomentSequence w) n) := by
  rw [xiShiftedAdaptiveNullGaugeCorrectedArithmeticProducer_eq_arithmeticSource hw
      (HTGeometry.monicOrtho_monic _ _)
      (HTGeometry.natDegree_monicOrtho_eq _ _),
    xiShiftedAdaptiveMixedCompletedArithmeticSource_monicOrtho_eq_jacobiEnergy_of_hankelPosDef
      hw hn hH]

/-- A single finite positive Hankel block makes the full corrected moving-admission producer
strictly positive. -/
theorem xiShiftedAdaptiveNullGaugeCorrectedArithmeticProducer_monicOrtho_pos_of_hankelPosDef
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    0 < xiShiftedAdaptiveNullGaugeCorrectedArithmeticProducer w
      (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n) n := by
  rw [xiShiftedAdaptiveNullGaugeCorrectedArithmeticProducer_eq_arithmeticSource hw
      (HTGeometry.monicOrtho_monic _ _)
      (HTGeometry.natDegree_monicOrtho_eq _ _)]
  exact mul_pos (by positivity)
    (xiShiftedAdaptiveMixedCompletedArithmeticSource_monicOrtho_pos_of_hankelPosDef
      hw hn hH)

/-- Exact obstruction locus for a negative corrected null-gauge producer.  Inside the next finite
positive Hankel chamber, negativity certifies that the frozen amplitude is not current admission. -/
theorem neg_correctedNullGaugeProducer_forces_hankelFailure_or_admissionMismatch
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    {A : Polynomial ℝ} (hA : A.Monic) (hAdeg : A.natDegree = n)
    (hneg : xiShiftedAdaptiveNullGaugeCorrectedArithmeticProducer w A n < 0) :
    ¬(HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w) (n + 2)).PosDef ∨
      A ≠ HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n := by
  have hfactor : 0 < (((2 * n + 1 : ℕ) : ℝ)) := by positivity
  have hsource : xiShiftedAdaptiveMixedCompletedArithmeticSource w A < 0 := by
    rw [xiShiftedAdaptiveNullGaugeCorrectedArithmeticProducer_eq_arithmeticSource
      hw hA hAdeg] at hneg
    have hlt : (((2 * n + 1 : ℕ) : ℝ)) *
        xiShiftedAdaptiveMixedCompletedArithmeticSource w A <
          (((2 * n + 1 : ℕ) : ℝ)) * 0 := by simpa using hneg
    exact lt_of_mul_lt_mul_left hlt hfactor.le
  exact neg_adaptiveArithmeticSource_forces_hankelFailure_or_admissionMismatch
    hw hn A hsource

/-- A genuine outgoing crossing has only two source-side realizations: a higher finite Hankel block
has already failed, or the transported boundary amplitude has acquired nontrivial admission
holonomy relative to the moving monic orthogonal flag. -/
theorem genuineCrossing_forces_higherHankelFailure_or_admissionHolonomy
    {y : ℝ} (hyquarter : 1 / 4 < y) (hymax : y < 41 / 2)
    {n : ℕ} (hn : 0 < n) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ¬ (xiShiftedMomentHankelMatrix (y - u) (n + 1)).PosSemidef) :
    ∃ m : ℕ, ∃ w : ℝ,
      1 / 2 < w ∧ y < w ^ 2 ∧
      let P := HTGeometry.finiteHankelNullMonicPolynomial c
      let A := P * X ^ m
      ¬(HTGeometry.momentHankelMatrix
          (xiShiftedRealMomentSequence w) (n + m + 2)).PosDef ∨
        A ≠ HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) (n + m) := by
  obtain ⟨m, w, hw, hyw, hneg⟩ :=
    exists_xiShiftedAdaptiveNullGaugeCorrectedSource_neg_on_outgoingRay_of_genuine_crossing
      hyquarter hymax c hhead hc hlast hright hleft
  refine ⟨m, w, hw, hyw, ?_⟩
  dsimp only
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let A := P * X ^ m
  have hP : P.Monic := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg : P.natDegree = n :=
    HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hA : A.Monic := hP.mul (Polynomial.monic_X_pow m)
  have hAdeg : A.natDegree = n + m := by
    dsimp only [A]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow m), hPdeg,
      Polynomial.natDegree_X_pow]
  have hnegProducer :
      xiShiftedAdaptiveNullGaugeCorrectedArithmeticProducer w A (n + m) < 0 := by
    rw [xiShiftedAdaptiveNullGaugeCorrectedArithmeticProducer]
    change
      2 * PowerSeries.coeff 2
            (xiShiftedAdaptiveNullGaugeSourceSeries
              (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) A (n + m)) -
          2 * HTGeometry.momentFunctional
            (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re)
            (xiShiftedAdaptiveNullGaugeLowerResidualPolynomial A (n + m)) < 0
    simpa only [A, P] using hneg
  exact neg_correctedNullGaugeProducer_forces_hankelFailure_or_admissionMismatch
    hw (by omega) hA hAdeg hnegProducer

end

end RHTower
