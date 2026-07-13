import GaloisForLFunctions.RHTower.PrimeArchCanonicalReflectionPositiveEquivalence
import GaloisForLFunctions.RHTower.XiEndpointReflectionNeumannCarrier

/-!
# Prime--archimedean Connes reflection main theorem

This module gathers the quantitative endpoint theorem, the cofinal Neumann reconstruction, and
the reflection-positive Hankel realization into one theorem surface.  Its unconditional part is a
strict source contraction and an all-order holomorphic reconstruction.  Its sharp part identifies
the remaining equality simultaneously with RH, source Hankel positivity, a reflection-positive
Gram orbit, and a self-adjoint vacuum realization.
-/

open Complex

namespace RHTower

noncomputable section

/-- Existence of a reflection-positive Gram orbit for the normalized completed prime--Gamma
moments. -/
def PrimeArchComplexReflectionPositiveGram : Prop :=
  ∃ v : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2,
    ∀ i j, inner ℂ (v i) (v j) =
      (normalizedPrimeArchMoment (i + j) : ℂ)

/-- Existence of a bounded self-adjoint observable and vacuum whose moments are the normalized
completed prime--Gamma moments. -/
def PrimeArchSelfAdjointVacuumRealization : Prop :=
  ∃ (A : lp (fun _ : XiZeroCopy => ℂ) 2 →L[ℂ]
        lp (fun _ : XiZeroCopy => ℂ) 2)
      (omega : lp (fun _ : XiZeroCopy => ℂ) 2),
    IsSelfAdjoint A ∧
    ∀ n, inner ℂ omega ((A ^ n) omega) =
      (normalizedPrimeArchMoment n : ℂ)

/-- Endpoint saturation of the unconditional Hermitian/source norm budget. -/
def PrimeArchEndpointSaturation : Prop :=
  xiRawReciprocalHermitianMass = xiEndpointCompletedCurvature

theorem primeArchEndpointSaturation_iff_riemannHypothesis :
    PrimeArchEndpointSaturation ↔ RiemannHypothesis := by
  rw [PrimeArchEndpointSaturation]
  constructor
  · intro h
    exact xiRawReciprocalHermitianMass_le_endpointCurvature_iff_rh.mp h.le
  · intro hRH
    exact le_antisymm
      (xiRawReciprocalHermitianMass_le_endpointCurvature_iff_rh.mpr hRH)
      xiEndpointCompletedCurvature_le_rawMass

theorem primeArchComplexReflectionPositiveGram_iff_riemannHypothesis :
    PrimeArchComplexReflectionPositiveGram ↔ RiemannHypothesis := by
  simpa only [PrimeArchComplexReflectionPositiveGram] using
    riemannHypothesis_iff_exists_primeArchComplexReflectionPositiveGram.symm

theorem primeArchSelfAdjointVacuumRealization_iff_riemannHypothesis :
    PrimeArchSelfAdjointVacuumRealization ↔ RiemannHypothesis := by
  simpa only [PrimeArchSelfAdjointVacuumRealization] using
    riemannHypothesis_iff_exists_primeArchSelfAdjointVacuumRealization.symm

/-- **Prime--archimedean Connes reflection main theorem.**

The first conjunct is unconditional.  The remaining conjuncts identify the sharp endpoint with
the complete reflection-positive source condition. -/
theorem primeArchConnesReflectionMain :
    ((xiEndpointCompletedCurvature =
          2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) ∧
      0 < xiEndpointCompletedCurvature ∧
      xiEndpointCompletedCurvature < 1 / 2 ∧
      xiEndpointReflectionDefectEnergy ≤
        (xiEndpointCompletedCurvature /
          (1 - xiEndpointCompletedCurvature)) *
            xiEndpointCompletedCurvature ∧
      xiEndpointReflectionDefectEnergy < xiEndpointCompletedCurvature ∧
      xiEndpointCompletedCurvature ≤ xiRawReciprocalHermitianMass ∧
      xiRawReciprocalHermitianMass <
        (3 / 2) * xiEndpointCompletedCurvature ∧
      (∀ q : XiZeroCopy,
        HasSum (fun n : ℕ =>
          -((starRingEnd ℂ) (xiRawReciprocalCoordinate q)) ^ (n + 1))
          (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))) ∧
      HasSum (fun n : ℕ => -xiRawReciprocalPowerTrace (n + 2))
        (-logDeriv XiC (I / 2) / (I / 2))) ∧
    (RiemannHypothesis ↔ xiEndpointReflectionDefectEnergy = 0) ∧
    (RiemannHypothesis ↔ PrimeArchEndpointSaturation) ∧
    (RiemannHypothesis ↔ PrimeArchSourceTraceHankelIntNonnegative) ∧
    (RiemannHypothesis ↔ PrimeArchComplexReflectionPositiveGram) ∧
    (RiemannHypothesis ↔ PrimeArchSelfAdjointVacuumRealization) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨xiEndpointCompletedCurvature_eq_eulerMascheroni_log,
      xiEndpointCompletedCurvature_pos,
      xiEndpointCompletedCurvature_lt_one_half,
      xiEndpointDefectEnergy_le_unconditional_source_factor,
      xiEndpointReflectionDefectEnergy_lt_endpointCurvature,
      xiEndpointCompletedCurvature_le_rawMass,
      xiRawReciprocalHermitianMass_lt_three_halves_mul_endpointCurvature,
      hasSum_xiRawReciprocalCoordinate_lineConj_neumann,
      hasSum_completedEndpointLogDeriv_holomorphicTraces⟩
  · exact xiEndpointReflectionDefectEnergy_eq_zero_iff_rh.symm
  · exact primeArchEndpointSaturation_iff_riemannHypothesis.symm
  · exact primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis.symm
  · exact primeArchComplexReflectionPositiveGram_iff_riemannHypothesis.symm
  · exact primeArchSelfAdjointVacuumRealization_iff_riemannHypothesis.symm

end

end RHTower
