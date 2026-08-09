import GaloisForLFunctions.HTGeometry.OccupiedBuresTargetBodyLaw
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Bures equilibrium observer tilts

Every positive-definite reporter is an exponential of a Hermitian observable.
The inverse channel is the opposite exponential tilt.  This module exposes
complete and return-excised incidence certificates for every bounded occupied
target family.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MeasureTheory Matrix Set
open scoped ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-! ## Hermitian opposite-tilt reporters -/

/-- Exponentiating a Hermitian finite-dimensional observable produces a
positive-definite reporter. -/
theorem finiteBuresReporterExp_posDef
    {n : ℕ} {W : Matrix (Fin n) (Fin n) ℂ} (hW : W.IsHermitian) :
    (NormedSpace.exp W).PosDef := by
  have hnonneg : 0 ≤ NormedSpace.exp W :=
    hW.isSelfAdjoint.exp_nonneg
  have hpsd : (NormedSpace.exp W).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hnonneg
  exact hpsd.posDef_iff_isUnit.mpr (Matrix.isUnit_exp W)

/-- Every positive-definite matrix reporter is the exponential of a Hermitian
observable; no reporter is lost by the opposite-tilt parameterization. -/
theorem exists_finiteBuresHermitian_exp_eq_reporter
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ∃ W : Matrix (Fin n) (Fin n) ℂ, W.IsHermitian ∧
      NormedSpace.exp W = A := by
  refine ⟨CFC.log A, IsSelfAdjoint.log.isHermitian, ?_⟩
  exact CFC.exp_log A hA.isStrictlyPositive

/-- The inverse reporter channel is exactly the exponential of the opposite
Hermitian tilt. -/
theorem finiteBuresTargetLeverage_exp_eq_oppositeTilt
    {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    finiteBuresTargetLeverage (NormedSpace.exp W) v =
      (star v ⬝ᵥ (NormedSpace.exp (-W) *ᵥ v)).re := by
  unfold finiteBuresTargetLeverage
  rw [Matrix.exp_neg]

/-- **Opposite-tilt complete-incidence certificate.**  Every Hermitian
observable gives one unconditional source--target reporter bound for an
arbitrary bounded occupied image. -/
theorem finiteBures_completeIncidence_oppositeTilt_bound
    {X C : Type*} [MeasurableSpace X] [Nonempty C] {n : ℕ}
    (mu : Measure X) [IsFiniteMeasure mu]
    (target : C → Fin n → ℂ) (state : X → Fin n → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : W.IsHermitian)
    (hTargetBounded : Bornology.IsBounded (Set.range target))
    (hprod : ∀ i j, Integrable
      (fun x ↦ state x i * star (state x j)) mu) :
    threshold * mu.real
        (finitePositiveReporterCaptureEvent target state threshold) ≤
      finiteBuresSourcePairing
          (finitePositiveReporterSourceCovariance mu state)
          (NormedSpace.exp W) *
        finiteBuresOccupiedTargetMaximum
          (NormedSpace.exp W) (Set.range target) := by
  let A : Matrix (Fin n) (Fin n) ℂ := NormedSpace.exp W
  let B : ℝ := finiteBuresOccupiedTargetMaximum A (Set.range target)
  have hA : A.PosDef := finiteBuresReporterExp_posDef hW
  have hceiling : ∀ c,
      finitePositiveReporterTargetLeverage A (target c) ≤ B := by
    intro c
    exact finiteBuresTargetLeverage_le_occupiedTargetMaximum_of_isBounded
      A hTargetBounded (Set.mem_range_self c)
  let c0 : C := Classical.choice inferInstance
  have hBnonneg : 0 ≤ B :=
    (finitePositiveReporterTargetLeverage_nonneg hA (target c0)).trans
      (hceiling c0)
  have h := finitePositiveReporter_completeIncidence_covariance_bound
    mu A hA target state threshold hthreshold B hBnonneg hceiling
      (finitePositiveReporterSourceEnergy_integrable mu state A hprod) hprod
  simpa [A, B, finiteBuresSourcePairing, mul_comm] using h

/-- Return-excised opposite-tilt certificate.  Return mass is paid once and
the source channel is integrated only on the independently fixed complement. -/
theorem finiteBures_returnExcisedIncidence_oppositeTilt_bound
    {X C : Type*} [MeasurableSpace X] [Nonempty C] {n : ℕ}
    (mu : Measure X) [IsFiniteMeasure mu]
    (target : C → Fin n → ℂ) (state : X → Fin n → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : W.IsHermitian)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hTargetBounded : Bornology.IsBounded (Set.range target))
    (hprod : ∀ i j, Integrable
      (fun x ↦ state x i * star (state x j))
        (mu.restrict returnSetᶜ)) :
    mu.real (finitePositiveReporterCaptureEvent target state threshold) ≤
      mu.real returnSet +
        (finiteBuresSourcePairing
            (finitePositiveReporterSourceCovariance
              (mu.restrict returnSetᶜ) state)
            (NormedSpace.exp W) *
          finiteBuresOccupiedTargetMaximum
            (NormedSpace.exp W) (Set.range target)) / threshold := by
  let A : Matrix (Fin n) (Fin n) ℂ := NormedSpace.exp W
  let B : ℝ := finiteBuresOccupiedTargetMaximum A (Set.range target)
  have hA : A.PosDef := finiteBuresReporterExp_posDef hW
  have hceiling : ∀ c,
      finitePositiveReporterTargetLeverage A (target c) ≤ B := by
    intro c
    exact finiteBuresTargetLeverage_le_occupiedTargetMaximum_of_isBounded
      A hTargetBounded (Set.mem_range_self c)
  let c0 : C := Classical.choice inferInstance
  have hBnonneg : 0 ≤ B :=
    (finitePositiveReporterTargetLeverage_nonneg hA (target c0)).trans
      (hceiling c0)
  have hint := finitePositiveReporterSourceEnergy_integrable
    (mu.restrict returnSetᶜ) state A hprod
  have h := finitePositiveReporter_returnExcisedIncidence_bound
    mu A hA target state threshold hthreshold B hBnonneg hceiling
      returnSet hreturn hint
  rw [← finitePositiveReporter_re_trace_covariance_mul_eq_integral
    (mu.restrict returnSetᶜ) state A hprod] at h
  simpa [A, B, finiteBuresSourcePairing, mul_comm] using h

end

end GaloisForLFunctions.HTGeometry
