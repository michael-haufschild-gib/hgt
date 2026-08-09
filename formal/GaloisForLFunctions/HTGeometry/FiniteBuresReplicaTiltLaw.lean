import GaloisForLFunctions.HTGeometry.OccupiedBuresTargetBodyLaw
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Replica-powered Bures observer tilts

The positive-reporter Cauchy--Schwarz law may be powered pointwise before
integration.  This gives the additive-observer replica certificate directly:
the complete target union is paid once, the occupied inverse-channel ceiling
is raised to the replica power, and the source channel contributes its exact
powered moment.  No tensor-coordinate realization or target-label union bound
is needed.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MeasureTheory Matrix Set
open scoped ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Exponential reporter positivity, kept local to the powered law so this
module has no build-order dependency on the one-copy tilt interface. -/
theorem finiteBuresReplicaReporterExp_posDef
    {n : ℕ} {W : Matrix (Fin n) (Fin n) ℂ} (hW : W.IsHermitian) :
    (NormedSpace.exp W).PosDef := by
  have hnonneg : 0 ≤ NormedSpace.exp W := hW.isSelfAdjoint.exp_nonneg
  have hpsd : (NormedSpace.exp W).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hnonneg
  exact hpsd.posDef_iff_isUnit.mpr (Matrix.isUnit_exp W)

/-- Powering the pointwise complete-capture reporter bound gives the exact
replica moment threshold. -/
theorem finitePositiveReporter_completeCapture_subset_powered
    {X C : Type*} {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef)
    (target : C → Fin n → ℂ) (state : X → Fin n → ℂ)
    (threshold targetCeiling : ℝ) (hthreshold : 0 ≤ threshold)
    (hceiling : ∀ c,
      finitePositiveReporterTargetLeverage A (target c) ≤ targetCeiling) :
    finitePositiveReporterCaptureEvent target state threshold ⊆
      {x | threshold ^ r ≤ targetCeiling ^ r *
        finitePositiveReporterSourceEnergy A (state x) ^ r} := by
  intro x hx
  have hpoint := finitePositiveReporter_completeCapture_subset
    A hA target state threshold targetCeiling hceiling hx
  have hpow := pow_le_pow_left₀ hthreshold hpoint r
  simpa [mul_pow] using hpow

/-- **Powered complete-union reporter law.**  For every replica power, one
target-independent reporter controls the whole target family through one
powered source moment and one powered inverse-channel ceiling. -/
theorem finitePositiveReporter_completeIncidence_powered_bound
    {X C : Type*} [MeasurableSpace X] {n r : ℕ}
    (mu : Measure X) [IsFiniteMeasure mu]
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef)
    (target : C → Fin n → ℂ) (state : X → Fin n → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (targetCeiling : ℝ) (hceilingNonneg : 0 ≤ targetCeiling)
    (hceiling : ∀ c,
      finitePositiveReporterTargetLeverage A (target c) ≤ targetCeiling)
    (hint : Integrable
      (fun x ↦ finitePositiveReporterSourceEnergy A (state x) ^ r) mu) :
    threshold ^ r * mu.real
        (finitePositiveReporterCaptureEvent target state threshold) ≤
      targetCeiling ^ r * ∫ x,
        finitePositiveReporterSourceEnergy A (state x) ^ r ∂mu := by
  let q : X → ℝ := fun x ↦
    targetCeiling ^ r * finitePositiveReporterSourceEnergy A (state x) ^ r
  let E : Set X := finitePositiveReporterCaptureEvent target state threshold
  have hEQ : E ⊆ {x | threshold ^ r ≤ q x} := by
    exact finitePositiveReporter_completeCapture_subset_powered
      A hA target state threshold targetCeiling hthreshold.le hceiling
  have hintq : Integrable q mu := hint.const_mul (targetCeiling ^ r)
  have hqnonneg : 0 ≤ᵐ[mu] q :=
    Filter.Eventually.of_forall fun x ↦ mul_nonneg
      (pow_nonneg hceilingNonneg r)
      (pow_nonneg
        (finitePositiveReporterSourceEnergy_nonneg hA (state x)) r)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    hqnonneg hintq (threshold ^ r)
  calc
    threshold ^ r * mu.real E ≤
        threshold ^ r * mu.real {x | threshold ^ r ≤ q x} :=
      mul_le_mul_of_nonneg_left
        (measureReal_mono hEQ (by finiteness)) (pow_nonneg hthreshold.le r)
    _ ≤ ∫ x, q x ∂mu := hmarkov
    _ = targetCeiling ^ r * ∫ x,
        finitePositiveReporterSourceEnergy A (state x) ^ r ∂mu := by
      exact integral_const_mul (targetCeiling ^ r) _

/-- Return-excised powered reporter law.  Return mass is paid once, independent
of the replica exponent, and the powered source moment is integrated only on
the surviving complement. -/
theorem finitePositiveReporter_returnExcisedIncidence_powered_bound
    {X C : Type*} [MeasurableSpace X] {n r : ℕ}
    (mu : Measure X) [IsFiniteMeasure mu]
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef)
    (target : C → Fin n → ℂ) (state : X → Fin n → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (targetCeiling : ℝ) (hceilingNonneg : 0 ≤ targetCeiling)
    (hceiling : ∀ c,
      finitePositiveReporterTargetLeverage A (target c) ≤ targetCeiling)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hint : Integrable
      (fun x ↦ finitePositiveReporterSourceEnergy A (state x) ^ r)
        (mu.restrict returnSetᶜ)) :
    mu.real (finitePositiveReporterCaptureEvent target state threshold) ≤
      mu.real returnSet +
        (targetCeiling ^ r * ∫ x,
          finitePositiveReporterSourceEnergy A (state x) ^ r
            ∂(mu.restrict returnSetᶜ)) / threshold ^ r := by
  let nu : Measure X := mu.restrict returnSetᶜ
  let E : Set X := finitePositiveReporterCaptureEvent target state threshold
  have hscaled := finitePositiveReporter_completeIncidence_powered_bound
    nu A hA target state threshold hthreshold targetCeiling
      hceilingNonneg hceiling hint
  have hthresholdPower : 0 < threshold ^ r := pow_pos hthreshold r
  have hresidual :
      nu.real E ≤
        (targetCeiling ^ r * ∫ x,
          finitePositiveReporterSourceEnergy A (state x) ^ r ∂nu) /
            threshold ^ r := by
    apply (le_div_iff₀' hthresholdPower).2
    simpa [mul_comm] using hscaled
  have hcut := measureReal_le_return_add_restrict_compl
    mu E returnSet hreturn
  exact hcut.trans (by
    simpa [E, nu] using add_le_add_left hresidual (mu.real returnSet))

/-- **Opposite-tilt replica law (`TILT-r`).**  Every Hermitian one-copy
observer controls every replica power through the exact powered opposite
target channel and powered source moment. -/
theorem finiteBures_completeIncidence_oppositeTilt_powered_bound
    {X C : Type*} [MeasurableSpace X] [Nonempty C] {n r : ℕ}
    (mu : Measure X) [IsFiniteMeasure mu]
    (target : C → Fin n → ℂ) (state : X → Fin n → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : W.IsHermitian)
    (hTargetBounded : Bornology.IsBounded (Set.range target))
    (hint : Integrable
      (fun x ↦ finitePositiveReporterSourceEnergy
        (NormedSpace.exp W) (state x) ^ r) mu) :
    threshold ^ r * mu.real
        (finitePositiveReporterCaptureEvent target state threshold) ≤
      finiteBuresOccupiedTargetMaximum
          (NormedSpace.exp W) (Set.range target) ^ r *
        ∫ x, finitePositiveReporterSourceEnergy
          (NormedSpace.exp W) (state x) ^ r ∂mu := by
  let A : Matrix (Fin n) (Fin n) ℂ := NormedSpace.exp W
  let B : ℝ := finiteBuresOccupiedTargetMaximum A (Set.range target)
  have hA : A.PosDef := finiteBuresReplicaReporterExp_posDef hW
  have hceiling : ∀ c,
      finitePositiveReporterTargetLeverage A (target c) ≤ B := by
    intro c
    exact finiteBuresTargetLeverage_le_occupiedTargetMaximum_of_isBounded
      A hTargetBounded (Set.mem_range_self c)
  let c0 : C := Classical.choice inferInstance
  have hBnonneg : 0 ≤ B :=
    (finitePositiveReporterTargetLeverage_nonneg hA (target c0)).trans
      (hceiling c0)
  simpa [A, B] using finitePositiveReporter_completeIncidence_powered_bound
    mu A hA target state threshold hthreshold B hBnonneg hceiling hint

/-- Return-excised `TILT-r`: one return charge and the exact powered
opposite-channel moment on its complement. -/
theorem finiteBures_returnExcisedIncidence_oppositeTilt_powered_bound
    {X C : Type*} [MeasurableSpace X] [Nonempty C] {n r : ℕ}
    (mu : Measure X) [IsFiniteMeasure mu]
    (target : C → Fin n → ℂ) (state : X → Fin n → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : W.IsHermitian)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hTargetBounded : Bornology.IsBounded (Set.range target))
    (hint : Integrable
      (fun x ↦ finitePositiveReporterSourceEnergy
        (NormedSpace.exp W) (state x) ^ r)
        (mu.restrict returnSetᶜ)) :
    mu.real (finitePositiveReporterCaptureEvent target state threshold) ≤
      mu.real returnSet +
        (finiteBuresOccupiedTargetMaximum
              (NormedSpace.exp W) (Set.range target) ^ r *
          ∫ x, finitePositiveReporterSourceEnergy
            (NormedSpace.exp W) (state x) ^ r
              ∂(mu.restrict returnSetᶜ)) / threshold ^ r := by
  let A : Matrix (Fin n) (Fin n) ℂ := NormedSpace.exp W
  let B : ℝ := finiteBuresOccupiedTargetMaximum A (Set.range target)
  have hA : A.PosDef := finiteBuresReplicaReporterExp_posDef hW
  have hceiling : ∀ c,
      finitePositiveReporterTargetLeverage A (target c) ≤ B := by
    intro c
    exact finiteBuresTargetLeverage_le_occupiedTargetMaximum_of_isBounded
      A hTargetBounded (Set.mem_range_self c)
  let c0 : C := Classical.choice inferInstance
  have hBnonneg : 0 ≤ B :=
    (finitePositiveReporterTargetLeverage_nonneg hA (target c0)).trans
      (hceiling c0)
  simpa [A, B] using
    finitePositiveReporter_returnExcisedIncidence_powered_bound
      mu A hA target state threshold hthreshold B hBnonneg hceiling
        returnSet hreturn hint

end

end GaloisForLFunctions.HTGeometry
