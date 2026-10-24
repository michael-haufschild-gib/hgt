import GaloisForLFunctions.ArithmeticDefectRigidity.TheActualReceiverHasAnAbsolutePoleTrace
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CriticalWienerKernelsRepairAPositiveDriftOnlyAtItsPole

/-!
# Linear cofactor renormalization on the absolute pole-trace domain

The pole subtraction is linear when its coefficient is read from the row's Mellin trace.
The actual receiver belongs to this domain without an admission assumption, and its trace
is the coefficient already used in the paid forcing decomposition. Its image returns to the
trace domain. Generic boundedness and domain invariance remain separate questions.
-/

open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.TransHorizonIncidenceMechanics
  (mellinCell summable_mul_mellinCell_of_energy subHalfRemainder weightCenteredPrefix_zero)

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- Rows vanishing at the origin whose Mellin-cell trace is absolutely summable. -/
def poleTraceDomain (ε : SubcriticalDamping) : Submodule ℝ (ℕ → ℝ) where
  carrier := {v | v 0 = 0 ∧ Summable (fun n => v n * mellinCell (1 - (ε : ℝ)) n)}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    refine ⟨?_, ?_⟩
    · change v 0 + w 0 = 0
      rw [hv.1, hw.1, add_zero]
    · simpa only [Pi.add_apply, add_mul] using hv.2.add hw.2
  smul_mem' := by
    intro c v hv
    refine ⟨?_, ?_⟩
    · change c * v 0 = 0
      rw [hv.1, mul_zero]
    · simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using hv.2.mul_left c

/-- The linear boundary coefficient at the cofactor pole. -/
def poleTrace (ε : SubcriticalDamping) : poleTraceDomain ε →ₗ[ℝ] ℝ where
  toFun v := (∑' n, v n * mellinCell (1 - (ε : ℝ)) n) / (1 - (ε : ℝ))
  map_add' := by
    intro v w
    change (∑' n, (v n + w n) * mellinCell (1 - (ε : ℝ)) n) / (1 - (ε : ℝ)) = _
    simp_rw [add_mul]
    rw [v.property.2.tsum_add w.property.2, add_div] <;> rfl
  map_smul' := by
    intro c v
    change (∑' n, (c * v n) * mellinCell (1 - (ε : ℝ)) n) / (1 - (ε : ℝ)) =
      c * ((∑' n, v n * mellinCell (1 - (ε : ℝ)) n) / (1 - (ε : ℝ)))
    simp_rw [mul_assoc]
    rw [tsum_mul_left]
    ring

/-- The proper finite cofactor sum acts linearly on all rows. -/
def finiteCofactorOperator (ε : ℝ) : (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ) where
  toFun v n := ∑ j ∈ Icc 2 n, (j : ℝ) ^ (-ε) * v (n / j)
  map_add' := by
    intro v w
    funext n
    simp only [Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' := by
    intro c v
    funext n
    simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
    apply sum_congr rfl
    intro j _
    ring

/-- The rank-one power term is read linearly from the boundary trace. -/
def polePowerOperator (ε : SubcriticalDamping) : poleTraceDomain ε →ₗ[ℝ] (ℕ → ℝ) where
  toFun v n := poleTrace ε v * (n : ℝ) ^ (1 - (ε : ℝ))
  map_add' := by
    intro v w
    funext n
    change poleTrace ε (v + w) * (n : ℝ) ^ (1 - (ε : ℝ)) = _
    rw [map_add, add_mul] <;> rfl
  map_smul' := by
    intro c v
    funext n
    change poleTrace ε (c • v) * (n : ℝ) ^ (1 - (ε : ℝ)) = _
    rw [map_smul]
    change (c * poleTrace ε v) * (n : ℝ) ^ (1 - (ε : ℝ)) =
      c * (poleTrace ε v * (n : ℝ) ^ (1 - (ε : ℝ)))
    ring

/-- Cofactor renormalization is a linear row-valued map on the proved trace domain. -/
def renormalizedCofactorOperator (ε : SubcriticalDamping) :
    poleTraceDomain ε →ₗ[ℝ] (ℕ → ℝ) :=
  (finiteCofactorOperator ε).comp (poleTraceDomain ε).subtype - polePowerOperator ε

/-- The actual receiver lies in the trace domain regardless of critical-energy admission. -/
def actualTraceVector (ε : SubcriticalDamping) : poleTraceDomain ε :=
  ⟨pmPowerDampedCenteredDivisorPrefix ε,
    ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero ε,
    summable_receiver_mul_poleMellinCell ε⟩

/-- The row-defined linear trace recovers the exact actual forcing coefficient. -/
theorem poleTrace_actualTraceVector (ε : SubcriticalDamping) :
    poleTrace ε (actualTraceVector ε) = forcingPowerCoefficient ε :=
  actualPoleTrace_eq_forcingPowerCoefficient ε

/-- On the actual source, linear renormalization agrees with the paid cofactor residual. -/
theorem renormalizedCofactorOperator_actualTraceVector (ε : SubcriticalDamping) :
    renormalizedCofactorOperator ε (actualTraceVector ε) = renormalizedCofactor ε := by
  funext n
  change (∑ j ∈ Icc 2 n, (j : ℝ) ^ (-(ε : ℝ)) *
    pmPowerDampedCenteredDivisorPrefix ε (n / j)) -
    poleTrace ε (actualTraceVector ε) * (n : ℝ) ^ (1 - (ε : ℝ)) = _
  rw [poleTrace_actualTraceVector] <;> rfl

/-- The actual linear residual has a uniform global pronic budget. -/
theorem pronicNorm_actual_linearResidual_le (ε : SubcriticalDamping) (T : ℕ) :
    pronicNorm T (fun n => actualTraceVector ε n +
      renormalizedCofactorOperator ε (actualTraceVector ε) n) ≤ forcingRemainderBudget ε := by
  rw [renormalizedCofactorOperator_actualTraceVector]
  exact pronicNorm_receiver_add_renormalizedCofactor_le ε T

theorem forcingRemainder_zero (ε : SubcriticalDamping) : forcingRemainder ε 0 = 0 := by
  have hα : 1 - (ε : ℝ) ≠ 0 := by linarith [ε.property.2]
  rw [forcingRemainder_eq]
  simp only [subHalfRemainder, weightCenteredPrefix_zero, Nat.cast_zero,
    Real.zero_rpow hα, mul_zero, sub_self]

/-- The paid global remainder belongs to the absolute trace domain. -/
theorem forcingRemainder_mem_poleTraceDomain (ε : SubcriticalDamping) :
    forcingRemainder ε ∈ poleTraceDomain ε := by
  refine ⟨forcingRemainder_zero ε, ?_⟩
  apply summable_mul_mellinCell_of_energy
    (by linarith [ε.property.2] : 1 / 2 < 1 - (ε : ℝ)) (forcingRemainder_zero ε)
  intro T
  simpa only [pronicNorm_sq] using forcingRemainderEnergy_le ε T

/-- The actual cofactor image returns to the trace domain after the power is removed. -/
theorem actual_renormalizedCofactor_mem_poleTraceDomain (ε : SubcriticalDamping) :
    renormalizedCofactorOperator ε (actualTraceVector ε) ∈ poleTraceDomain ε := by
  have hsub := (poleTraceDomain ε).sub_mem (forcingRemainder_mem_poleTraceDomain ε)
    (actualTraceVector ε).property
  have heq : forcingRemainder ε - (actualTraceVector ε : ℕ → ℝ) = renormalizedCofactor ε := by
    funext n
    cases n with
    | zero =>
      have hα : 1 - (ε : ℝ) ≠ 0 := by linarith [ε.property.2]
      have hIcc : (Icc 2 0 : Finset ℕ) = ∅ := Finset.Icc_eq_empty (by omega)
      change forcingRemainder ε 0 - pmPowerDampedCenteredDivisorPrefix ε 0 = _
      rw [forcingRemainder_zero,
        ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero]
      simp only [renormalizedCofactor, offDiagonalUnitDilation, forcingPower,
        hIcc, sum_empty, Nat.cast_zero,
        Real.zero_rpow hα, mul_zero, sub_self]
    | succ n =>
      change forcingRemainder ε (n + 1) - pmPowerDampedCenteredDivisorPrefix ε (n + 1) = _
      have h := receiver_add_renormalizedCofactor_eq ε n
      linarith
  rw [renormalizedCofactorOperator_actualTraceVector, ← heq]
  exact hsub

end GaloisForLFunctions.ArithmeticDefectRigidity
