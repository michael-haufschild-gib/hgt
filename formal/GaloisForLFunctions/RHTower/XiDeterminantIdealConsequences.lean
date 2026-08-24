import GaloisForLFunctions.RHTower.XiDeterminantSingularValueTransfer
import GaloisForLFunctions.RHTower.XiOrderedPrimeApproximationAsymptotics
import GaloisForLFunctions.RHTower.XiOrderedPrimeSchattenThreshold
import GaloisForLFunctions.RHTower.XiLogEnhancedWeakTraceIdeal
import GaloisForLFunctions.RHTower.XiOrderedPrimePartialTraceAsymptotics

/-!
# Exact Xi determinant ideal consequences

The pointwise transfer theorem turns every zero-free-gauge self-adjoint Hilbert--Carleman
realization into the canonical reciprocal-Xi approximation-number sequence.  This leaf records
all forced asymptotic, Schatten, weak-ideal, endpoint-residue, and partial-trace consequences.
-/

open Complex Set Filter
open HilbertSchmidt

namespace RHTower

noncomputable section

theorem exactXiDeterminant_approxNumber_eq_canonical
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z)
    (n : ℕ) :
    approxNumber (toOperator hK) n =
      approxNumber xiOrderedSignedPrimeOperator n := by
  rw [xiDeterminant_approxNumber_exactXiDeterminant
    hK hself H hHanalytic hH hXi,
    xiOrderedSignedPrimeOperator_approxNumber]

theorem exactXiDeterminant_approxNumber_asymptotic
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z) :
    Tendsto (fun n : ℕ =>
      approxNumber (toOperator hK) n /
        (Real.log ((n : ℝ) + 1) / (Real.pi * ((n : ℝ) + 1))))
      atTop (nhds 1) := by
  apply tendsto_xiOrderedSignedPrimeOperator_approxNumber_div_model.congr'
  exact Filter.Eventually.of_forall fun n => by
    change approxNumber xiOrderedSignedPrimeOperator n /
        (Real.log ((n : ℝ) + 1) / (Real.pi * ((n : ℝ) + 1))) =
      approxNumber (toOperator hK) n /
        (Real.log ((n : ℝ) + 1) / (Real.pi * ((n : ℝ) + 1)))
    rw [exactXiDeterminant_approxNumber_eq_canonical
      hK hself H hHanalytic hH hXi]

theorem exactXiDeterminant_memSchattenClass
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z)
    {q : ℝ} (hq : 1 < q) :
    MemSchattenClass q (toOperator hK) := by
  unfold MemSchattenClass at *
  exact (xiOrderedSignedPrimeOperator_memSchattenClass hq).congr fun n => by
    rw [exactXiDeterminant_approxNumber_eq_canonical
      hK hself H hHanalytic hH hXi]

theorem exactXiDeterminant_not_memSchattenClass_one
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z) :
    ¬ MemSchattenClass 1 (toOperator hK) := by
  intro htrace
  apply xiOrderedSignedPrimeOperator_not_memSchattenClass_one
  unfold MemSchattenClass at htrace ⊢
  exact htrace.congr fun n => by
    rw [exactXiDeterminant_approxNumber_eq_canonical
      hK hself H hHanalytic hH hXi]

theorem exactXiDeterminant_memSchattenClass_two
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z) :
    MemSchattenClass 2 (toOperator hK) :=
  exactXiDeterminant_memSchattenClass hK hself H hHanalytic hH hXi
    (by norm_num)

theorem exactXiDeterminant_hasLogEnhancedWeakTraceResidue
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z) :
    HasLogEnhancedWeakTraceResidue (toOperator hK) Real.pi⁻¹ := by
  apply hasLogEnhancedWeakTraceResidue_xiOrderedSignedPrimeOperator.congr'
  exact Filter.Eventually.of_forall fun n => by
    rw [logEnhancedWeakTraceProfile, logEnhancedWeakTraceProfile,
      exactXiDeterminant_approxNumber_eq_canonical
        hK hself H hHanalytic hH hXi]

theorem exactXiDeterminant_memLogEnhancedWeakTraceClass
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z) :
    MemLogEnhancedWeakTraceClass (toOperator hK) := by
  rcases memLogEnhancedWeakTraceClass_xiOrderedSignedPrimeOperator with
    ⟨_, C, hC, hbound⟩
  refine ⟨(isHilbertSchmidt_toOperator hK).isCompactOperator, C, hC, fun n => ?_⟩
  rw [logEnhancedWeakTraceProfile,
    exactXiDeterminant_approxNumber_eq_canonical
      hK hself H hHanalytic hH hXi]
  exact hbound n

theorem exactXiDeterminant_succ_mul_approxNumber_tendsto_atTop
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      approxNumber (toOperator hK) n) atTop atTop := by
  apply tendsto_succ_mul_xiOrderedSignedPrimeOperator_approxNumber_atTop.congr'
  exact Filter.Eventually.of_forall fun n => by
    change ((n : ℝ) + 1) * approxNumber xiOrderedSignedPrimeOperator n =
      ((n : ℝ) + 1) * approxNumber (toOperator hK) n
    rw [exactXiDeterminant_approxNumber_eq_canonical
      hK hself H hHanalytic hH hXi]

theorem exactXiDeterminant_not_memWeakSchattenClass_one
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z) :
    ¬ MemWeakSchattenClass 1 (toOperator hK) := by
  rintro ⟨C, hC, hbound⟩
  apply xiOrderedSignedPrimeOperator_not_memWeakSchattenClass_one
  refine ⟨C, hC, fun n => ?_⟩
  rw [← exactXiDeterminant_approxNumber_eq_canonical
    hK hself H hHanalytic hH hXi]
  exact hbound n

theorem exactXiDeterminant_partialTrace_asymptotic
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, approxNumber (toOperator hK) n) /
        Real.log ((N : ℝ) + 1) ^ 2) atTop
      (nhds (1 / (2 * Real.pi))) := by
  apply tendsto_xiOrderedSignedPrimeOperator_approxNumber_partialSum_div_logSq.congr'
  exact Filter.Eventually.of_forall fun N => by
    change (∑ n ∈ Finset.range N, approxNumber xiOrderedSignedPrimeOperator n) /
        Real.log ((N : ℝ) + 1) ^ 2 =
      (∑ n ∈ Finset.range N, approxNumber (toOperator hK) n) /
        Real.log ((N : ℝ) + 1) ^ 2
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [exactXiDeterminant_approxNumber_eq_canonical
      hK hself H hHanalytic hH hXi]

end

end RHTower

