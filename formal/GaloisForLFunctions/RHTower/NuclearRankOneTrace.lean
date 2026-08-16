import GaloisForLFunctions.RHTower.NuclearRankOneSchatten
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace
import GaloisForLFunctions.RHTower.TraceClassCyclicity
import GaloisForLFunctions.HTGeometry.PointedFisherCutoffWardTrace

/-!
# Ordinary trace of an absolutely summable rank-one operator series

`NuclearRankOneSchatten` proves that an absolutely operator-norm summable family of
rank-at-most-one operators is Schatten one.  This file proves the corresponding trace identity:
ordinary operator trace commutes with the arbitrarily indexed tsum.  Absolute Fubini is obtained
from the approximation-number trace-norm bound on every orthonormal diagonal.
-/

open Filter Topology
open scoped BigOperators InnerProductSpace

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem opTrace_eq_tsum_basis_of_memSchattenClass_one'
    {T : H →L[ℂ] H} (hT : MemSchattenClass 1 T)
    {κ : Type*} (b : HilbertBasis κ ℂ H) :
    ContinuousLinearMap.opTrace T = ∑' i, inner ℂ (b i) (T (b i)) := by
  obtain ⟨A, B, hA, hB, hfactor⟩ := hT.one_isTraceClass
  rw [hfactor]
  exact ContinuousLinearMap.opTrace_comp_eq_tsum_basis hA hB b

/-- Ordinary trace commutes with every absolutely norm-summable, arbitrarily indexed family of
rank-at-most-one operators. -/
theorem opTrace_tsum_rankOneTerms_of_summable_norm
    {ι : Type*} (A : ι → H →L[ℂ] H) (hA : ∀ k, HasRankLE (A k) 1)
    (hnorm : Summable (fun k => ‖A k‖)) :
    ContinuousLinearMap.opTrace (∑' k, A k) =
      ∑' k, ContinuousLinearMap.opTrace (A k) := by
  let b := ContinuousLinearMap.hsBasis ℂ H
  have hsumA : Summable A := Summable.of_norm hnorm
  have hmem (k : ι) : MemSchattenClass 1 (A k) :=
    memSchattenClass_of_hasRankLE one_pos (hA k)
  have hdiag (k : ι) : Summable (fun i => inner ℂ (b i) (A k (b i))) :=
    (hmem k).one_summable_inner_diag_basis b
  have hdiagNormBound (k : ι) :
      (∑' i, ‖inner ℂ (b i) (A k (b i))‖) ≤ ‖A k‖ := by
    calc
      (∑' i, ‖inner ℂ (b i) (A k (b i))‖) ≤ traceNorm H (A k) := by
        apply Real.tsum_le_of_sum_le (fun i => norm_nonneg _)
        exact sum_norm_inner_le_traceNorm
          ((hmem k).isCompactOperator one_pos)
          (hmem k).one_summable_approxNumber
          (fun i => Or.inr (b.orthonormal.1 i))
          (fun i j hij => b.orthonormal.2 hij)
          (fun i => Or.inr (b.orthonormal.1 i))
          (fun i j hij => b.orthonormal.2 hij)
      _ = ‖A k‖ := traceNorm_eq_norm_of_hasRankLE_one (hA k)
  have houter : Summable (fun k =>
      ∑' i, ‖inner ℂ (b i) (A k (b i))‖) := by
    exact Summable.of_nonneg_of_le
      (fun k => tsum_nonneg (fun i => norm_nonneg _)) hdiagNormBound hnorm
  have hprodNorm : Summable (Function.uncurry
      (fun k i => ‖inner ℂ (b i) (A k (b i))‖)) := by
    exact (summable_prod_of_nonneg
      (f := Function.uncurry (fun k i => ‖inner ℂ (b i) (A k (b i))‖))
      (fun p => norm_nonneg _)).2 ⟨fun k => (hdiag k).norm, houter⟩
  have hprod : Summable (Function.uncurry
      (fun k i => inner ℂ (b i) (A k (b i)))) :=
    Summable.of_norm hprodNorm
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one'
    (memSchattenClass_one_tsum_rankOneTerms_of_summable_norm A hA hnorm) b]
  calc
    (∑' i, inner ℂ (b i) ((∑' k, A k) (b i))) =
        ∑' i, ∑' k, inner ℂ (b i) (A k (b i)) := by
      apply tsum_congr
      intro i
      let L : (H →L[ℂ] H) →L[ℂ] ℂ :=
        (innerSL ℂ (b i)).comp (ContinuousLinearMap.apply ℂ H (b i))
      change L (∑' k, A k) = ∑' k, L (A k)
      exact L.map_tsum hsumA
    _ = ∑' k, ∑' i, inner ℂ (b i) (A k (b i)) := hprod.tsum_comm
    _ = ∑' k, ContinuousLinearMap.opTrace (A k) := by
      apply tsum_congr
      intro k
      exact (opTrace_eq_tsum_basis_of_memSchattenClass_one' (hmem k) b).symm

/-- Trace of a scalar multiple of a positive rank-one operator. -/
theorem opTrace_smul_rankOne_self (c : ℂ) (x : H) :
    ContinuousLinearMap.opTrace (c • InnerProductSpace.rankOne ℂ x x) =
      c * (‖x‖ ^ 2 : ℂ) := by
  rw [opTrace_smul, GaloisForLFunctions.HTGeometry.opTrace_rankOne,
    inner_self_eq_norm_sq_to_K]
  rfl

end RHTower
