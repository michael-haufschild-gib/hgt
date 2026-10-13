import GaloisForLFunctions.HTGeometry.PaperGenealogyTraceCompletion

/-! # Native errors of finite genealogy, adjoint and Gram completion

All three errors are uniformly bounded and strongly null. The full genealogy
error retains its compact-ideal obstruction at every finite depth.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter Topology
open scoped ENNReal
variable {d : ℕ}

def paperGenealogyError (a : OpCertStream d) (N : ℕ) : FibSeq d →L[ℂ] FibSeq d :=
  a.genealogy - paperGenealogyPrefix a N

def paperGenealogyAdjointError (a : OpCertStream d) (N : ℕ) : FibSeq d →L[ℂ] FibSeq d :=
  ContinuousLinearMap.adjoint a.genealogy - ContinuousLinearMap.adjoint (paperGenealogyPrefix a N)

def paperGenealogyGramError (a : OpCertStream d) (N : ℕ) : FibSeq d →L[ℂ] FibSeq d :=
  (ContinuousLinearMap.adjoint a.genealogy ∘L a.genealogy) -
    (ContinuousLinearMap.adjoint (paperGenealogyPrefix a N) ∘L paperGenealogyPrefix a N)

theorem paperGenealogyError_norm_le (a : OpCertStream d) (N : ℕ) :
    ‖paperGenealogyError a N‖ ≤ 2 * ‖a.genealogy‖ := by
  exact (norm_sub_le _ _).trans (by
    have h := norm_paperCoordinateCompression_le a.genealogy N
    change ‖paperGenealogyPrefix a N‖ ≤ ‖a.genealogy‖ at h
    linarith)

theorem paperGenealogyAdjointError_norm_le (a : OpCertStream d) (N : ℕ) :
    ‖paperGenealogyAdjointError a N‖ ≤ 2 * ‖a.genealogy‖ := by
  have he : paperGenealogyAdjointError a N = ContinuousLinearMap.adjoint (paperGenealogyError a N) := by
    simp only [paperGenealogyAdjointError, paperGenealogyError, map_sub]
  rw [he, LinearIsometryEquiv.norm_map]
  exact paperGenealogyError_norm_le a N

theorem paperGenealogyGramError_norm_le (a : OpCertStream d) (N : ℕ) :
    ‖paperGenealogyGramError a N‖ ≤ 2 * ‖a.genealogy‖ ^ 2 := by
  have h := norm_sub_le (ContinuousLinearMap.adjoint a.genealogy ∘L a.genealogy)
    (ContinuousLinearMap.adjoint (paperGenealogyPrefix a N) ∘L paperGenealogyPrefix a N)
  rw [ContinuousLinearMap.norm_adjoint_comp_self, ContinuousLinearMap.norm_adjoint_comp_self] at h
  have hb := norm_paperCoordinateCompression_le a.genealogy N
  change ‖paperGenealogyPrefix a N‖ ≤ ‖a.genealogy‖ at hb
  change ‖paperGenealogyGramError a N‖ ≤ _ at h
  nlinarith [norm_nonneg (paperGenealogyPrefix a N), norm_nonneg a.genealogy]

theorem paperGenealogyError_strong (a : OpCertStream d) (x : FibSeq d) :
    Tendsto (fun N => paperGenealogyError a N x) atTop (𝓝 0) := by
  simpa only [paperGenealogyError, paperGenealogyPrefix, sub_apply, sub_self] using
    (tendsto_const_nhds (x := a.genealogy x)).sub (tendsto_paperCoordinateCompression a.genealogy x)

theorem paperGenealogyAdjointError_strong (a : OpCertStream d) (x : FibSeq d) :
    Tendsto (fun N => paperGenealogyAdjointError a N x) atTop (𝓝 0) := by
  simpa only [paperGenealogyAdjointError, paperGenealogyPrefix, sub_apply, sub_self] using
    (tendsto_const_nhds (x := ContinuousLinearMap.adjoint a.genealogy x)).sub
      (tendsto_adjoint_paperCoordinateCompression a.genealogy x)

theorem paperGenealogyGramError_strong (a : OpCertStream d) (x : FibSeq d) :
    Tendsto (fun N => paperGenealogyGramError a N x) atTop (𝓝 0) := by
  simpa only [paperGenealogyGramError, paperGenealogyPrefix, sub_apply, sub_self] using
    (tendsto_const_nhds (x := (ContinuousLinearMap.adjoint a.genealogy ∘L a.genealogy) x)).sub
      (tendsto_gram_paperCoordinateCompression a.genealogy x)

theorem paperGenealogyError_norm_gap (d : ℕ) (a : OpCertStream (d + 1)) (N : ℕ) :
    1 ≤ ‖paperGenealogyError a N‖ := one_le_norm_genealogy_sub_prefix d a N

theorem paperGenealogyError_traceCost (d : ℕ) (a : OpCertStream (d + 1)) (N : ℕ) :
    compactOperatorTraceCost (FibSeq (d + 1)) (paperGenealogyError a N) = ∞ := by
  let K : compactOperatorStarAlgebra (FibSeq (d + 1)) :=
    ⟨paperGenealogyPrefix a N, isCompactOperator_paperCoordinateCompression a.genealogy N⟩
  simpa [paperGenealogyError, sub_eq_add_neg, K] using
    compactOperatorTraceCost_genealogy_add_compact d a (-K)

end
end GaloisForLFunctions.HTGeometry
