import GaloisForLFunctions.HTGeometry.PaperCoordinateCompression
import GaloisForLFunctions.HTGeometry.PaperOperatorGenealogyIdealTrace

/-!
# Finite genealogy costs and the completed trace

Every finite genealogy compression has zero compact-ideal Gram cost, while the completed
genealogy has infinite cost. The operators, adjoints and positive Gram operators all converge
strongly. The operator-norm gap nevertheless remains at least one. Thus this ideal trace
cannot be passed through strong completion, even when the finite operators retain the
exact action on their prefix histories. Compact repairs do not remove the discrepancy.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The literal finite coordinate compression of the completed genealogy. -/
def paperGenealogyPrefix {d : ℕ} (a : OpCertStream d) (N : ℕ) :
    FibSeq d →L[ℂ] FibSeq d := paperCoordinateCompression a.genealogy N

/-- The backward genealogy preserves each prefix subspace exactly. -/
theorem paperGenealogyPrefix_eq_genealogy_comp_projection
    {d : ℕ} (a : OpCertStream d) (N : ℕ) :
    paperGenealogyPrefix a N = a.genealogy ∘L paperCoordinateProjection N := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  change paperCoordinateProjection N (a.genealogy (paperCoordinateProjection N x)) n =
    a.genealogy (paperCoordinateProjection N x) n
  rw [paperCoordinateProjection_coordinate]
  split_ifs with hn
  · rfl
  · have hn' : ¬ n + 1 < N := by omega
    simp [OpCertStream.genealogy_apply, paperCoordinateProjection_coordinate, hn, hn']

/-- The finite matrix entries are the actual certificate entries, including the last row. -/
theorem paperGenealogyPrefix_coordinate {d : ℕ} (a : OpCertStream d) (N : ℕ)
    (x : FibSeq d) (n : ℕ) :
    paperGenealogyPrefix a N x n =
      (if n < N then x n else 0) - matOp (a.C n) (if n + 1 < N then x (n + 1) else 0) := by
  rw [paperGenealogyPrefix_eq_genealogy_comp_projection]
  simp only [ContinuousLinearMap.comp_apply, OpCertStream.genealogy_apply,
    paperCoordinateProjection_coordinate]

/-- On an actual prefix history the finite genealogy agrees exactly with its completion. -/
theorem paperGenealogyPrefix_on_prefix {d : ℕ} (a : OpCertStream d) (N : ℕ)
    (x : FibSeq d) :
    paperGenealogyPrefix a N (paperCoordinateProjection N x) =
      a.genealogy (paperCoordinateProjection N x) := by
  rw [paperGenealogyPrefix_eq_genealogy_comp_projection]
  change a.genealogy ((paperCoordinateProjection N ∘L paperCoordinateProjection N) x) = _
  rw [paperCoordinateProjection_idempotent]

/-- Every finite genealogy has zero compact-ideal Gram cost. -/
theorem compactOperatorTraceCost_paperGenealogyPrefix
    {d : ℕ} (a : OpCertStream d) (N : ℕ) :
    compactOperatorTraceCost (FibSeq d) (paperGenealogyPrefix a N) = 0 :=
  compactOperatorTraceCost_paperCoordinateCompression a.genealogy N

/-- The norm discrepancy remains uniform at every finite depth. -/
theorem one_le_norm_genealogy_sub_prefix (d : ℕ) (a : OpCertStream (d + 1)) (N : ℕ) :
    1 ≤ ‖a.genealogy - paperGenealogyPrefix a N‖ :=
  one_le_norm_genealogy_sub_compact d a
    ⟨paperGenealogyPrefix a N, isCompactOperator_paperCoordinateCompression a.genealogy N⟩

/-- Strong convergence of operators, adjoints and Grams coexists with a zero-to-infinite
ideal-trace jump for every completed genealogy. -/
theorem paperGenealogyPrefix_trace_completion (d : ℕ) (a : OpCertStream (d + 1)) :
    (∀ N, compactOperatorTraceCost (FibSeq (d + 1)) (paperGenealogyPrefix a N) = 0) ∧
    (∀ x : FibSeq (d + 1),
      Tendsto (fun N => paperGenealogyPrefix a N x) atTop (𝓝 (a.genealogy x)) ∧
      Tendsto (fun N => ContinuousLinearMap.adjoint (paperGenealogyPrefix a N) x)
        atTop (𝓝 (ContinuousLinearMap.adjoint a.genealogy x)) ∧
      Tendsto (fun N => (ContinuousLinearMap.adjoint (paperGenealogyPrefix a N) ∘L
          paperGenealogyPrefix a N) x)
        atTop (𝓝 ((ContinuousLinearMap.adjoint a.genealogy ∘L a.genealogy) x))) ∧
    compactOperatorTraceCost (FibSeq (d + 1)) a.genealogy = ∞ := by
  refine ⟨compactOperatorTraceCost_paperGenealogyPrefix a, ?_,
    compactOperatorTraceCost_genealogy d a⟩
  intro x
  exact ⟨tendsto_paperCoordinateCompression a.genealogy x,
    tendsto_adjoint_paperCoordinateCompression a.genealogy x,
    tendsto_gram_paperCoordinateCompression a.genealogy x⟩

/-- The lower-semicontinuity inequality fails along these strong Gram approximations. -/
theorem paperGenealogyPrefix_trace_liminf_failure (d : ℕ) (a : OpCertStream (d + 1)) :
    ¬ compactOperatorTraceCost (FibSeq (d + 1)) a.genealogy ≤
      Filter.liminf (fun N => compactOperatorTraceCost (FibSeq (d + 1))
        (paperGenealogyPrefix a N)) atTop := by
  simp only [compactOperatorTraceCost_genealogy, compactOperatorTraceCost_paperGenealogyPrefix,
    liminf_const]
  simp

/-- Strong completion cannot be strengthened to operator-norm completion. -/
theorem not_tendsto_paperGenealogyPrefix_norm (d : ℕ) (a : OpCertStream (d + 1)) :
    ¬ Tendsto (paperGenealogyPrefix a) atTop (𝓝 a.genealogy) := by
  intro h
  have hz : Tendsto (fun N => ‖a.genealogy - paperGenealogyPrefix a N‖) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => a.genealogy)
      atTop (𝓝 a.genealogy)).sub h).norm
  have hf : (1 : ℝ) ≤ 0 := ge_of_tendsto hz
    (Eventually.of_forall (one_le_norm_genealogy_sub_prefix d a))
  exact (not_le_of_gt zero_lt_one) hf

/-- Even after any compact repair, finite compressions have zero cost and their strongly
convergent Gram limit has infinite cost. -/
theorem paperGenealogy_compactRepair_trace_completion (d : ℕ) (a : OpCertStream (d + 1))
    (K : compactOperatorStarAlgebra (FibSeq (d + 1))) :
    (∀ N, compactOperatorTraceCost (FibSeq (d + 1))
      (paperCoordinateCompression (a.genealogy + K.1) N) = 0) ∧
    (∀ x : FibSeq (d + 1), Tendsto
      (fun N => (ContinuousLinearMap.adjoint (paperCoordinateCompression (a.genealogy + K.1) N)
        ∘L paperCoordinateCompression (a.genealogy + K.1) N) x)
      atTop (𝓝 ((ContinuousLinearMap.adjoint (a.genealogy + K.1) ∘L (a.genealogy + K.1)) x))) ∧
    compactOperatorTraceCost (FibSeq (d + 1)) (a.genealogy + K.1) = ∞ :=
  ⟨compactOperatorTraceCost_paperCoordinateCompression _,
    tendsto_gram_paperCoordinateCompression _, compactOperatorTraceCost_genealogy_add_compact d a K⟩

end

end GaloisForLFunctions.HTGeometry
