import GaloisForLFunctions.HTGeometry.FiniteFieldStateSpaceHankelRank

/-!
# Recovery with repeated spectral nodes

Vandermonde inversion on distinct node fibers classifies modal sequences without assuming
simple spectrum. The first `d` moments recover exactly the total weight on each fiber.
For several sensors, the same statement applies to their coordinatewise weighted fibers.
-/

open scoped BigOperators Matrix
open HTGeometry
namespace GaloisForLFunctions.BiScaleUncertainty.Observation
noncomputable section
variable {K : Type*} [Field K] {d : ℕ}

def modalFiberWeight (w node : Fin d → K) (z : K) : K := by
  classical
  exact ∑ i, if node i = z then w i else 0

private def nodeSet (node : Fin d → K) : Finset K := by
  classical
  exact Finset.univ.image node

private theorem grouped_moments (w node : Fin d → K) (k : ℕ) :
    finiteModalSequence w node k =
      ∑ z : nodeSet node, modalFiberWeight w node z * (z : K) ^ k := by
  classical
  simp only [modalFiberWeight, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  unfold finiteModalSequence
  apply Finset.sum_congr rfl
  intro i _
  have hi : node i ∈ nodeSet node := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  rw [Finset.sum_eq_single (⟨node i, hi⟩ : nodeSet node)]
  · simp
  · intro b _ hbi
    have hn : node i ≠ (b : K) := by
      intro h; apply hbi; exact Subtype.ext h.symm
    simp only [if_neg hn]
  · simp

private theorem fiber_zero_of_moments (w node : Fin d → K)
    (hm : ∀ k : Fin (Fintype.card (nodeSet node)), finiteModalSequence w node k = 0) :
    ∀ z : K, modalFiberWeight w node z = 0 := by
  classical
  let e := Fintype.equivFin (nodeSet node)
  let nodes : Fin (Fintype.card (nodeSet node)) → K := fun i => (e.symm i).val
  let weights : Fin (Fintype.card (nodeSet node)) → K := fun i => modalFiberWeight w node (nodes i)
  have hn : Function.Injective nodes := by
    intro i j h
    exact e.symm.injective (Subtype.ext h)
  have hzero : weights = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hn
    intro k
    have he := (e.symm.sum_comp (fun z : nodeSet node => modalFiberWeight w node z * (z : K) ^ k.val))
    change (∑ j, modalFiberWeight w node (e.symm j) * (e.symm j : K) ^ k.val) = 0
    rw [he, ← grouped_moments]
    exact hm k
  intro z
  by_cases hz : z ∈ nodeSet node
  · simpa only [weights, nodes, Equiv.symm_apply_apply, Pi.zero_apply] using
      congrFun hzero (e ⟨z, hz⟩)
  · unfold modalFiberWeight
    apply Finset.sum_eq_zero
    intro i _
    have hnz : node i ≠ z := by
      intro hi; apply hz
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
    exact if_neg hnz

theorem first_moments_eq_iff_fiber_weights (u v node : Fin d → K) :
    (∀ k : Fin d, finiteModalSequence u node k = finiteModalSequence v node k) ↔
      ∀ z : K, modalFiberWeight u node z = modalFiberWeight v node z := by
  classical
  constructor
  · intro h
    have hz : ∀ k : Fin d, finiteModalSequence (u - v) node k = 0 := by
      intro k
      simp only [finiteModalSequence, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (h k)
    have hcard : Fintype.card (nodeSet node) ≤ d := by
      simpa only [Fintype.card_coe, nodeSet, Finset.card_univ, Fintype.card_fin] using
        (Finset.card_image_le (f := node) (s := Finset.univ))
    have hf := fiber_zero_of_moments (u - v) node
      (fun k => hz ⟨k.val, lt_of_lt_of_le k.isLt hcard⟩)
    intro z
    have he : modalFiberWeight (u - v) node z = modalFiberWeight u node z - modalFiberWeight v node z := by
      simp only [modalFiberWeight, Pi.sub_apply, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    exact sub_eq_zero.mp (he.symm.trans (hf z))
  · intro h k
    rw [grouped_moments, grouped_moments]
    simp only [h]

theorem all_moments_eq_iff_first (u v node : Fin d → K) :
    finiteModalSequence u node = finiteModalSequence v node ↔
      ∀ k : Fin d, finiteModalSequence u node k = finiteModalSequence v node k := by
  constructor
  · intro h k; exact congrFun h k
  · intro h
    have hf := (first_moments_eq_iff_fiber_weights u v node).mp h
    funext k
    rw [grouped_moments, grouped_moments]
    simp only [hf]


/-- Each sensor sees a diagonal orbit through its coordinatewise input weights. -/
theorem diagonal_channel_response (node input output : Fin d → K) (k : ℕ) :
    algebraicStateSpaceResponse (Matrix.diagonal node) input output k =
      finiteModalSequence (fun i => output i * input i) node k := by
  classical
  simp only [algebraicStateSpaceResponse, Matrix.diagonal_pow, Matrix.mulVec,
    Matrix.diagonal_apply, dotProduct, finiteModalSequence, Pi.pow_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- With repeated eigenvalues, several sensors recover exactly their weighted sums on each
spectral fiber. The first `d` samples already contain every later sample. -/
theorem diagonal_multichannel_fibers {C : Type*}
    (node u v : Fin d → K) (sensor : C → Fin d → K) :
    (∀ c, ∀ k : Fin d,
      algebraicStateSpaceResponse (Matrix.diagonal node) u (sensor c) k =
        algebraicStateSpaceResponse (Matrix.diagonal node) v (sensor c) k) ↔
      ∀ c z, modalFiberWeight (fun i => sensor c i * u i) node z =
        modalFiberWeight (fun i => sensor c i * v i) node z := by
  simp only [diagonal_channel_response, first_moments_eq_iff_fiber_weights]


/-- Number of distinct nodes, which determines the necessary Vandermonde block size. -/
def modalDistinctCount (node : Fin d → K) : ℕ := Fintype.card (nodeSet node)

/-- Only as many samples as distinct nodes are needed, even when many coordinates collide. -/
theorem distinct_moments_eq_iff_fiber_weights (u v node : Fin d → K) :
    (∀ k : Fin (modalDistinctCount node),
      finiteModalSequence u node k = finiteModalSequence v node k) ↔
        ∀ z : K, modalFiberWeight u node z = modalFiberWeight v node z := by
  constructor
  · intro h
    have hz : ∀ k : Fin (modalDistinctCount node), finiteModalSequence (u - v) node k = 0 := by
      intro k
      simp only [finiteModalSequence, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (h k)
    have hf := fiber_zero_of_moments (u - v) node hz
    intro z
    have he : modalFiberWeight (u - v) node z = modalFiberWeight u node z - modalFiberWeight v node z := by
      simp only [modalFiberWeight, Pi.sub_apply, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    exact sub_eq_zero.mp (he.symm.trans (hf z))
  · intro h k
    rw [grouped_moments, grouped_moments]
    simp only [h]

#print axioms distinct_moments_eq_iff_fiber_weights
#print axioms first_moments_eq_iff_fiber_weights
#print axioms all_moments_eq_iff_first
#print axioms diagonal_multichannel_fibers

end
end GaloisForLFunctions.BiScaleUncertainty.Observation
