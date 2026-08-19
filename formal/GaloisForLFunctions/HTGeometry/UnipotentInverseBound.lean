import GaloisForLFunctions.HTGeometry.JacobiDecomposition

/-!
# The inverse of a bounded unipotent matrix is bounded

Unipotent upper triangular matrices with entries in a fixed interval form a compact set on which
the determinant is identically one, so the inverse is the adjugate — a polynomial in the entries —
and is therefore bounded there.

This is the estimate that converts a bound on the Jacobi coordinates of a form into a bound on the
form itself, which is what a Siegel set needs.

* `unipotentBall` : the unipotent upper triangular matrices with entries bounded by `u`.
* `isCompact_unipotentBall` : **it is compact.**
* `exists_unipotent_inv_bound` : **the inverses are uniformly bounded.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- The unipotent upper triangular matrices with entries bounded by `u`. -/
def unipotentBall (n : ℕ) (u : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {U | (∀ i j, j < i → U i j = 0) ∧ (∀ i, U i i = 1) ∧ (∀ i j, |U i j| ≤ u)}

theorem det_eq_one_of_unipotent {U : Matrix (Fin n) (Fin n) ℝ}
    (hlow : ∀ i j, j < i → U i j = 0) (hdiag : ∀ i, U i i = 1) : U.det = 1 := by
  have hbt : U.BlockTriangular id := fun i j hij => hlow i j hij
  rw [Matrix.det_of_upperTriangular hbt]
  simp [hdiag]

theorem inv_eq_adjugate_of_unipotent {U : Matrix (Fin n) (Fin n) ℝ}
    (hlow : ∀ i j, j < i → U i j = 0) (hdiag : ∀ i, U i i = 1) : U⁻¹ = U.adjugate := by
  rw [Matrix.inv_def, det_eq_one_of_unipotent hlow hdiag]
  simp

/-- **The unipotent ball is compact.** -/
theorem isCompact_unipotentBall (n : ℕ) (u : ℝ) : IsCompact (unipotentBall n u) := by
  classical
  have hentry : ∀ i j : Fin n, Continuous fun U : Matrix (Fin n) (Fin n) ℝ => U i j :=
    fun i j => continuous_id.matrix_elem i j
  have hclosed : IsClosed (unipotentBall n u) := by
    have heq : unipotentBall n u =
        (⋂ i : Fin n, ⋂ j : Fin n, {U : Matrix (Fin n) (Fin n) ℝ | j < i → U i j = 0})
          ∩ ((⋂ i : Fin n, {U : Matrix (Fin n) (Fin n) ℝ | U i i = 1})
            ∩ (⋂ i : Fin n, ⋂ j : Fin n, {U : Matrix (Fin n) (Fin n) ℝ | |U i j| ≤ u})) := by
      ext U
      simp only [unipotentBall, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [heq]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
      by_cases hij : j < i
      · simpa [hij] using isClosed_eq (hentry i j) continuous_const
      · simp [hij]
    · exact isClosed_iInter fun i => isClosed_eq (hentry i i) continuous_const
    · exact isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_le (hentry i j).abs continuous_const
  have hbox : IsCompact ((Set.univ : Set (Fin n)).pi fun _ : Fin n =>
      (Set.univ : Set (Fin n)).pi fun _ : Fin n => Set.Icc (-u) u) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset hclosed ?_
  intro U hU i _ j _
  exact abs_le.1 (hU.2.2 i j)

/-- **The inverses of bounded unipotent matrices are uniformly bounded.** -/
theorem exists_unipotent_inv_bound (n : ℕ) (u : ℝ) :
    ∃ C : ℝ, ∀ U ∈ unipotentBall n u, ∀ i j, |U⁻¹ i j| ≤ C := by
  classical
  rcases (unipotentBall n u).eq_empty_or_nonempty with hemp | hne
  · exact ⟨0, by simp [hemp]⟩
  set f : Matrix (Fin n) (Fin n) ℝ → ℝ := fun M => ∑ i, ∑ j, |M.adjugate i j| with hf
  have hcont : Continuous f := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (continuous_id.matrix_adjugate.matrix_elem i j).abs
  obtain ⟨M, hM, hmax⟩ := (isCompact_unipotentBall n u).exists_isMaxOn hne hcont.continuousOn
  refine ⟨f M, fun U hU i j => ?_⟩
  have hUadj : U⁻¹ = U.adjugate := inv_eq_adjugate_of_unipotent hU.1 hU.2.1
  rw [hUadj]
  refine le_trans ?_ (hmax hU)
  refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ b, |U.adjugate a b|)
    (fun a _ => Finset.sum_nonneg fun b _ => abs_nonneg _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun b => |U.adjugate i b|)
    (fun b _ => abs_nonneg _) (Finset.mem_univ j)

end GaloisForLFunctions.HTGeometry
