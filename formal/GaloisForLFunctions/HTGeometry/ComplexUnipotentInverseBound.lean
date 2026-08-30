import GaloisForLFunctions.HTGeometry.ComplexJacobiDecomposition

/-!
# Uniform inverse bounds for complex upper-unipotent matrices

Complex upper-unipotent matrices with uniformly bounded entries form a compact set. Their inverses
are adjugates, hence have one uniform entry bound. This is the Hermitian counterpart of
`UnipotentInverseBound`.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

variable {n : ℕ}

/-- Complex upper-unipotent matrices with entry norms bounded by `u`. -/
def complexUnipotentBall (n : ℕ) (u : ℝ) :
    Set (Matrix (Fin n) (Fin n) ℂ) :=
  {U | (∀ i j, j < i → U i j = 0) ∧
    (∀ i, U i i = 1) ∧ (∀ i j, ‖U i j‖ ≤ u)}

theorem complex_det_eq_one_of_unipotent
    {U : Matrix (Fin n) (Fin n) ℂ}
    (hlow : ∀ i j, j < i → U i j = 0)
    (hdiag : ∀ i, U i i = 1) : U.det = 1 := by
  have hbt : U.BlockTriangular id := fun i j hij => hlow i j hij
  rw [Matrix.det_of_upperTriangular hbt]
  simp [hdiag]

theorem complex_inv_eq_adjugate_of_unipotent
    {U : Matrix (Fin n) (Fin n) ℂ}
    (hlow : ∀ i j, j < i → U i j = 0)
    (hdiag : ∀ i, U i i = 1) : U⁻¹ = U.adjugate := by
  rw [Matrix.inv_def, complex_det_eq_one_of_unipotent hlow hdiag]
  simp

/-- Complex bounded upper-unipotent matrices form a compact set. -/
theorem isCompact_complexUnipotentBall (n : ℕ) (u : ℝ) :
    IsCompact (complexUnipotentBall n u) := by
  classical
  have hentry : ∀ i j : Fin n,
      Continuous fun U : Matrix (Fin n) (Fin n) ℂ => U i j :=
    fun i j => continuous_id.matrix_elem i j
  have hclosed : IsClosed (complexUnipotentBall n u) := by
    have heq : complexUnipotentBall n u =
        (⋂ i : Fin n, ⋂ j : Fin n,
          {U : Matrix (Fin n) (Fin n) ℂ | j < i → U i j = 0}) ∩
        ((⋂ i : Fin n, {U : Matrix (Fin n) (Fin n) ℂ | U i i = 1}) ∩
          (⋂ i : Fin n, ⋂ j : Fin n,
            {U : Matrix (Fin n) (Fin n) ℂ | ‖U i j‖ ≤ u})) := by
      ext U
      simp only [complexUnipotentBall, Set.mem_setOf_eq, Set.mem_inter_iff,
        Set.mem_iInter]
    rw [heq]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
      by_cases hij : j < i
      · simpa [hij] using isClosed_eq (hentry i j) continuous_const
      · simp [hij]
    · exact isClosed_iInter fun i => isClosed_eq (hentry i i) continuous_const
    · exact isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_le (continuous_norm.comp (hentry i j)) continuous_const
  have hcoord : IsCompact {z : ℂ | ‖z‖ ≤ u} := by
    simpa [Metric.closedBall, dist_zero_right] using
      (isCompact_closedBall (0 : ℂ) u)
  have hbox : IsCompact ((Set.univ : Set (Fin n)).pi fun _ : Fin n =>
      (Set.univ : Set (Fin n)).pi fun _ : Fin n => {z : ℂ | ‖z‖ ≤ u}) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hcoord
  refine hbox.of_isClosed_subset hclosed ?_
  intro U hU i _ j _
  exact hU.2.2 i j

/-- Inverses of bounded complex upper-unipotent matrices have uniformly bounded entries. -/
theorem exists_complex_unipotent_inv_bound (n : ℕ) (u : ℝ) :
    ∃ C : ℝ, ∀ U ∈ complexUnipotentBall n u,
      ∀ i j, ‖U⁻¹ i j‖ ≤ C := by
  classical
  rcases (complexUnipotentBall n u).eq_empty_or_nonempty with hemp | hne
  · exact ⟨0, by simp [hemp]⟩
  set f : Matrix (Fin n) (Fin n) ℂ → ℝ :=
    fun M => ∑ i, ∑ j, ‖M.adjugate i j‖ with hf
  have hcont : Continuous f := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact continuous_norm.comp (continuous_id.matrix_adjugate.matrix_elem i j)
  obtain ⟨M, hM, hmax⟩ :=
    (isCompact_complexUnipotentBall n u).exists_isMaxOn hne hcont.continuousOn
  refine ⟨f M, fun U hU i j => ?_⟩
  have hUadj : U⁻¹ = U.adjugate :=
    complex_inv_eq_adjugate_of_unipotent hU.1 hU.2.1
  rw [hUadj]
  refine le_trans ?_ (hmax hU)
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun a => ∑ b, ‖U.adjugate a b‖)
    (fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _)
    (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun b => ‖U.adjugate i b‖)
    (fun b _ => norm_nonneg _) (Finset.mem_univ j)

end GaloisForLFunctions.HTGeometry
