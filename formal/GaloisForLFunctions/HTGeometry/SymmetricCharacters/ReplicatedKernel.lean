import GaloisForLFunctions.HTGeometry.SymmetricCharacters.FiniteColoring
import Mathlib.Algebra.Order.Star.Real

/-!
# Positivity under arbitrarily many replicas

A replicated kernel consists of a shared block kernel and an independent diagonal correction.
Constant vectors on each block isolate the shared quadratic form; differences of two replicas
isolate the correction. Thus diagonal noise cannot conceal a negative shared direction at every
replication number.
-/

noncomputable section
open scoped BigOperators Classical

namespace GaloisForLFunctions.SymmetricCharacters

variable {I : Type*} [Fintype I]

/-- Repeat every index and add independent noise on each repeated diagonal entry. -/
def replicatedKernel (H : Matrix I I ℝ) (d : I → ℝ) (n : ℕ) :
    Matrix (I × Fin n) (I × Fin n) ℝ :=
  H.submatrix Prod.fst Prod.fst + Matrix.diagonal (fun i => d i.1)

/-- Constant block vectors separate the quadratic and linear replication terms. -/
theorem replicatedKernel_constant_quadratic (H : Matrix I I ℝ) (d v : I → ℝ) (n : ℕ) :
    dotProduct (fun i : I × Fin n => v i.1)
        ((replicatedKernel H d n).mulVec (fun i => v i.1)) =
      (n : ℝ) ^ 2 * dotProduct v (H.mulVec v) +
        n * ∑ i, d i * v i ^ 2 := by
  rw [replicatedKernel, Matrix.add_mulVec, dotProduct_add]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  simp only [← Finset.mul_sum]
  congr 1
  · simp only [pow_two, mul_assoc]
    congr 1
    symm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

private theorem nonneg_of_all_replications (q d : ℝ)
    (h : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ 2 * q + n * d) : 0 ≤ q := by
  by_contra hq
  have hq : q < 0 := lt_of_not_ge hq
  obtain ⟨n, hn⟩ := exists_nat_gt (max 0 (d / (-q)))
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hnd : d < (n : ℝ) * (-q) :=
    (div_lt_iff₀ (neg_pos.mpr hq)).mp (lt_of_le_of_lt (le_max_right _ _) hn)
  have hneg : (n : ℝ) * ((n : ℝ) * q + d) < 0 :=
    mul_neg_of_pos_of_neg hnpos (by linarith)
  have hnq := h n
  nlinarith only [hneg, hnq]

/-- Exact finite-replication threshold for detecting a negative shared direction. -/
theorem replicatedKernel_constant_negative_iff (H : Matrix I I ℝ) (d v : I → ℝ)
    {n : ℕ} (hn : 0 < n) :
    dotProduct (fun i : I × Fin n => v i.1)
        ((replicatedKernel H d n).mulVec (fun i => v i.1)) < 0 ↔
      (n : ℝ) * dotProduct v (H.mulVec v) + ∑ i, d i * v i ^ 2 < 0 := by
  rw [replicatedKernel_constant_quadratic]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [show (n : ℝ) ^ 2 * dotProduct v (H.mulVec v) + n * ∑ i, d i * v i ^ 2 =
    n * ((n : ℝ) * dotProduct v (H.mulVec v) + ∑ i, d i * v i ^ 2) by ring]
  constructor
  · intro h
    nlinarith only [h, hn']
  · exact mul_neg_of_pos_of_neg hn'

/-- Arbitrary replication is positive exactly when the shared kernel and noise are positive. -/
theorem forall_replicatedKernel_posSemidef_iff (H : Matrix I I ℝ) (d : I → ℝ) :
    (∀ n, (replicatedKernel H d n).PosSemidef) ↔
      H.PosSemidef ∧ ∀ i, 0 ≤ d i := by
  constructor
  · intro h
    constructor
    · rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      constructor
      · apply Matrix.IsHermitian.ext
        intro i j
        have hh := (h 2).isHermitian.apply (i, 0) (j, 1)
        simpa [replicatedKernel, Matrix.diagonal_apply] using hh
      · intro v
        apply nonneg_of_all_replications _ (∑ i, d i * v i ^ 2)
        intro n
        have hv := (h n).dotProduct_mulVec_nonneg (fun i => v i.1)
        simpa only [star_trivial, replicatedKernel_constant_quadratic] using hv
    · intro i
      have hp := (h 2).submatrix (fun a : Fin 2 => (i, a))
      have hv := hp.dotProduct_mulVec_nonneg ![1, -1]
      simp [replicatedKernel, Matrix.diagonal_apply, dotProduct, Matrix.mulVec,
        Fin.sum_univ_two] at hv
      linarith
  · rintro ⟨hH, hd⟩ n
    exact (hH.submatrix Prod.fst).add (Matrix.PosSemidef.diagonal (fun i => hd i.1))

/-- For normalized Gram matrices the diagonal correction is exactly one minus the shared diagonal. -/
theorem forall_normalizedReplicas_posSemidef_iff (H : Matrix I I ℝ) :
    (∀ n, (replicatedKernel H (fun i => 1 - H i i) n).PosSemidef) ↔
      H.PosSemidef ∧ ∀ i, H i i ≤ 1 := by
  rw [forall_replicatedKernel_posSemidef_iff]
  simp only [sub_nonneg]

end GaloisForLFunctions.SymmetricCharacters
