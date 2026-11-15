import GaloisForLFunctions.BiarithmeticGeometry.Affine.SigmaBlockAlgebra
import Mathlib.Data.Prod.Lex

/-!
# Block matrices whose off-diagonal terms strictly lower a rank

An off-diagonal block may be nonzero only when its column has smaller rank
than its row. The condition is closed under multiplication, diagonal blocks
multiply separately, and determinants factor over the original block labels.
No injectivity of the rank and no order on the block labels is required.
-/

open Matrix
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume

namespace GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix
noncomputable section
variable {ι : Type*} {κ : ι → Type*} {R : Type*}

/-- Every nonzero off-diagonal block strictly lowers the assigned natural rank. -/
def RankLower [Zero R] (ρ : ι → ℕ) (M : Matrix (Sigma κ) (Sigma κ) R) : Prop :=
  ∀ a b, a.1 ≠ b.1 → ρ a.1 ≤ ρ b.1 → M a b = 0

theorem rankLower_blockDiagonal [DecidableEq ι] [Zero R] (ρ : ι → ℕ)
    (B : ∀ i, Matrix (κ i) (κ i) R) : RankLower ρ (Matrix.blockDiagonal' B) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ hij _
  exact Matrix.blockDiagonal'_apply_ne B x y hij

theorem rankLower_one [DecidableEq ι] [∀ i, DecidableEq (κ i)] [Zero R] [One R]
    (ρ : ι → ℕ) : RankLower ρ (1 : Matrix (Sigma κ) (Sigma κ) R) := by
  intro a b hab _
  have hne : a ≠ b := fun h => hab (congrArg (fun c : Sigma κ => c.1) h)
  simp only [Matrix.one_apply, if_neg hne]

/-- Products cannot create a nonzero block at an equal or higher distinct rank. -/
theorem RankLower.mul [Fintype ι] [∀ i, Fintype (κ i)] [Semiring R]
    {ρ : ι → ℕ} {M N : Matrix (Sigma κ) (Sigma κ) R}
    (hM : RankLower ρ M) (hN : RankLower ρ N) : RankLower ρ (M * N) := by
  classical
  intro a b hab hr
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hac : a.1 = c.1
  · have hcb : c.1 ≠ b.1 := fun h => hab (hac.trans h)
    have hrc : ρ c.1 ≤ ρ b.1 := by simpa only [hac] using hr
    rw [hN c b hcb hrc, mul_zero]
  · by_cases hρ : ρ a.1 ≤ ρ c.1
    · rw [hM a c hac hρ, zero_mul]
    · have hcb : c.1 ≠ b.1 := by
        intro h
        apply hρ
        simpa only [h] using hr
      have hrc : ρ c.1 ≤ ρ b.1 := by omega
      rw [hN c b hcb hrc, mul_zero]

/-- Diagonal blocks multiply independently under strict rank lowering. -/
theorem diagonalBlock_mul_of_rankLower [Fintype ι] [∀ i, Fintype (κ i)] [Semiring R]
    {ρ : ι → ℕ} {M N : Matrix (Sigma κ) (Sigma κ) R}
    (hM : RankLower ρ M) (hN : RankLower ρ N) (i : ι) :
    diagonalBlock (M * N) i = diagonalBlock M i * diagonalBlock N i := by
  classical
  ext x y
  change (∑ a : Sigma κ, M ⟨i, x⟩ a * N a ⟨i, y⟩) = _
  rw [Fintype.sum_sigma, Finset.sum_eq_single i]
  · rfl
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro z _
    by_cases hρ : ρ i ≤ ρ j
    · rw [hM ⟨i, x⟩ ⟨j, z⟩ hji.symm hρ, zero_mul]
    · rw [hN ⟨j, z⟩ ⟨i, y⟩ hji (show ρ j ≤ ρ i by omega), mul_zero]
  · simp

private abbrev rankOrder [Fintype ι] [hEq : DecidableEq ι] (ρ : ι → ℕ) : LinearOrder ι :=
  let o := LinearOrder.lift' (fun i => toLex (ρ i, Fintype.equivFin ι i)) (fun a b h => by
    apply (Fintype.equivFin ι).injective
    have hp : (ρ a, Fintype.equivFin ι a) = (ρ b, Fintype.equivFin ι b) := h
    exact congrArg Prod.snd hp)
  { o with
    toDecidableEq := hEq
    compare_eq_compareOfLessAndEq := by
      intro a b
      have h := o.compare_eq_compareOfLessAndEq a b
      have he : o.toDecidableEq = hEq := Subsingleton.elim _ _
      exact h.trans (congrArg
        (fun deq : DecidableEq ι => @compareOfLessAndEq ι a b o.toLT (o.toDecidableLT a b) deq) he) }

private theorem rank_le_of_rankOrder_lt [Fintype ι] [DecidableEq ι] (ρ : ι → ℕ) {a b : ι}
    (h : @LT.lt ι (rankOrder ρ).toLT a b) : ρ a ≤ ρ b := by
  change toLex (ρ a, Fintype.equivFin ι a) < toLex (ρ b, Fintype.equivFin ι b) at h
  exact (Prod.Lex.toLex_lt_toLex'.mp h).1

/-- Strict rank lowering suffices for the product determinant law, including repeated ranks. -/
theorem det_of_rankLower [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [CommRing R]
    {ρ : ι → ℕ} (M : Matrix (Sigma κ) (Sigma κ) R) (hM : RankLower ρ M) :
    M.det = ∏ i, (diagonalBlock M i).det := by
  letI : LinearOrder ι := rankOrder ρ
  apply det_of_lower
  intro a b hab
  exact hM a b (ne_of_lt hab) (rank_le_of_rankOrder_lt ρ hab)

/-- Blockwise selected determinants obey the same factorization under strict rank lowering. -/
theorem det_selectedMatrix_of_rankLower [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    {ρ : ι → ℕ} (M : Matrix (Sigma κ) (Sigma κ) ℝ) (hM : RankLower ρ M)
    (s : ∀ i, κ i → κ i ⊕ κ i) :
    (selectedMatrix M (blockSelector s)).det =
      ∏ i, (selectedMatrix (diagonalBlock M i) (s i)).det := by
  letI : LinearOrder ι := rankOrder ρ
  apply det_selectedMatrix_of_lower
  intro a b hab
  exact hM a b (ne_of_lt hab) (rank_le_of_rankOrder_lt ρ hab)

#print axioms rankLower_blockDiagonal
#print axioms rankLower_one
#print axioms RankLower.mul
#print axioms diagonalBlock_mul_of_rankLower
#print axioms det_of_rankLower
#print axioms det_selectedMatrix_of_rankLower

end
end GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix
