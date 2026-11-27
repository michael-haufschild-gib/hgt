import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedTailMeans
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockSuperdiagonal

/-! On an upper-block unitriangular matrix the Whittaker character factors
into the characters of the two blocks and the boundary root. -/

noncomputable section
open WindowedLandauTheory.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.GLq

variable {g a b : ℕ} [Fact g.Prime]

private theorem superdiagonal_upperBlocks (A : Mt g (a + 1))
    (X : Matrix (Fin (a + 1)) (Fin b) (ZMod g)) (D : Mt g b) :
    (∑ j ∈ Finset.range (a + 1 + b - 1), entN (upperBlockMatrix A X D) j (j + 1)) =
      (∑ j ∈ Finset.range a, entN A j (j + 1)) + lastRowFirstColumn X +
        ∑ j ∈ Finset.range (b - 1), entN D j (j + 1) := by
  cases b with
  | zero =>
    have he : X = 0 := Subsingleton.elim _ _
    subst X
    simpa only [lastRowFirstColumn, dif_neg (Nat.not_lt_zero 0), add_zero, Nat.add_sub_cancel]
      using superdiagonal_blockDiagonal A D
  | succ b =>
    let M := upperBlockMatrix A X D
    let B := upperBlockMatrix A 0 D
    let C := upperBlockMatrix (1 : Mt g (a + 1)) X D
    let E := upperBlockMatrix (1 : Mt g (a + 1)) 0 D
    have hM : M = B + C - E := by
      ext i j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [M, B, C, E, upperBlockMatrix]
    have he (j : ℕ) : entN M j (j + 1) =
        entN B j (j + 1) + entN C j (j + 1) - entN E j (j + 1) := by
      rw [hM]
      unfold entN
      split_ifs <;> simp
    change (∑ j ∈ Finset.range (a + 1 + (b + 1) - 1), entN M j (j + 1)) = _
    rw [Finset.sum_congr rfl fun j _ => he j, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    change (∑ j ∈ Finset.range (a + 1 + (b + 1) - 1), entN (upperBlockMatrix A 0 D) j (j + 1)) +
      (∑ j ∈ Finset.range (a + 1 + (b + 1) - 1), entN C j (j + 1)) -
      (∑ j ∈ Finset.range (a + 1 + (b + 1) - 1), entN E j (j + 1)) = _
    have hC := superdiagonal_upperBlock X D
    have hE := superdiagonal_upperBlock (0 : Matrix (Fin (a + 1)) (Fin (b + 1)) (ZMod g)) D
    change (∑ j ∈ Finset.range (a + 1 + (b + 1) - 1), entN C j (j + 1)) = _ at hC
    change (∑ j ∈ Finset.range (a + 1 + (b + 1) - 1), entN E j (j + 1)) = _ at hE
    rw [superdiagonal_blockDiagonal, hC, hE]
    simp only [Matrix.zero_apply, zero_add, Nat.add_sub_cancel, lastRowFirstColumn,
      dif_pos (Nat.succ_pos b)]
    abel

/-- The boundary root contributes the last row of the rectangle's first column. -/
theorem whittakerCharacter_upperBlocks (ψ : AddChar (ZMod g) ℂ)
    (A : upperUnitriangular g (a + 1)) (X : Matrix (Fin (a + 1)) (Fin b) (ZMod g))
    (D : upperUnitriangular g b) :
    (whittakerCharacter ψ (a + 1 + b) (unitriangularBlock A X D) : ℂ) =
      (whittakerCharacter ψ (a + 1) A : ℂ) *
        (ψ (lastRowFirstColumn X) * (whittakerCharacter ψ b D : ℂ)) := by
  change ψ (∑ j ∈ Finset.range (a + 1 + b - 1),
    entN (upperBlockMatrix A.val.val X D.val.val) j (j + 1)) =
    ψ (∑ j ∈ Finset.range a, entN A.val.val j (j + 1)) *
      (ψ (lastRowFirstColumn X) * ψ (∑ j ∈ Finset.range (b - 1), entN D.val.val j (j + 1)))
  rw [superdiagonal_upperBlocks, add_assoc, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]

/-- Appending an identity coordinate introduces no boundary phase. -/
theorem whittakerCharacter_append_one (ψ : AddChar (ZMod g) ℂ) (A : upperUnitriangular g a) :
    (whittakerCharacter ψ (a + 1) (unitriangularBlock A 0 (1 : upperUnitriangular g 1)) : ℂ) =
      (whittakerCharacter ψ a A : ℂ) := by
  change ψ (∑ j ∈ Finset.range (a + 1 - 1), entN (upperBlockMatrix A.val.val 0 (1 : Mt g 1)) j (j + 1)) =
    ψ (∑ j ∈ Finset.range (a - 1), entN A.val.val j (j + 1))
  rw [superdiagonal_blockDiagonal]
  simp

end GlobalTheory.GLq
