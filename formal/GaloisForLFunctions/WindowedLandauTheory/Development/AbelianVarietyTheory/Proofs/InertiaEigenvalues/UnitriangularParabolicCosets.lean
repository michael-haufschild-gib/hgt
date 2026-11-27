import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitriangularBruhatExistence
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.TwoBlockHarishChandraInduction
import GaloisForLFunctions.HTGeometry.BlockShuffleSign

/-! Permutation representatives of unitriangular–parabolic double cosets,
and the adjacent crossing in every cell outside the open cell. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions.HTGeometry WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

variable {g a b : ℕ} [Fact g.Prime]

abbrev permutationUnit {n : ℕ} (σ : Equiv.Perm (Fin n)) : Gn g n :=
  monomialUnit σ (fun _ => 1)

theorem upperUnitriangular_le_twoBlockParabolic :
    upperUnitriangular g (a + b) ≤ twoBlockParabolic g a b := by
  intro x hx i j hj hi
  exact (mem_upperUnitriangular.mp hx i j).1 (hj.trans_le hi)

private theorem monomial_mem_parabolic
    (σ : Equiv.Perm (Fin (a + b))) (c : Fin (a + b) → (ZMod g)ˣ)
    (h : ∀ j, j.val < a → (σ j).val < a) :
    monomialUnit σ c ∈ twoBlockParabolic g a b := by
  intro i j hj hi
  have he : i ≠ σ j := fun e => (not_lt_of_ge hi) (e.symm ▸ h j hj)
  simp [monomialUnit, signedMonomialMatrix, he]

/-- Every unitriangular–parabolic double coset has a permutation representative. -/
theorem exists_parabolic_permutation_rep (x : Gn g (a + b)) :
    ∃ σ : Equiv.Perm (Fin (a + b)),
      DoubleCoset.mk (upperUnitriangular g (a + b)) (twoBlockParabolic g a b) (permutationUnit σ) =
        DoubleCoset.mk (upperUnitriangular g (a + b)) (twoBlockParabolic g a b) x := by
  let U := upperUnitriangular g (a + b)
  let P := twoBlockParabolic g a b
  obtain ⟨l, r, σ, c, hx⟩ := exists_unitriangular_monomial g (a + b) x
  let d : Gn g (a + b) := monomialUnit (Equiv.refl _) c
  have hd : d ∈ P := monomial_mem_parabolic (Equiv.refl _) c (fun _ h => h)
  have hr : r.val ∈ P := upperUnitriangular_le_twoBlockParabolic r.property
  have hσ : monomialUnit σ c = permutationUnit σ * d := by
    apply Units.ext
    change signedMonomialMatrix σ c =
      signedMonomialMatrix σ (fun _ => 1) * signedMonomialMatrix (Equiv.refl _) c
    simp only [signedMonomialMatrix_mul, Equiv.refl_trans, one_mul]
  refine ⟨σ, (DoubleCoset.eq U P _ _).mpr ⟨l.val, l.property, d * r.val, P.mul_mem hd hr, ?_⟩⟩
  simp only [hx, hσ, mul_assoc]

/-- The image of the first block under a permutation. -/
def firstBlockImage (σ : Equiv.Perm (Fin (a + b))) : Finset (Fin (a + b)) :=
  (initSeg (a + b) a).map σ.toEmbedding

theorem mem_firstBlockImage (σ : Equiv.Perm (Fin (a + b))) (i : Fin (a + b)) :
    i ∈ firstBlockImage σ ↔ (σ.symm i).val < a := by
  rw [firstBlockImage, Finset.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa [initSeg] using hj
  · intro hi
    exact ⟨σ.symm i, by simpa [initSeg] using hi, σ.apply_symm_apply i⟩

theorem card_firstBlockImage (σ : Equiv.Perm (Fin (a + b))) : (firstBlockImage σ).card = a := by
  rw [firstBlockImage, Finset.card_map, card_initSeg (Nat.le_add_right a b)]

/-- Permutations with the same first-block image give the same double coset. -/
theorem parabolic_coset_eq_of_firstBlockImage_eq (σ τ : Equiv.Perm (Fin (a + b)))
    (h : firstBlockImage σ = firstBlockImage τ) :
    DoubleCoset.mk (upperUnitriangular g (a + b)) (twoBlockParabolic g a b) (permutationUnit τ) =
      DoubleCoset.mk (upperUnitriangular g (a + b)) (twoBlockParabolic g a b) (permutationUnit σ) := by
  let U := upperUnitriangular g (a + b)
  let P := twoBlockParabolic g a b
  let ρ := σ.trans τ.symm
  have hρ : permutationUnit ρ ∈ P := by
    apply monomial_mem_parabolic
    intro j hj
    have he : σ j ∈ firstBlockImage σ := (mem_firstBlockImage σ (σ j)).mpr (by simpa using hj)
    rw [h] at he
    exact (mem_firstBlockImage τ (σ j)).mp he
  refine (DoubleCoset.eq U P _ _).mpr ⟨1, U.one_mem, permutationUnit ρ, hρ, ?_⟩
  rw [one_mul]
  apply Units.ext
  change signedMonomialMatrix σ (fun _ => 1) =
    signedMonomialMatrix τ (fun _ => 1) * signedMonomialMatrix ρ (fun _ => 1)
  rw [signedMonomialMatrix_mul]
  have he : ρ.trans τ = σ := Equiv.ext fun i => τ.apply_symm_apply (σ i)
  simp only [he, one_mul]

/-- The open-cell permutation moves the first block behind the second. -/
def openCellPermutation (a b : ℕ) : Equiv.Perm (Fin (a + b)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumComm (Fin a) (Fin b)).trans (finSumFinEquiv.trans (finCongr (Nat.add_comm b a))))

theorem openCellPermutation_left (i : Fin a) :
    (openCellPermutation a b (Fin.castAdd b i)).val = b + i.val := by
  simp [openCellPermutation, Nat.add_comm]

theorem openCellPermutation_right (j : Fin b) :
    (openCellPermutation a b (Fin.natAdd a j)).val = j.val := by
  simp [openCellPermutation]

theorem firstBlockImage_openCellPermutation :
    firstBlockImage (openCellPermutation a b) = (initSeg (a + b) b)ᶜ := by
  ext i
  obtain ⟨j, rfl⟩ := (openCellPermutation a b).surjective i
  rw [mem_firstBlockImage, Equiv.symm_apply_apply, Finset.mem_compl]
  simp only [initSeg, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [openCellPermutation_left]
    exact iff_of_true j.isLt (Nat.le_add_right _ _)
  · rw [openCellPermutation_right]
    exact iff_of_false (not_lt_of_ge (Nat.le_add_right a j.val)) (not_le_of_gt j.isLt)

/-- In every other cell, a simple upper root crosses from the first block to the second. -/
theorem exists_adjacent_crossing (σ : Equiv.Perm (Fin (a + b)))
    (h : firstBlockImage σ ≠ firstBlockImage (openCellPermutation a b)) :
    ∃ i j : Fin (a + b), i.val < a ∧ a ≤ j.val ∧ (σ i).val + 1 = (σ j).val := by
  let S := firstBlockImage σ
  have hc : Sᶜ.card = b := (card_compl_fin (card_firstBlockImage σ)).trans (Nat.add_sub_cancel_left a b)
  have hn : Sᶜ ≠ initSeg (a + b) b := by
    intro e
    apply h
    rw [firstBlockImage_openCellPermutation]
    exact (compl_compl S).symm.trans (congrArg (fun T : Finset (Fin (a + b)) => Tᶜ) e)
  obtain ⟨x, hx, hx1, hy⟩ := exists_mem_pred_not_mem hc hn
  let y : Fin (a + b) := ⟨x.val - 1, by have := x.isLt; omega⟩
  have hyS : y ∈ S := by
    change y ∉ Sᶜ at hy
    simpa only [Finset.mem_compl, not_not] using hy
  refine ⟨σ.symm y, σ.symm x, (mem_firstBlockImage σ y).mp hyS, ?_, ?_⟩
  · exact Nat.le_of_not_gt (fun hh => (Finset.mem_compl.mp hx) ((mem_firstBlockImage σ x).mpr hh))
  · rw [σ.apply_symm_apply, σ.apply_symm_apply]
    exact Nat.sub_add_cancel hx1

end GlobalTheory.GLq
