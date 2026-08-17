import Mathlib
import GaloisForLFunctions.HTGeometry.UnitaryConjugationMatrixUnits

/-!
# The two-index block algebra and its unitary

For two distinct indices `i ≠ j` the four matrices

`P = E i i + E j j`, `Q = E i j + E j i`, `Z = E i i - E j j`, `R = E i j - E j i`

multiply inside the span of themselves, and `V = 1 + ((1+I)/2 - 1) P + ((1-I)/2) Q` is unitary.
Conjugating `Z` by `V` produces `-I R`: the two-index block unitary rotates the diagonal difference
onto the antisymmetric off-diagonal pair.  This is the one non-monomial unitary needed to relate the
diagonal and off-diagonal constants of a conjugation-equivariant linear map, and the reason such a
map has only two parameters.

The module also records the transport of matrix units under permutation matrices, the diagonality of
the image of a diagonal matrix unit, and the existence of a permutation carrying one ordered pair of
distinct indices to another.
-/

namespace GaloisForLFunctions.EquivariantCausalizer

open Matrix

variable {n : ℕ}

theorem unitPhase_ite (m : Fin n) : ∀ x : Fin n, ‖(if x = m then Complex.I else 1 : ℂ)‖ = 1 := by
  intro x
  by_cases h : x = m <;> simp [h]

/-- The image of a diagonal matrix unit is diagonal. -/
theorem diag_image_offDiag_eq_zero (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hL : ∀ V ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, L (Vᴴ * A * V) = Vᴴ * L A * V)
    (i : Fin n) {k l : Fin n} (hkl : l ≠ k) :
    (L (Matrix.single i i 1)) k l = 0 := by
  have h := phase_equation' L hL i i (fun x => if x = k then Complex.I else 1) (unitPhase_ite k) k l
  have e1 : (starRingEnd ℂ) (if i = k then Complex.I else 1) *
      (if i = k then Complex.I else 1) = 1 := by
    by_cases hik : i = k
    · rw [if_pos hik]
      simp [Complex.conj_I]
    · rw [if_neg hik]
      simp
  have e2 : (starRingEnd ℂ) (if k = k then Complex.I else 1) *
      (if l = k then Complex.I else 1) = -Complex.I := by
    rw [if_pos rfl, if_neg hkl]
    simp [Complex.conj_I]
  rw [e1, e2] at h
  refine eq_zero_of_mul_eq_mul h ?_
  intro hc
  have h2 := congrArg Complex.im hc
  simp at h2

/-- Entries of a permutation conjugate. -/
theorem permMatrix_conj_entry (σ : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ)
    (k l : Fin n) :
    ((Equiv.Perm.permMatrix ℂ σ)ᴴ * M * (Equiv.Perm.permMatrix ℂ σ)) k l
      = M (σ.symm k) (σ.symm l) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, permMatrix_apply, RCLike.star_def]
  rw [Finset.sum_eq_single (σ.symm l)]
  · rw [Finset.sum_eq_single (σ.symm k)]
    · simp
    · intro b _ hb
      have : σ b ≠ k := by
        intro hc
        exact hb (by rw [← hc, Equiv.symm_apply_apply])
      simp [this]
    · intro hb
      exact absurd (Finset.mem_univ (σ.symm k)) hb
  · intro b _ hb
    have : σ b ≠ l := by
      intro hc
      exact hb (by rw [← hc, Equiv.symm_apply_apply])
    simp [this]
  · intro hb
    exact absurd (Finset.mem_univ (σ.symm l)) hb

/-- Permutation transport of the image of a matrix unit. -/
theorem perm_transport (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hL : ∀ V ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, L (Vᴴ * A * V) = Vᴴ * L A * V)
    (σ : Equiv.Perm (Fin n)) (i j k l : Fin n) :
    (L (Matrix.single (σ i) (σ j) 1)) k l = (L (Matrix.single i j 1)) (σ.symm k) (σ.symm l) := by
  have h := hL _ (mem_unitaryGroup_permMatrix σ) (Matrix.single i j 1)
  rw [permMatrix_conj_single] at h
  rw [h, permMatrix_conj_entry]

/-- For two ordered pairs of distinct indices there is a permutation carrying one to the other. -/
theorem exists_perm_map_pair {i j i' j' : Fin n} (hij : i ≠ j) (hij' : i' ≠ j') :
    ∃ σ : Equiv.Perm (Fin n), σ i = i' ∧ σ j = j' := by
  classical
  set σ₁ := Equiv.swap i i' with hσ₁
  have h1 : σ₁ i = i' := by simp [hσ₁]
  set j₁ := σ₁ j with hj₁
  have hj₁i' : j₁ ≠ i' := by
    rw [hj₁, ← h1]
    exact fun hc => hij (σ₁.injective hc).symm
  set σ₂ := Equiv.swap j₁ j' with hσ₂
  have h2 : σ₂ i' = i' := by
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
    · exact Ne.symm hj₁i'
    · exact hij'
  refine ⟨σ₁.trans σ₂, ?_, ?_⟩
  · show σ₂ (σ₁ i) = i'
    rw [h1, h2]
  · show σ₂ (σ₁ j) = j'
    rw [← hj₁, hσ₂]
    simp


section TwoBlock

variable {i j : Fin n}

/-- The `{i,j}`-block unitary with entries `(1 ± I)/2`. -/
noncomputable def blockP (i j : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.single i i 1 + Matrix.single j j 1

noncomputable def blockQ (i j : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.single i j 1 + Matrix.single j i 1

noncomputable def blockZ (i j : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.single i i 1 - Matrix.single j j 1

noncomputable def blockR (i j : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.single i j 1 - Matrix.single j i 1

theorem blockP_mul_blockP (hij : i ≠ j) : blockP i j * blockP i j = blockP i j := by
  simp only [blockP, add_mul, mul_add, one_mul, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hij)]
  abel

theorem blockQ_mul_blockQ (hij : i ≠ j) : blockQ i j * blockQ i j = blockP i j := by
  simp only [blockP, blockQ, add_mul, mul_add, one_mul, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hij)]
  abel

theorem blockP_mul_blockQ (hij : i ≠ j) : blockP i j * blockQ i j = blockQ i j := by
  simp only [blockP, blockQ, add_mul, mul_add, one_mul, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hij)]
  abel

theorem blockQ_mul_blockP (hij : i ≠ j) : blockQ i j * blockP i j = blockQ i j := by
  simp only [blockP, blockQ, add_mul, mul_add, one_mul, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hij)]
  abel

theorem blockP_mul_blockZ (hij : i ≠ j) : blockP i j * blockZ i j = blockZ i j := by
  simp only [blockP, blockZ, add_mul, mul_sub, one_mul, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hij)]
  abel

theorem blockZ_mul_blockP (hij : i ≠ j) : blockZ i j * blockP i j = blockZ i j := by
  simp only [blockP, blockZ, sub_mul, mul_add, one_mul, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hij)]
  abel

theorem blockZ_mul_blockQ (hij : i ≠ j) : blockZ i j * blockQ i j = blockR i j := by
  simp only [blockQ, blockZ, blockR, sub_mul, mul_add, one_mul, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hij)]
  abel

theorem blockQ_mul_blockZ (hij : i ≠ j) : blockQ i j * blockZ i j = -blockR i j := by
  simp only [blockQ, blockZ, blockR, add_mul, mul_sub, one_mul, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hij)]
  abel

theorem blockP_mul_blockR (hij : i ≠ j) : blockP i j * blockR i j = blockR i j := by
  simp only [blockP, blockR, add_mul, mul_sub, one_mul, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hij)]
  abel

theorem blockR_mul_blockP (hij : i ≠ j) : blockR i j * blockP i j = blockR i j := by
  simp only [blockP, blockR, sub_mul, mul_add, one_mul, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hij)]
  abel

theorem blockQ_mul_blockR (hij : i ≠ j) : blockQ i j * blockR i j = -blockZ i j := by
  simp only [blockQ, blockZ, blockR, add_mul, mul_sub, one_mul, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hij)]
  abel

theorem blockR_mul_blockQ (hij : i ≠ j) : blockR i j * blockQ i j = blockZ i j := by
  simp only [blockR, blockQ, blockZ, sub_mul, mul_add, one_mul, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hij,
    Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hij)]
  abel

theorem blockR_mul_blockR (hij : i ≠ j) : blockR i j * blockR i j = -blockP i j := by
  simp only [blockR, blockP, sub_mul, mul_sub, one_mul, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hij,
    Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hij)]
  abel

theorem blockZ_mul_blockZ (hij : i ≠ j) : blockZ i j * blockZ i j = blockP i j := by
  simp only [blockP, blockZ, sub_mul, mul_sub, one_mul, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hij)]
  abel

end TwoBlock


section BlockUnitary

variable {i j : Fin n}

theorem blockP_conjTranspose : (blockP i j)ᴴ = blockP i j := by
  simp [blockP, Matrix.conjTranspose_add, Matrix.conjTranspose_single]

theorem blockQ_conjTranspose : (blockQ i j)ᴴ = blockQ i j := by
  simp [blockQ, Matrix.conjTranspose_add, Matrix.conjTranspose_single]
  abel

theorem blockZ_conjTranspose : (blockZ i j)ᴴ = blockZ i j := by
  simp [blockZ, Matrix.conjTranspose_sub, Matrix.conjTranspose_single]

/-- The `{i,j}`-block unitary with entries `(1 ± I)/2`. -/
noncomputable def blockUnitary (i j : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  1 + ((1 + Complex.I) / 2 - 1) • blockP i j + ((1 - Complex.I) / 2) • blockQ i j

theorem blockUnitary_conjTranspose :
    (blockUnitary i j)ᴴ = 1 + ((1 - Complex.I) / 2 - 1) • blockP i j
      + ((1 + Complex.I) / 2) • blockQ i j := by
  simp only [blockUnitary, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, blockP_conjTranspose, blockQ_conjTranspose]
  congr 2
  · congr 1
    simp [Complex.conj_I]
    ring
  · simp [Complex.conj_I]


theorem blockUnitary_mem_unitaryGroup (hij : i ≠ j) :
    blockUnitary i j ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, blockUnitary_conjTranspose]
  simp only [blockUnitary, add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, blockP_mul_blockP hij, blockP_mul_blockQ hij, blockQ_mul_blockP hij,
    blockQ_mul_blockQ hij]
  match_scalars <;> norm_num [Complex.ext_iff]


theorem blockUnitary_conj_blockZ (hij : i ≠ j) :
    (blockUnitary i j)ᴴ * blockZ i j * blockUnitary i j = (-Complex.I) • blockR i j := by
  rw [blockUnitary_conjTranspose]
  simp only [blockUnitary, add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, smul_neg, neg_smul, neg_mul,
    blockP_mul_blockZ hij, blockZ_mul_blockP hij, blockZ_mul_blockQ hij,
    blockQ_mul_blockZ hij, blockR_mul_blockP hij, blockR_mul_blockQ hij]
  match_scalars <;> norm_num [Complex.ext_iff]

end BlockUnitary

end GaloisForLFunctions.EquivariantCausalizer
