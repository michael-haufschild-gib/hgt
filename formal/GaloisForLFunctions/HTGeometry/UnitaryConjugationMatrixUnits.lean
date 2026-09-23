import Mathlib

/-!
# Unitary conjugation of matrix units

Conjugation by a diagonal unitary multiplies the matrix unit `E i j` by the phase
`conj (w i) * w j`, and conjugation by a permutation matrix relabels it as `E (σ i) (σ j)`.
Consequently a linear map on matrices that commutes with unitary conjugation sends every
off-diagonal matrix unit to a multiple of itself: two diagonal phase families, one supported at the
row index and one at the column index, kill every other entry.

These are the coordinate tools behind the classification of conjugation-equivariant linear maps.
-/

namespace GaloisForLFunctions.EquivariantCausalizer

open Matrix

variable {n : ℕ}

theorem diagonal_mul_single (w : Fin n → ℂ) (i j : Fin n) (c : ℂ) :
    diagonal w * Matrix.single i j c = Matrix.single i j (w i * c) := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single k]
  · by_cases hk : i = k
    · subst hk
      simp
    · simp [hk]
  · intro b _ hb
    simp [Ne.symm hb]
  · intro hb
    exact absurd (Finset.mem_univ k) hb

theorem single_mul_diagonal (w : Fin n → ℂ) (i j : Fin n) (c : ℂ) :
    Matrix.single i j c * diagonal w = Matrix.single i j (c * w j) := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single l]
  · by_cases hl : j = l
    · subst hl
      by_cases hk : i = k <;> simp [hk]
    · simp [hl]
  · intro b _ hb
    simp [hb]
  · intro hb
    exact absurd (Finset.mem_univ l) hb

theorem diagonal_conj_single (w : Fin n → ℂ) (i j : Fin n) :
    (diagonal w)ᴴ * Matrix.single i j (1 : ℂ) * diagonal w
      = ((starRingEnd ℂ) (w i) * w j) • Matrix.single i j (1 : ℂ) := by
  rw [Matrix.diagonal_conjTranspose, diagonal_mul_single, single_mul_diagonal,
    Matrix.smul_single]
  congr 1
  simp [Pi.star_apply]

theorem mem_unitaryGroup_diagonal (w : Fin n → ℂ) (hw : ∀ i, ‖w i‖ = 1) :
    diagonal w ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  have hsq : Complex.normSq (w i) = 1 := by
    have h1 := hw i
    have h2 : ‖w i‖ ^ (2 : ℕ) = 1 := by rw [h1]; norm_num
    rw [← Complex.normSq_eq_norm_sq] at h2
    exact h2
  have hmul : (w i) * (starRingEnd ℂ) (w i) = 1 := by
    rw [Complex.mul_conj, hsq]
    norm_num
  simpa [Pi.star_apply] using hmul


theorem permMatrix_apply (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (Equiv.Perm.permMatrix ℂ σ) i j = if σ i = j then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

theorem mem_unitaryGroup_permMatrix (σ : Equiv.Perm (Fin n)) :
    (Equiv.Perm.permMatrix ℂ σ) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, permMatrix_apply, Matrix.one_apply,
    RCLike.star_def]
  rw [Finset.sum_eq_single (σ i)]
  · by_cases h : i = k
    · subst h; simp
    · have hσ : σ k ≠ σ i := fun hc => h (σ.injective hc).symm
      simp [h, hσ]
  · intro b _ hb
    simp [Ne.symm hb]
  · intro hb
    exact absurd (Finset.mem_univ (σ i)) hb

theorem permMatrix_conj_single (σ : Equiv.Perm (Fin n)) (i j : Fin n) (c : ℂ) :
    (Equiv.Perm.permMatrix ℂ σ)ᴴ * Matrix.single i j c * (Equiv.Perm.permMatrix ℂ σ)
      = Matrix.single (σ i) (σ j) c := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, permMatrix_apply,
    Matrix.single_apply, RCLike.star_def]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · by_cases hk : σ i = k
      · by_cases hl : σ j = l
        · simp [hk, hl]
        · simp [hk, hl]
      · simp [hk]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hb
      exact absurd (Finset.mem_univ i) hb
  · intro b _ hb
    have hz : (∑ x, (starRingEnd ℂ) (if σ x = k then 1 else 0) *
        (if i = x ∧ j = b then c else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      simp [Ne.symm hb]
    rw [hz, zero_mul]
  · intro hb
    exact absurd (Finset.mem_univ j) hb


theorem diagonal_conj_entry (w : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (k l : Fin n) :
    ((diagonal w)ᴴ * M * diagonal w) k l = (starRingEnd ℂ) (w k) * M k l * w l := by
  rw [Matrix.diagonal_conjTranspose]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single l]
  · rw [Finset.sum_eq_single k]
    · simp [Pi.star_apply]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hb
      exact absurd (Finset.mem_univ k) hb
  · intro b _ hb
    simp [hb]
  · intro hb
    exact absurd (Finset.mem_univ l) hb

/-- The phase equation satisfied by the image of a matrix unit under a conjugation-equivariant
linear map. -/
theorem phase_equation (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hL : ∀ V ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, L (Vᴴ * A * V) = Vᴴ * L A * V)
    (i j : Fin n) (w : Fin n → ℂ) (hw : ∀ x, ‖w x‖ = 1) (k l : Fin n) :
    (starRingEnd ℂ) (w i) * w j * (L (Matrix.single i j 1)) k l
      = (starRingEnd ℂ) (w k) * ((L (Matrix.single i j 1)) k l) * w l := by
  have h := hL (diagonal w) (mem_unitaryGroup_diagonal w hw) (Matrix.single i j 1)
  rw [diagonal_conj_single, map_smul] at h
  have hentry := congrFun (congrFun h k) l
  rw [diagonal_conj_entry] at hentry
  simpa using hentry

theorem eq_zero_of_mul_eq_mul {a b z : ℂ} (h : a * z = b * z) (hne : a ≠ b) : z = 0 := by
  by_contra hz
  exact hne (mul_right_cancel₀ hz h)

theorem phase_equation' (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hL : ∀ V ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, L (Vᴴ * A * V) = Vᴴ * L A * V)
    (i j : Fin n) (w : Fin n → ℂ) (hw : ∀ x, ‖w x‖ = 1) (k l : Fin n) :
    ((starRingEnd ℂ) (w i) * w j) * (L (Matrix.single i j 1)) k l
      = ((starRingEnd ℂ) (w k) * w l) * ((L (Matrix.single i j 1)) k l) := by
  have h := phase_equation L hL i j w hw k l
  rw [h]
  ring

/-- The image of an off-diagonal matrix unit is supported at that unit. -/
theorem exists_offDiag_coeff (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hL : ∀ V ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, L (Vᴴ * A * V) = Vᴴ * L A * V)
    {i j : Fin n} (hij : i ≠ j) :
    ∃ c : ℂ, L (Matrix.single i j 1) = Matrix.single i j c := by
  classical
  have hwI : ∀ (m : Fin n), ∀ x : Fin n, ‖(if x = m then Complex.I else 1 : ℂ)‖ = 1 := by
    intro m x
    by_cases h : x = m <;> simp [h]
  have hInel : Complex.I ≠ 1 := by
    intro hc
    have := congrArg Complex.im hc
    simp at this
  have hnegInel : -Complex.I ≠ 1 := by
    intro hc
    have := congrArg Complex.im hc
    simp at this
  have hnegIneI : -Complex.I ≠ Complex.I := by
    intro hc
    have h2 := congrArg Complex.im hc
    simp at h2
    norm_num at h2
  have hzero : ∀ k l, ¬ (k = i ∧ l = j) → (L (Matrix.single i j 1)) k l = 0 := by
    intro k l hkl
    by_cases hk : k = i
    · subst hk
      have hln : l ≠ j := fun hc => hkl ⟨rfl, hc⟩
      have h := phase_equation' L hL k j (fun x => if x = j then Complex.I else 1) (hwI j) k l
      have e1 : (starRingEnd ℂ) (if k = j then Complex.I else 1) *
          (if j = j then Complex.I else 1) = Complex.I := by
        rw [if_neg hij, if_pos rfl]
        simp
      have e2 : (starRingEnd ℂ) (if k = j then Complex.I else 1) *
          (if l = j then Complex.I else 1) = 1 := by
        rw [if_neg hij, if_neg hln]
        simp
      rw [e1, e2] at h
      exact eq_zero_of_mul_eq_mul h hInel
    · have h := phase_equation' L hL i j (fun x => if x = i then Complex.I else 1) (hwI i) k l
      have e1 : (starRingEnd ℂ) (if i = i then Complex.I else 1) *
          (if j = i then Complex.I else 1) = -Complex.I := by
        rw [if_pos rfl, if_neg (Ne.symm hij)]
        simp [Complex.conj_I]
      by_cases hli : l = i
      · have e2 : (starRingEnd ℂ) (if k = i then Complex.I else 1) *
            (if l = i then Complex.I else 1) = Complex.I := by
          rw [if_neg hk, if_pos hli]
          simp
        rw [e1, e2] at h
        exact eq_zero_of_mul_eq_mul h hnegIneI
      · have e2 : (starRingEnd ℂ) (if k = i then Complex.I else 1) *
            (if l = i then Complex.I else 1) = 1 := by
          rw [if_neg hk, if_neg hli]
          simp
        rw [e1, e2] at h
        exact eq_zero_of_mul_eq_mul h hnegInel
  refine ⟨(L (Matrix.single i j 1)) i j, ?_⟩
  ext k l
  rw [Matrix.single_apply]
  by_cases h : i = k ∧ j = l
  · obtain ⟨hk, hl⟩ := h
    subst hk; subst hl
    simp
  · rw [if_neg h]
    exact hzero k l (fun hc => h ⟨hc.1.symm, hc.2.symm⟩)

end GaloisForLFunctions.EquivariantCausalizer
