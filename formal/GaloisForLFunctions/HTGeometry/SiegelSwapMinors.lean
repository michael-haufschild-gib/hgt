import GaloisForLFunctions.HTGeometry.SiegelPotential

/-!
# A swap moves only one leading minor

Conjugating by the permutation matrix of a transposition rewrites the form entrywise as
`A'ₐᵦ = A_{σa,σb}`.  A leading block below both swapped indices is therefore untouched, and a
leading block above both is the old one permuted, so its determinant is unchanged.  Only the block
that separates the two indices can move.

* `permMatrix_congr_apply` : the entries of a permutation congruate.
* `leadingBlock_swap_low` : blocks below both indices are unchanged.
* `det_leadingBlock_swap_high` : blocks above both indices have unchanged determinant.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- **The entries of a permutation congruate.** -/
theorem permMatrix_congr_apply {σ : Equiv.Perm (Fin n)} (hσ : ∀ a, σ (σ a) = a)
    (A : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) :
    ((permMatrix σ)ᵀ * A * permMatrix σ) a b = A (σ a) (σ b) := by
  classical
  have hinner : ∀ q : Fin n, ((permMatrix σ)ᵀ * A) a q = A (σ a) q := by
    intro q
    rw [Matrix.mul_apply]
    refine (Finset.sum_eq_single (σ a) (fun p _ hp => ?_)
      (fun hcon => absurd (Finset.mem_univ (σ a)) hcon)).trans ?_
    · have hne : a ≠ σ p := by
        intro hcon
        exact hp (by rw [hcon, hσ])
      show (permMatrix σ) p a * A p q = 0
      simp [permMatrix, hne]
    · show (permMatrix σ) (σ a) a * A (σ a) q = A (σ a) q
      simp [permMatrix, hσ a]
  rw [Matrix.mul_apply]
  refine (Finset.sum_eq_single (σ b) (fun q _ hq => ?_)
    (fun hcon => absurd (Finset.mem_univ (σ b)) hcon)).trans ?_
  · have hne : b ≠ σ q := by
      intro hcon
      exact hq (by rw [hcon, hσ])
    show ((permMatrix σ)ᵀ * A) a q * (permMatrix σ) q b = 0
    simp [permMatrix, hne]
  · rw [hinner (σ b)]
    show A (σ a) (σ b) * (permMatrix σ) (σ b) b = A (σ a) (σ b)
    simp [permMatrix, hσ b]

/-- **A leading block below both swapped indices is unchanged.** -/
theorem leadingBlock_swap_low {A : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n} {k : ℕ}
    (hk : k ≤ n) (hki : k ≤ (i : ℕ)) (hkj : k ≤ (j : ℕ)) :
    leadingBlock hk ((permMatrix (Equiv.swap i j))ᵀ * A * permMatrix (Equiv.swap i j))
      = leadingBlock hk A := by
  classical
  ext a b
  have hσ : ∀ c, (Equiv.swap i j) ((Equiv.swap i j) c) = c := Equiv.swap_apply_self i j
  show ((permMatrix (Equiv.swap i j))ᵀ * A * permMatrix (Equiv.swap i j))
    (Fin.castLE hk a) (Fin.castLE hk b) = A (Fin.castLE hk a) (Fin.castLE hk b)
  rw [permMatrix_congr_apply hσ]
  have hfix : ∀ c : Fin k, (Equiv.swap i j) (Fin.castLE hk c) = Fin.castLE hk c := by
    intro c
    have hci : Fin.castLE hk c ≠ i := by
      intro hcon
      have := c.isLt
      have : (i : ℕ) = (c : ℕ) := by rw [← hcon]; rfl
      omega
    have hcj : Fin.castLE hk c ≠ j := by
      intro hcon
      have := c.isLt
      have : (j : ℕ) = (c : ℕ) := by rw [← hcon]; rfl
      omega
    exact Equiv.swap_apply_of_ne_of_ne hci hcj
  rw [hfix a, hfix b]

/-- **A leading block above both swapped indices has unchanged determinant.** -/
theorem det_leadingBlock_swap_high {A : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n} {k : ℕ}
    (hk : k ≤ n) (hik : (i : ℕ) < k) (hjk : (j : ℕ) < k) :
    (leadingBlock hk ((permMatrix (Equiv.swap i j))ᵀ * A * permMatrix (Equiv.swap i j))).det
      = (leadingBlock hk A).det := by
  classical
  have hσ : ∀ c, (Equiv.swap i j) ((Equiv.swap i j) c) = c := Equiv.swap_apply_self i j
  set i' : Fin k := ⟨(i : ℕ), hik⟩ with hi'
  set j' : Fin k := ⟨(j : ℕ), hjk⟩ with hj'
  set e : Equiv.Perm (Fin k) := Equiv.swap i' j' with he
  have hcasti : Fin.castLE hk i' = i := Fin.ext rfl
  have hcastj : Fin.castLE hk j' = j := Fin.ext rfl
  have hcompat : ∀ c : Fin k, Fin.castLE hk (e c) = (Equiv.swap i j) (Fin.castLE hk c) := by
    intro c
    by_cases hci : c = i'
    · rw [hci, he, Equiv.swap_apply_left, hcastj, hcasti, Equiv.swap_apply_left]
    by_cases hcj : c = j'
    · rw [hcj, he, Equiv.swap_apply_right, hcasti, hcastj, Equiv.swap_apply_right]
    · rw [he, Equiv.swap_apply_of_ne_of_ne hci hcj]
      refine (Equiv.swap_apply_of_ne_of_ne ?_ ?_).symm
      · intro hcon
        exact hci (Fin.ext (by simpa using congrArg Fin.val hcon))
      · intro hcon
        exact hcj (Fin.ext (by simpa using congrArg Fin.val hcon))
  have hblock : leadingBlock hk ((permMatrix (Equiv.swap i j))ᵀ * A * permMatrix (Equiv.swap i j))
      = (leadingBlock hk A).submatrix e e := by
    ext a b
    show ((permMatrix (Equiv.swap i j))ᵀ * A * permMatrix (Equiv.swap i j))
      (Fin.castLE hk a) (Fin.castLE hk b) = A (Fin.castLE hk (e a)) (Fin.castLE hk (e b))
    rw [permMatrix_congr_apply hσ, hcompat a, hcompat b]
  rw [hblock, Matrix.det_submatrix_equiv_self]

end GaloisForLFunctions.HTGeometry
