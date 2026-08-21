import GaloisForLFunctions.HTGeometry.BorelWeil.WeylAction
import GaloisForLFunctions.HTGeometry.BorelWeil.BottCombinatorics

/-!
# Cells related by a simple reflection

Two Bruhat cells whose indices differ by a simple reflection on the right have flags that differ
only in one step, so all of their leading minors agree up to sign except the one at that step.  The
exceptional pair of minors is the homogeneous coordinate of the `ℙ¹` fibre of `G/B → G/P_i`.

## Main results

* `minorPolyAt_mul_swapNext_of_le` — the minors below the step agree.
* `minorPolyAt_mul_swapNext_of_gt` — the minors above the step agree up to sign.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

theorem submatrix_mul_perm (σ τ : Equiv.Perm (Fin N))
    (A : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) k)) :
    A.submatrix (⇑(σ * τ)) id = (A.submatrix (⇑σ) id).submatrix (⇑τ) id := by
  ext r c
  rfl

theorem swapNext_apply_of_lt {i : Fin N} {hi : (i : ℕ) + 1 < N} {r : Fin N}
    (hr : (r : ℕ) < (i : ℕ)) : (swapNext i hi) r = r := by
  refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
  · intro hc
    rw [hc] at hr
    omega
  · intro hc
    have : (r : ℕ) = (i : ℕ) + 1 := by rw [hc]
    omega

theorem swapNext_maps_lt {i : Fin N} {hi : (i : ℕ) + 1 < N} {j : ℕ} (hj : (i : ℕ) + 1 < j)
    {r : Fin N} (hr : (r : ℕ) < j) : (((swapNext i hi) r : Fin N) : ℕ) < j := by
  classical
  by_cases h1 : r = i
  · rw [h1, swapNext, Equiv.swap_apply_left]
    omega
  · by_cases h2 : r = ⟨(i : ℕ) + 1, hi⟩
    · rw [h2, swapNext, Equiv.swap_apply_right]
      omega
    · rw [swapNext, Equiv.swap_apply_of_ne_of_ne h1 h2]
      exact hr

/-- **Below the step the minors agree.** -/
theorem minorPolyAt_mul_swapNext_of_le (σ : Equiv.Perm (Fin N)) {i : Fin N}
    (hi : (i : ℕ) + 1 < N) {j : ℕ} (hj : j ≤ (i : ℕ)) :
    minorPolyAt N k (σ * swapNext i hi) j = minorPolyAt N k σ j := by
  rw [minorPolyAt, minorPolyAt, submatrix_mul_perm]
  congr 1
  refine Matrix.ext fun r c => ?_
  by_cases h1 : (r : ℕ) < j
  · by_cases h2 : (c : ℕ) < j
    · rw [truncate_apply_of_both h1 h2, truncate_apply_of_both h1 h2, Matrix.submatrix_apply,
        id_eq, swapNext_apply_of_lt (by omega)]
    · rw [truncate_apply_of_not_right h2, truncate_apply_of_not_right h2]
  · rw [truncate_apply_of_not_left h1, truncate_apply_of_not_left h1]

/-- Truncation commutes with a row permutation that preserves the truncation block. -/
theorem truncate_submatrix_perm {R : Type*} [CommRing R] {j : ℕ} (τ : Equiv.Perm (Fin N))
    (hτ : ∀ r : Fin N, ((r : ℕ) < j ↔ ((τ r : Fin N) : ℕ) < j))
    (hτ' : ∀ r : Fin N, j ≤ (r : ℕ) → τ r = r) (A : Matrix (Fin N) (Fin N) R) :
    truncate j (A.submatrix (⇑τ) id) = (truncate j A).submatrix (⇑τ) id := by
  classical
  refine Matrix.ext fun r c => ?_
  rw [Matrix.submatrix_apply, id_eq]
  by_cases h1 : (r : ℕ) < j
  · have h1' : ((τ r : Fin N) : ℕ) < j := (hτ r).mp h1
    by_cases h2 : (c : ℕ) < j
    · rw [truncate_apply_of_both h1 h2, truncate_apply_of_both h1' h2, Matrix.submatrix_apply,
        id_eq]
    · rw [truncate_apply_of_not_right h2, truncate_apply_of_not_right h2,
        if_neg (fun hc => by rw [← hc] at h2; omega), if_neg (fun hc => by rw [← hc] at h2; omega)]
  · have h1' : ¬ (((τ r : Fin N) : ℕ) < j) := fun hcon => h1 ((hτ r).mpr hcon)
    rw [truncate_apply_of_not_left h1, truncate_apply_of_not_left h1', hτ' r (by omega)]

/-- **Above the step the minors agree up to sign.** -/
theorem minorPolyAt_mul_swapNext_of_gt (σ : Equiv.Perm (Fin N)) {i : Fin N}
    (hi : (i : ℕ) + 1 < N) {j : ℕ} (hj : (i : ℕ) + 1 < j) :
    minorPolyAt N k (σ * swapNext i hi) j = - minorPolyAt N k σ j := by
  classical
  have hne : i ≠ ⟨(i : ℕ) + 1, hi⟩ := by
    intro hc
    have h := congrArg (Fin.val) hc
    simp at h
  have hswap : ∀ r : Fin N, r ≠ i → r ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin N) → (swapNext i hi) r = r := by
    intro r hr1 hr2
    rw [swapNext, Equiv.swap_apply_of_ne_of_ne hr1 hr2]
  have hmem : ∀ r : Fin N, ((r : ℕ) < j ↔ (((swapNext i hi) r : Fin N) : ℕ) < j) := by
    intro r
    by_cases hr1 : r = i
    · rw [hr1, swapNext, Equiv.swap_apply_left]
      constructor <;> intro _ <;> omega
    · by_cases hr2 : r = (⟨(i : ℕ) + 1, hi⟩ : Fin N)
      · rw [hr2, swapNext, Equiv.swap_apply_right]
        constructor <;> intro _ <;> omega
      · rw [hswap r hr1 hr2]
  have hfix : ∀ r : Fin N, j ≤ (r : ℕ) → (swapNext i hi) r = r := by
    intro r hr
    refine hswap r ?_ ?_
    · intro hc
      have h := congrArg (Fin.val) hc
      omega
    · intro hc
      have h := congrArg (Fin.val) hc
      simp at h
      omega
  rw [minorPolyAt, minorPolyAt, submatrix_mul_perm,
    truncate_submatrix_perm (swapNext i hi) hmem hfix, Matrix.det_permute, swapNext,
    Equiv.Perm.sign_swap hne]
  simp

end GaloisForLFunctions.HTGeometry.BorelWeil
