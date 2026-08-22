import GaloisForLFunctions.HTGeometry.HypercubeSingleTransverseBlocks

/-!
# A transverse coupling in an arbitrary direction

Relabelling the qubits carries a transverse flip in direction `i` to a flip in direction `0`, so the
block decomposition and the characteristic polynomial of the single-direction Hamiltonian follow
from the direction-zero case with no new computation.

## Main results

* `singleDirectionHam` — arbitrary diagonal energies plus one transverse flip in direction `i`.
* `cubeRelabel` — the coordinate relabelling of the hypercube.
* `reindex_singleDirectionHam` — relabelling moves the direction.
* `charpoly_singleDirectionHam` — the characteristic polynomial as a product of block quadratics.
-/

open Polynomial Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Arbitrary diagonal energies plus a single transverse flip in direction `i`. -/
def singleDirectionHam (d : (Fin n → Bool) → R) (u : R) (i : Fin n) :
    Matrix (Fin n → Bool) (Fin n → Bool) R :=
  fun x y => if x = y then d x else if y = boolToggle x i then u else 0

theorem singleDirectionHam_zero (d : (Fin (n + 1) → Bool) → R) (u : R) :
    singleDirectionHam d u 0 = singleTransverseHam d u := rfl

/-- Relabelling the coordinates of the hypercube. -/
def cubeRelabel (τ : Equiv.Perm (Fin n)) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun x := x ∘ τ
  invFun x := x ∘ τ.symm
  left_inv x := by
    funext j
    simp
  right_inv x := by
    funext j
    simp

@[simp] theorem cubeRelabel_apply (τ : Equiv.Perm (Fin n)) (x : Fin n → Bool) :
    cubeRelabel τ x = x ∘ τ := rfl

@[simp] theorem cubeRelabel_symm_apply (τ : Equiv.Perm (Fin n)) (x : Fin n → Bool) :
    (cubeRelabel τ).symm x = x ∘ τ.symm := rfl

theorem boolToggle_comp (τ : Equiv.Perm (Fin n)) (x : Fin n → Bool) (j : Fin n) :
    boolToggle (x ∘ τ) j = (boolToggle x (τ j)) ∘ τ := by
  funext k
  by_cases hk : k = j
  · subst hk
    simp [boolToggle, Function.update_self]
  · have hτ : τ k ≠ τ j := fun h => hk (τ.injective h)
    simp [boolToggle, Function.update_of_ne hk, Function.update_of_ne hτ]

/-- **Relabelling moves the transverse direction.** -/
theorem reindex_singleDirectionHam (d : (Fin n → Bool) → R) (u : R) (i : Fin n)
    (τ : Equiv.Perm (Fin n)) :
    Matrix.reindex (cubeRelabel τ) (cubeRelabel τ) (singleDirectionHam d u i)
      = singleDirectionHam (d ∘ (cubeRelabel τ).symm) u (τ.symm i) := by
  ext x y
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  show (if (x ∘ τ.symm) = (y ∘ τ.symm) then d (x ∘ τ.symm)
      else if (y ∘ τ.symm) = boolToggle (x ∘ τ.symm) i then u else 0)
    = if x = y then d (x ∘ τ.symm)
      else if y = boolToggle x (τ.symm i) then u else 0
  have hxy : (x ∘ τ.symm = y ∘ τ.symm) ↔ x = y := by
    constructor
    · intro h
      funext k
      have := congrFun h (τ k)
      simpa using this
    · intro h
      rw [h]
  have htoggle : (y ∘ τ.symm = boolToggle (x ∘ τ.symm) i) ↔ y = boolToggle x (τ.symm i) := by
    rw [boolToggle_comp τ.symm x i]
    constructor
    · intro h
      funext k
      have := congrFun h (τ k)
      simpa using this
    · intro h
      rw [h]
  by_cases h1 : x = y
  · rw [if_pos (hxy.mpr h1), if_pos h1]
  · rw [if_neg (fun h => h1 (hxy.mp h)), if_neg h1]
    by_cases h2 : y = boolToggle x (τ.symm i)
    · rw [if_pos (htoggle.mpr h2), if_pos h2]
    · rw [if_neg (fun h => h2 (htoggle.mp h)), if_neg h2]

/-- **The characteristic polynomial of a single-direction Hamiltonian.** -/
theorem charpoly_singleDirectionHam [Nontrivial R] [DecidableEq R]
    {m : ℕ} (d : (Fin (m + 1) → Bool) → R) (u : R) (i : Fin (m + 1)) :
    (singleDirectionHam d u i).charpoly
      = ∏ z : Fin m → Bool,
          (X ^ 2 -
            C (d ((cubeRelabel (Equiv.swap 0 i)).symm (Fin.cons false z))
              + d ((cubeRelabel (Equiv.swap 0 i)).symm (Fin.cons true z))) * X
            + C (d ((cubeRelabel (Equiv.swap 0 i)).symm (Fin.cons false z))
              * d ((cubeRelabel (Equiv.swap 0 i)).symm (Fin.cons true z)) - u * u)) := by
  classical
  set τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 i with hτ
  have hτi : τ.symm i = 0 := by
    rw [hτ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hre := Matrix.charpoly_reindex (cubeRelabel τ) (singleDirectionHam d u i)
  rw [reindex_singleDirectionHam d u i τ, hτi, singleDirectionHam_zero] at hre
  rw [← hre, charpoly_singleTransverseHam]
  rfl

end GaloisForLFunctions.HTGeometry
