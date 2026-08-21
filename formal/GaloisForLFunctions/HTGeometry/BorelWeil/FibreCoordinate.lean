import GaloisForLFunctions.HTGeometry.BorelWeil.PairTransition
import GaloisForLFunctions.HTGeometry.BorelWeil.WeylAction

/-!
# The fibre coordinate is a cell coordinate

The exceptional minor of the cell `s_i` is the bordered minor of the identity cell in the direction
of the simple root: the rows `s_i(0), …, s_i(i)` are `0, …, i−1, i+1`.  Hence the coordinate
`cellCoord (i+1) i` of the big cell is the inverse of the fibre coordinate of the pair
`{1, s_i}` — the `ℙ¹` coordinate of the fibre of `G/B → G/P_i` is an affine coordinate of the big
cell.

## Main results

* `borderPoly_succ_eq_minorPolyAt_swapNext`
* `cellCoord_succ_eq_fibreCoord_inv`
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- Truncation of a row-permuted matrix depends only on the rows inside the block. -/
theorem truncate_submatrix_congr {R : Type*} [CommRing R] {j : ℕ} {f f' : Fin N → Fin N}
    (hff : ∀ r : Fin N, (r : ℕ) < j → f r = f' r) (A : Matrix (Fin N) (Fin N) R) :
    truncate j (A.submatrix f id) = truncate j (A.submatrix f' id) := by
  refine Matrix.ext fun r c => ?_
  by_cases h1 : (r : ℕ) < j
  · by_cases h2 : (c : ℕ) < j
    · rw [truncate_apply_of_both h1 h2, truncate_apply_of_both h1 h2, Matrix.submatrix_apply,
        Matrix.submatrix_apply, hff r h1]
    · rw [truncate_apply_of_not_right h2, truncate_apply_of_not_right h2]
  · rw [truncate_apply_of_not_left h1, truncate_apply_of_not_left h1]

/-- **The exceptional minor of the simple reflection cell is a bordered minor.** -/
theorem borderPoly_succ_eq_minorPolyAt_swapNext {i : Fin N} (hi : (i : ℕ) + 1 < N) :
    borderPoly (k := k) (⟨(i : ℕ) + 1, hi⟩ : Fin N) i
      = minorPolyAt N k (swapNext i hi) ((i : ℕ) + 1) := by
  classical
  rw [borderPoly, minorPolyAt]
  congr 1
  refine truncate_submatrix_congr (fun r hr => ?_) _
  by_cases hri : r = i
  · rw [hri, Function.update_self, swapNext, Equiv.swap_apply_left]
  · rw [Function.update_of_ne hri, swapNext, Equiv.swap_apply_of_ne_of_ne hri ?_]
    · rfl
    · intro hc
      have h := congrArg (Fin.val) hc
      simp at h
      omega

/-- **The cell coordinate along a simple root is the inverse fibre coordinate.** -/
theorem cellCoord_succ_eq_fibreCoord_inv {i : Fin N} (hi : (i : ℕ) + 1 < N) :
    cellCoord (k := k) (⟨(i : ℕ) + 1, hi⟩ : Fin N) i
      = (((fibreCoord (1 : Equiv.Perm (Fin N)) hi)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k) := by
  have hone : (1 : Equiv.Perm (Fin N)) * swapNext i hi = swapNext i hi := one_mul _
  rw [cellCoord, borderPoly_succ_eq_minorPolyAt_swapNext hi, fibreCoord, hone, inv_div,
    div_eq_mul_inv, Units.val_mul, coe_minorUnit]

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

theorem weylSubst_coe_minorUnit (w σ : Equiv.Perm (Fin N)) {j : ℕ} (hj : j ≤ N) :
    weylSubst w ((minorUnit (k := k) σ j hj : (FlagLoc N k)ˣ) : FlagLoc N k)
      = ((minorUnit (w⁻¹ * σ) j hj : (FlagLoc N k)ˣ) : FlagLoc N k) := by
  rw [coe_minorUnit, weylSubst_algebraMap, substLeft_minorPolyAt, coe_minorUnit]

theorem weylSubst_minorUnit (w σ : Equiv.Perm (Fin N)) {j : ℕ} (hj : j ≤ N) :
    Units.map (weylSubst (k := k) w).toMonoidHom (minorUnit σ j hj)
      = minorUnit (w⁻¹ * σ) j hj := by
  refine Units.ext ?_
  rw [Units.coe_map]
  exact weylSubst_coe_minorUnit w σ hj

/-- **The Weyl reflection inverts the fibre coordinate.** -/
theorem weylSubst_fibreCoord {i : Fin N} (hi : (i : ℕ) + 1 < N) :
    Units.map (weylSubst (k := k) (swapNext i hi)).toMonoidHom (fibreCoord 1 hi)
      = (fibreCoord (1 : Equiv.Perm (Fin N)) hi)⁻¹ := by
  have hone : (1 : Equiv.Perm (Fin N)) * swapNext i hi = swapNext i hi := one_mul _
  have hinv : (swapNext i hi)⁻¹ = swapNext i hi := by
    rw [swapNext, Equiv.swap_inv]
  have hsq : swapNext i hi * swapNext i hi = (1 : Equiv.Perm (Fin N)) := by
    rw [swapNext, Equiv.swap_mul_self]
  rw [fibreCoord, hone, map_div, weylSubst_minorUnit, weylSubst_minorUnit, hinv, mul_one, hsq,
    inv_div]

theorem weylSubst_cellCoord_succ {i : Fin N} (hi : (i : ℕ) + 1 < N) :
    weylSubst (swapNext i hi) (cellCoord (k := k) (⟨(i : ℕ) + 1, hi⟩ : Fin N) i)
      = ((fibreCoord (1 : Equiv.Perm (Fin N)) hi : (FlagLoc N k)ˣ) : FlagLoc N k) := by
  have h := weylSubst_fibreCoord (k := k) hi
  have hval := congrArg (fun u : (FlagLoc N k)ˣ => ((u⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)) h
  simp only [inv_inv] at hval
  rw [cellCoord_succ_eq_fibreCoord_inv hi, ← hval, ← map_inv, Units.coe_map]
  rfl

end GaloisForLFunctions.HTGeometry.BorelWeil
