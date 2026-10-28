import GaloisForLFunctions.SignedArithmeticHodgeTheory.EveryFiniteCellSourceHasFiniteDyadicCoordinates

/-!
# The arithmetic action in complete dyadic coordinates

Every actual integer logarithmic translation commutes with the dyadic cell
clock. Its level matrix is triangular and constant along level diagonals.
Prime two acts as the exact unilateral shift on every generator chain.
These are source identities, without an assumed sign or a mixed-term bound.
-/

noncomputable section

open RHTower

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

local notation "CellH" => lp (fun _ : ℕ+ => ℂ) 2
local notation "W" => logCellShift 2

private theorem arithmetic_dyadic_commute {p : ℕ} (hp : 2 ≤ p) (x : CellH) :
    logCellShift p (W x) = W (logCellShift p x) := by
  have h : logCellShift p ∘L W = W ∘L logCellShift p := by
    rw [logCellShift_comp hp (by norm_num), logCellShift_comp (by norm_num) hp,
      Nat.mul_comm p 2]
  exact congrArg (fun T => T x) h

/-- Multiplicative arithmetic translation preserves every dyadic scale action. -/
theorem logCellShift_dyadic_pow {p : ℕ} (hp : 2 ≤ p) (j : ℕ) (x : CellH) :
    logCellShift p ((W ^ j) x) = (W ^ j) (logCellShift p x) := by
  induction j with
  | zero => simp
  | succ j ih =>
    simp only [pow_succ', mul_apply_eq_comp, arithmetic_dyadic_commute hp, ih]

/-- The original arithmetic map has an exact triangular level law on wandering rows. -/
theorem inner_logCellShift_dyadic_levels {p : ℕ} (hp : 2 ≤ p)
    {u : CellH} (hu : u ∈ logCellDyadicWandering) (v : CellH) (j k : ℕ) :
    inner ℂ ((W ^ j) u) (logCellShift p ((W ^ k) v)) =
      if k ≤ j then inner ℂ ((W ^ (j - k)) u) (logCellShift p v) else 0 := by
  rw [logCellShift_dyadic_pow hp]
  by_cases hkj : k ≤ j
  · rw [if_pos hkj]
    have hj : j = k + (j - k) := by omega
    conv_lhs => rw [hj]
    rw [pow_add, mul_apply_eq_comp, inner_logCellDyadic_pow]
  · rw [if_neg hkj]
    obtain ⟨r, hk⟩ := Nat.exists_eq_add_of_lt (show j < k by omega)
    rw [hk, show j + r + 1 = j + (r + 1) by omega, pow_add, mul_apply_eq_comp,
      inner_logCellDyadic_pow, pow_succ', mul_apply_eq_comp]
    exact Submodule.inner_left_of_mem_orthogonal
      (LinearMap.mem_range.mpr ⟨_, rfl⟩) hu

/-- A level-diagonal entry read directly from the original arithmetic source map. -/
def logCellArithmeticLevelEntry (p r : ℕ) (i l : Option ℕ+) : ℂ :=
  inner ℂ ((W ^ r) (logCellDyadicGenerator i)) (logCellShift p (logCellDyadicGenerator l))

/-- The complete matrix is determined by level diagonals indexed by nonnegative integers. -/
theorem logCellArithmetic_level_matrix {p : ℕ} (hp : 2 ≤ p)
    (j k : ℕ) (i l : Option ℕ+) :
    logCellDyadicCoordinates (logCellShift p (logCellDyadicOrbit (k, l))) (j, i) =
      if k ≤ j then logCellArithmeticLevelEntry p (j - k) i l else 0 := by
  rw [logCellDyadicCoordinates_apply]
  exact inner_logCellShift_dyadic_levels hp (logCellDyadicGenerator_mem i)
    (logCellDyadicGenerator l) j k

/-- The first coordinate of every actual dyadically shifted source vanishes. -/
theorem logCellDyadicCoordinates_shift_zero (x : CellH) (i : Option ℕ+) :
    logCellDyadicCoordinates (W x) (0, i) = 0 := by
  rw [logCellDyadicCoordinates_apply]
  change inner ℂ (logCellDyadicGenerator i) (W x) = 0
  exact Submodule.inner_left_of_mem_orthogonal
    (LinearMap.mem_range.mpr ⟨x, rfl⟩) (logCellDyadicGenerator_mem i)

/-- Prime two advances every generator chain by exactly one level. -/
theorem logCellDyadicCoordinates_shift_succ (x : CellH) (j : ℕ) (i : Option ℕ+) :
    logCellDyadicCoordinates (W x) (j + 1, i) = logCellDyadicCoordinates x (j, i) := by
  rw [logCellDyadicCoordinates_apply, logCellDyadicCoordinates_apply,
    logCellDyadicOrbit, logCellDyadicOrbit, pow_succ', mul_apply_eq_comp]
  simpa only [pow_one] using inner_logCellDyadic_pow 1 ((W ^ j) (logCellDyadicGenerator i)) x

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.inner_logCellShift_dyadic_levels
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellArithmetic_level_matrix
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellDyadicCoordinates_shift_zero
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellDyadicCoordinates_shift_succ
