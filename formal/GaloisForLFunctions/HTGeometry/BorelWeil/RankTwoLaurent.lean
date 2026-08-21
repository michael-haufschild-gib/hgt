import GaloisForLFunctions.HTGeometry.BorelWeil.RankTwoChart

/-!
# The Laurent monomials of the flag variety of `GL(2)`

The affine coordinate of the big cell is a unit of the flag localization, so its integer powers are
defined; nonnegative powers are the functions on one cell, nonpositive powers those on the other,
and every function on the intersection is a finite `k`-combination of them.

## Main definitions

* `tUnit`, `tPow`

## Main results

* `tPow_mem_cellSubalg_one`, `tPow_neg_mem_cellSubalg_swap`
* `exists_sum_tPow` — a function on the intersection is a combination of Laurent monomials.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {k : Type*} [Field k] [Infinite k]

/-- The affine coordinate of the big cell, as a unit. -/
noncomputable def tUnit (k : Type*) [Field k] [Infinite k] : (FlagLoc 2 k)ˣ :=
  (fibreCoord (1 : Equiv.Perm (Fin 2)) zero_succ_lt_two)⁻¹

@[simp] theorem coe_tUnit : ((tUnit k : (FlagLoc 2 k)ˣ) : FlagLoc 2 k) = tCoord k := by
  rw [tUnit, tCoord_eq_cellCoord, cellCoord_succ_eq_fibreCoord_inv]

@[simp] theorem coe_tUnit_inv : (((tUnit k)⁻¹ : (FlagLoc 2 k)ˣ) : FlagLoc 2 k) = tInv k := by
  rw [tUnit, inv_inv, tInv]

/-- The integer powers of the affine coordinate. -/
noncomputable def tPow (k : Type*) [Field k] [Infinite k] (n : ℤ) : FlagLoc 2 k :=
  ((tUnit k ^ n : (FlagLoc 2 k)ˣ) : FlagLoc 2 k)

@[simp] theorem tPow_zero : tPow k 0 = 1 := by
  rw [tPow, zpow_zero, Units.val_one]

theorem tPow_add (m n : ℤ) : tPow k (m + n) = tPow k m * tPow k n := by
  rw [tPow, tPow, tPow, zpow_add, Units.val_mul]

theorem tPow_natCast (j : ℕ) : tPow k (j : ℤ) = (tCoord k) ^ j := by
  rw [tPow, zpow_natCast, Units.val_pow_eq_pow_val, coe_tUnit]

theorem tPow_neg_natCast (j : ℕ) : tPow k (-(j : ℤ)) = (tInv k) ^ j := by
  rw [tPow, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, coe_tUnit_inv]

theorem tPow_mem_cellSubalg_one (j : ℕ) : tPow k (j : ℤ) ∈ cellSubalg 2 k {(1 : Equiv.Perm (Fin 2))} := by
  rw [tPow_natCast, cellSubalg_one_eq_adjoin]
  exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) j

theorem tPow_neg_mem_cellSubalg_swap (j : ℕ) :
    tPow k (-(j : ℤ)) ∈ cellSubalg 2 k {swapTwo} := by
  rw [tPow_neg_natCast, cellSubalg_swap_eq_adjoin]
  exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) j

/-- **A function on the intersection is a finite combination of Laurent monomials.** -/
theorem exists_sum_tPow {x : FlagLoc 2 k}
    (hx : x ∈ cellSections 2 k ({1, swapTwo} : Finset (Equiv.Perm (Fin 2))) (fun _ => 0)) :
    ∃ (m n : ℕ) (c : ℕ → k),
      x = ∑ j ∈ Finset.range n, c j • tPow k ((j : ℤ) - (m : ℤ)) := by
  classical
  have hx' : x ∈ cellSections 2 k ({1, swapNext (0 : Fin 2) zero_succ_lt_two} :
      Finset (Equiv.Perm (Fin 2))) (fun _ => 0) := hx
  obtain ⟨m, p, hp⟩ := exists_cellCoordAlg_fibre_denom zero_succ_lt_two hx'
  have hmem : cellCoordAlg (k := k) p ∈ Algebra.adjoin k ({tCoord k} : Set (FlagLoc 2 k)) :=
    cellCoordAlg_mem_adjoin p
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨q, hq⟩ := hmem
  refine ⟨m, q.natDegree + 1, fun j => q.coeff j, ?_⟩
  have hxeq : x = cellCoordAlg (k := k) p * (tInv k) ^ m := by
    have hunit : (tCoord k) ^ m * (tInv k) ^ m = 1 := by
      rw [← mul_pow, ← coe_tUnit, ← coe_tUnit_inv, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, one_pow]
    calc x = x * ((tCoord k) ^ m * (tInv k) ^ m) := by rw [hunit, mul_one]
      _ = (x * (tCoord k) ^ m) * (tInv k) ^ m := by ring
      _ = cellCoordAlg (k := k) p * (tInv k) ^ m := by
          rw [show x * (tCoord k) ^ m
            = x * (cellCoord (⟨(0 : Fin 2).val + 1, zero_succ_lt_two⟩ : Fin 2) (0 : Fin 2)) ^ m from
            rfl, hp]
  rw [hxeq, ← hq]
  show Polynomial.aeval (tCoord k) q * (tInv k) ^ m = _
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_assoc, ← tPow_natCast, ← tPow_neg_natCast, ← tPow_add, ← sub_eq_add_neg]

end GaloisForLFunctions.HTGeometry.BorelWeil
