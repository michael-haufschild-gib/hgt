import GaloisForLFunctions.HTGeometry.BorelWeil.RankTwoLaurent

/-!
# Splitting a section of the intersection for `GL(2)`

Trivialized on the big cell, a section of `L_λ` over the intersection of the two cells is a Laurent
polynomial in the affine coordinate, the sections over one cell are the nonnegative powers, and the
sections over the other are the powers at most `d = λ_0 − λ_1` — because the two trivializations
differ by the `d`-th power of the coordinate.  So the two subspaces span the intersection exactly
when `d ≥ −1`.

## Main results

* `tPow_mul_cellTriv_mem` — where each Laurent monomial lives.
* `cellSections_pair_le_sup` — the splitting, for `d ≥ −1`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {k : Type*} [Field k] [Infinite k]

theorem charUnits_neg_one :
    charUnits (N := 2) (-1 : kˣ) = (-1 : (FlagLoc 2 k)ˣ) := by
  refine Units.ext ?_
  rw [coe_charUnits, Units.val_neg, Units.val_one, Units.val_neg, Units.val_one, map_neg, map_one]

/-- **The two trivializations differ by the `d`-th power of the coordinate.** -/
theorem tPow_mul_cellTriv (lam : Fin 2 → ℤ) :
    ∃ c : k, c ≠ 0 ∧
      tPow k (lam 0 - lam 1) * ((cellTriv (1 : Equiv.Perm (Fin 2)) lam : (FlagLoc 2 k)ˣ) :
          FlagLoc 2 k)
        = c • ((cellTriv swapTwo lam : (FlagLoc 2 k)ˣ) : FlagLoc 2 k) := by
  have hone : (1 : Equiv.Perm (Fin 2)) * swapNext (0 : Fin 2) zero_succ_lt_two = swapTwo :=
    one_mul _
  have hidx : (⟨(0 : Fin 2).val + 1, zero_succ_lt_two⟩ : Fin 2) = (1 : Fin 2) := rfl
  have htrans := cellTriv_div_cellTriv_swapNext (k := k) (1 : Equiv.Perm (Fin 2))
    zero_succ_lt_two lam
  rw [hone, hidx] at htrans
  have hfib : fibreCoord (1 : Equiv.Perm (Fin 2)) zero_succ_lt_two = (tUnit k)⁻¹ := by
    rw [tUnit, inv_inv]
  rw [hfib] at htrans
  have heq : cellTriv (1 : Equiv.Perm (Fin 2)) lam
      = ((tUnit k)⁻¹ ^ (lam 0 - lam 1) * (-1 : (FlagLoc 2 k)ˣ) ^ (lam 1))
        * cellTriv swapTwo lam := div_eq_iff_eq_mul.mp htrans
  have hunits : tUnit k ^ (lam 0 - lam 1) * cellTriv (1 : Equiv.Perm (Fin 2)) lam
      = ((-1 : (FlagLoc 2 k)ˣ) ^ (lam 1)) * cellTriv swapTwo lam := by
    rw [heq, inv_zpow, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  refine ⟨(((-1 : kˣ) ^ (lam 1) : kˣ) : k), Units.ne_zero _, ?_⟩
  have hval := congrArg (fun u : (FlagLoc 2 k)ˣ => (u : FlagLoc 2 k)) hunits
  simp only [Units.val_mul] at hval
  rw [tPow, hval, Algebra.smul_def]
  congr 1
  rw [← charUnits_neg_one, ← map_zpow]
  rfl

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {k : Type*} [Field k] [Infinite k]

theorem tPow_mul_cellTriv_mem_one {lam : Fin 2 → ℤ} {n : ℤ} (hn : 0 ≤ n) :
    tPow k n * ((cellTriv (1 : Equiv.Perm (Fin 2)) lam : (FlagLoc 2 k)ˣ) : FlagLoc 2 k)
      ∈ cellSections 2 k {(1 : Equiv.Perm (Fin 2))} lam := by
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  exact (mem_cellSections_mul_cellTriv (Finset.mem_singleton_self _) lam).mpr
    (tPow_mem_cellSubalg_one j)

theorem tPow_mul_cellTriv_mem_swap {lam : Fin 2 → ℤ} {n : ℤ} (hn : n ≤ lam 0 - lam 1) :
    tPow k n * ((cellTriv (1 : Equiv.Perm (Fin 2)) lam : (FlagLoc 2 k)ˣ) : FlagLoc 2 k)
      ∈ cellSections 2 k {swapTwo} lam := by
  obtain ⟨c, hc, hceq⟩ := tPow_mul_cellTriv (k := k) lam
  have h1 : tPow k n * ((cellTriv (1 : Equiv.Perm (Fin 2)) lam : (FlagLoc 2 k)ˣ) : FlagLoc 2 k)
      = c • (tPow k (n - (lam 0 - lam 1))
        * ((cellTriv swapTwo lam : (FlagLoc 2 k)ˣ) : FlagLoc 2 k)) := by
    calc tPow k n * ((cellTriv (1 : Equiv.Perm (Fin 2)) lam : (FlagLoc 2 k)ˣ) : FlagLoc 2 k)
        = tPow k (n - (lam 0 - lam 1)) * (tPow k (lam 0 - lam 1)
            * ((cellTriv (1 : Equiv.Perm (Fin 2)) lam : (FlagLoc 2 k)ˣ) : FlagLoc 2 k)) := by
          rw [← mul_assoc, ← tPow_add]
          congr 2
          ring
      _ = tPow k (n - (lam 0 - lam 1)) * (c • ((cellTriv swapTwo lam : (FlagLoc 2 k)ˣ) :
            FlagLoc 2 k)) := by rw [hceq]
      _ = c • (tPow k (n - (lam 0 - lam 1))
            * ((cellTriv swapTwo lam : (FlagLoc 2 k)ˣ) : FlagLoc 2 k)) := by rw [mul_smul_comm]
  rw [h1]
  refine Submodule.smul_mem _ c ?_
  refine (mem_cellSections_mul_cellTriv (Finset.mem_singleton_self _) lam).mpr ?_
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ (lam 0 - lam 1) - n)
  have hneg : n - (lam 0 - lam 1) = -(j : ℤ) := by omega
  rw [hneg]
  exact tPow_neg_mem_cellSubalg_swap j

/-- **The two cells span the intersection when the weight pairs to at least `-1` with the
coroot.**  This is the vanishing of the rank-one first cohomology. -/
theorem cellSections_pair_le_sup {lam : Fin 2 → ℤ} (hd : -1 ≤ lam 0 - lam 1) :
    cellSections 2 k ({1, swapTwo} : Finset (Equiv.Perm (Fin 2))) lam
      ≤ cellSections 2 k {(1 : Equiv.Perm (Fin 2))} lam ⊔ cellSections 2 k {swapTwo} lam := by
  classical
  intro x hx
  have hxy : (x * (((cellTriv (1 : Equiv.Perm (Fin 2)) lam)⁻¹ : (FlagLoc 2 k)ˣ) : FlagLoc 2 k))
      * ((cellTriv (1 : Equiv.Perm (Fin 2)) lam : (FlagLoc 2 k)ˣ) : FlagLoc 2 k) = x := by
    rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hy0 : (x * (((cellTriv (1 : Equiv.Perm (Fin 2)) lam)⁻¹ : (FlagLoc 2 k)ˣ) : FlagLoc 2 k))
      ∈ cellSections 2 k ({1, swapTwo} : Finset (Equiv.Perm (Fin 2))) (fun _ => 0) := by
    refine (mem_cellSections_mul_cellTriv
      (Finset.mem_insert_self (1 : Equiv.Perm (Fin 2)) {swapTwo}) lam).mp ?_
    rw [hxy]
    exact hx
  obtain ⟨m, n, c, hsum⟩ := exists_sum_tPow hy0
  rw [← hxy, hsum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [smul_mul_assoc]
  refine Submodule.smul_mem _ _ ?_
  rcases le_or_gt 0 ((j : ℤ) - (m : ℤ)) with h | h
  · exact Submodule.mem_sup_left (tPow_mul_cellTriv_mem_one h)
  · exact Submodule.mem_sup_right (tPow_mul_cellTriv_mem_swap (by omega))

end GaloisForLFunctions.HTGeometry.BorelWeil
