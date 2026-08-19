import GaloisForLFunctions.HTGeometry.SiegelIntegralMinor

/-!
# One descent step

With the Lovász threshold written as `3/4`, terminality of the descent is exactly a Siegel bound
with parameter `2`, and a swap at a failing index contracts the potential by that same factor.

Only the single leading minor that separates the two swapped indices changes, and it changes by the
ratio of the new to the old Jacobi entry, which is what the failing condition bounds.

* `det_leadingBlock_succ` : consecutive leading minors differ by one diagonal entry.
* `isSiegel_two_of_terminal` : **terminality is a Siegel bound.**
* `potentialOf_swap_lt` : **a swap at a failing index contracts the potential by `3/4`.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- Consecutive leading minors differ by one diagonal entry. -/
theorem det_leadingBlock_succ (J : JacobiData n) {k : ℕ} (hk : k + 1 ≤ n) :
    (leadingBlock hk J.form).det
      = (leadingBlock (Nat.le_of_succ_le hk) J.form).det * J.d ⟨k, hk⟩ := by
  rw [det_leadingBlock_form hk J, det_leadingBlock_form (Nat.le_of_succ_le hk) J,
    Fin.prod_univ_castSucc]
  congr 1

/-- **Terminality of the descent is a Siegel bound with parameter `2`.** -/
theorem isSiegel_two_of_terminal (J : JacobiData n)
    (hred : ∀ a b : Fin n, a < b → |J.U a b| ≤ 1 / 2)
    (hterm : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 →
      3 / 4 * J.d i ≤ J.projNorm i (Pi.single j (1 : ℝ))) :
    J.IsSiegel 2 1 := by
  refine ⟨fun i j hij => ?_, fun i j => J.entries_le_one hred i j⟩
  have hjs : (j : ℕ) = (i : ℕ) + 1 := hij.symm
  have hstep := hterm i j hjs
  rw [J.projNorm_succ hjs] at hstep
  have hb : (J.U i j) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    have := hred i j (Fin.lt_def.2 (by omega))
    nlinarith [abs_nonneg (J.U i j), sq_abs (J.U i j)]
  nlinarith [hstep, hb, J.pos i]

/-- **A swap at a failing index contracts the potential.** -/
theorem potentialOf_swap_lt {J J' : JacobiData n} {i j : Fin n} (hij : i ≠ j) (hji : i ≤ j)
    (hjs : (j : ℕ) = (i : ℕ) + 1)
    (hform : J'.form
      = (permMatrix (Equiv.swap i j))ᵀ * J.form * permMatrix (Equiv.swap i j))
    (hfail : J.projNorm i (Pi.single j (1 : ℝ)) < 3 / 4 * J.d i) :
    potentialOf J'.form < 3 / 4 * potentialOf J.form := by
  classical
  set K : Fin (n + 1) := ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩ with hK
  have hKle : (i : ℕ) + 1 ≤ n := by have := j.isLt; omega
  have hile : (i : ℕ) ≤ n := Nat.le_of_succ_le hKle
  -- the other minors are unchanged
  have hother : ∀ k : Fin (n + 1), k ≠ K →
      (leadingBlock (Fin.is_le k) J'.form).det = (leadingBlock (Fin.is_le k) J.form).det := by
    intro k hk
    have hkne : (k : ℕ) ≠ (i : ℕ) + 1 := fun hc => hk (Fin.ext hc)
    rcases lt_or_ge (k : ℕ) ((i : ℕ) + 1) with hlow | hhigh
    · rw [hform, leadingBlock_swap_low (Fin.is_le k) (by omega) (by omega)]
    · rw [hform]
      exact det_leadingBlock_swap_high (Fin.is_le k) (by omega) (by omega)
  -- the separating minor contracts
  have hd' : J'.d i = J.projNorm i (Pi.single j (1 : ℝ)) := swap_d_eq_projNorm hij hji hform
  have hbase : (leadingBlock hile J'.form).det = (leadingBlock hile J.form).det := by
    rw [hform, leadingBlock_swap_low hile (by omega) (by omega)]
  have hii : (⟨(i : ℕ), by have := i.isLt; omega⟩ : Fin n) = i := Fin.ext rfl
  have hKsucc : ∀ M : JacobiData n, (leadingBlock (Fin.is_le K) M.form).det
      = (leadingBlock hile M.form).det * M.d i := by
    intro M
    have := det_leadingBlock_succ M hKle
    rw [hii] at this
    exact this
  have hbasepos : 0 < (leadingBlock hile J.form).det := by
    rw [det_leadingBlock_form hile J]
    exact Finset.prod_pos fun m _ => J.pos _
  have hKlt : (leadingBlock (Fin.is_le K) J'.form).det
      < 3 / 4 * (leadingBlock (Fin.is_le K) J.form).det := by
    rw [hKsucc J', hKsucc J, hbase, hd']
    calc (leadingBlock hile J.form).det * J.projNorm i (Pi.single j (1 : ℝ))
        < (leadingBlock hile J.form).det * (3 / 4 * J.d i) :=
          mul_lt_mul_of_pos_left hfail hbasepos
      _ = 3 / 4 * ((leadingBlock hile J.form).det * J.d i) := by ring
  -- assemble the products
  have hprodpos : 0 < ∏ k ∈ Finset.univ.erase K, (leadingBlock (Fin.is_le k) J.form).det := by
    refine Finset.prod_pos fun k _ => ?_
    rw [det_leadingBlock_form (Fin.is_le k) J]
    exact Finset.prod_pos fun m _ => J.pos _
  rw [potentialOf, potentialOf, ← Finset.mul_prod_erase _ _ (Finset.mem_univ K),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ K)]
  have heq : (∏ k ∈ Finset.univ.erase K, (leadingBlock (Fin.is_le k) J'.form).det)
      = ∏ k ∈ Finset.univ.erase K, (leadingBlock (Fin.is_le k) J.form).det :=
    Finset.prod_congr rfl fun k hk => hother k (Finset.ne_of_mem_erase hk)
  rw [heq]
  calc (leadingBlock (Fin.is_le K) J'.form).det
        * ∏ k ∈ Finset.univ.erase K, (leadingBlock (Fin.is_le k) J.form).det
      < (3 / 4 * (leadingBlock (Fin.is_le K) J.form).det)
        * ∏ k ∈ Finset.univ.erase K, (leadingBlock (Fin.is_le k) J.form).det :=
        mul_lt_mul_of_pos_right hKlt hprodpos
    _ = 3 / 4 * ((leadingBlock (Fin.is_le K) J.form).det
        * ∏ k ∈ Finset.univ.erase K, (leadingBlock (Fin.is_le k) J.form).det) := by ring

end GaloisForLFunctions.HTGeometry
