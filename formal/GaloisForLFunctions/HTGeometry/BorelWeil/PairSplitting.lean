import GaloisForLFunctions.HTGeometry.BorelWeil.FibrePowers

/-!
# Splitting the sections over a coset pair

Local triviality lets a chart function divided by a power of the fibre coordinate be split into a
chart function and a multiple of the `d`-th fibre power of a function on the reflected cell, as soon
as `d ≥ −1`.  Trivializing `L_λ` on the first cell, this says that the sections over the
intersection of the two cells of a coset pair are the sum of the sections over the two cells: the
first cohomology of the fibre vanishes.

## Main results

* `exists_split_of_fibrePow` — the splitting for chart functions with a pole.
* `cellSections_pair_le_sup_general` — the splitting of the sections.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

theorem fibrePow_mem_swap_of_nonpos (i : Fin N) (hi : (i : ℕ) + 1 < N) {n : ℤ} (hn : n ≤ 0) :
    fibrePow (k := k) i hi n ∈ cellSubalg N k {swapNext i hi} := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, n = -(j : ℤ) := ⟨n.natAbs, by omega⟩
  rw [hj]
  exact fibrePow_neg_mem_swap i hi j

theorem fibrePow_mem_one_of_nonneg (i : Fin N) (hi : (i : ℕ) + 1 < N) {n : ℤ} (hn : 0 ≤ n) :
    fibrePow (k := k) i hi n ∈ cellSubalg N k {(1 : Equiv.Perm (Fin N))} := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, n = (j : ℤ) := ⟨n.toNat, by omega⟩
  rw [hj]
  exact fibrePow_mem_one i hi j

/-- **Splitting a chart function with a pole along the fibre coordinate.** -/
theorem exists_split_of_fibrePow {i : Fin N} (hi : (i : ℕ) + 1 < N) {d : ℤ} (hd : -1 ≤ d) :
    ∀ (m : ℕ) (a : FlagLoc N k), a ∈ cellSubalg N k {(1 : Equiv.Perm (Fin N))} →
      ∃ u ∈ cellSubalg N k {(1 : Equiv.Perm (Fin N))},
        ∃ v ∈ cellSubalg N k {swapNext i hi},
          a * fibrePow i hi (-(m : ℤ)) = u + fibrePow i hi d * v := by
  intro m
  induction m with
  | zero =>
      intro a ha
      refine ⟨a, ha, 0, Subalgebra.zero_mem _, ?_⟩
      rw [Nat.cast_zero, neg_zero, fibrePow_zero, mul_one, mul_zero, add_zero]
  | succ m ih =>
      intro a ha
      obtain ⟨a', ha', b, hb1, hbs, heq⟩ := exists_fibre_decomposition hi ha
      obtain ⟨u, hu, v, hv, hsplit⟩ := ih a' ha'
      have hunit : ((fibreUnit (k := k) i hi : (FlagLoc N k)ˣ) : FlagLoc N k)
          = fibrePow i hi 1 := by
        rw [fibrePow, zpow_one]
      have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      have hp1 : fibrePow (k := k) i hi 1 * fibrePow i hi (-((m : ℤ) + 1))
          = fibrePow i hi (-(m : ℤ)) := by
        rw [← fibrePow_add]
        congr 1
        omega
      have hp2 : fibrePow (k := k) i hi d * fibrePow i hi (-((m : ℤ) + 1) - d)
          = fibrePow i hi (-((m : ℤ) + 1)) := by
        rw [← fibrePow_add]
        congr 1
        omega
      refine ⟨u, hu, v + b * fibrePow i hi (-((m : ℤ) + 1) - d), ?_, ?_⟩
      · refine Subalgebra.add_mem _ hv (Subalgebra.mul_mem _ hbs ?_)
        exact fibrePow_mem_swap_of_nonpos i hi (by omega)
      · rw [hcast, heq, ← coe_fibreUnit i hi, hunit]
        calc (fibrePow (k := k) i hi 1 * a' + b) * fibrePow i hi (-((m : ℤ) + 1))
            = a' * (fibrePow i hi 1 * fibrePow i hi (-((m : ℤ) + 1)))
              + b * fibrePow i hi (-((m : ℤ) + 1)) := by ring
          _ = a' * fibrePow i hi (-(m : ℤ)) + b * fibrePow i hi (-((m : ℤ) + 1)) := by rw [hp1]
          _ = (u + fibrePow i hi d * v) + b * fibrePow i hi (-((m : ℤ) + 1)) := by rw [hsplit]
          _ = u + fibrePow i hi d * (v + b * fibrePow i hi (-((m : ℤ) + 1) - d)) := by
              rw [mul_add]
              have hbd : fibrePow (k := k) i hi d * (b * fibrePow i hi (-((m : ℤ) + 1) - d))
                  = b * fibrePow i hi (-((m : ℤ) + 1)) := by
                rw [← mul_assoc, mul_comm (fibrePow (k := k) i hi d) b, mul_assoc, hp2]
              rw [hbd]
              ring

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- **The two cells of a coset pair span the sections over their intersection**, as soon as the
weight pairs to at least `−1` with the coroot: the first cohomology of the fibre vanishes. -/
theorem cellSections_pair_le_sup_general {i : Fin N} (hi : (i : ℕ) + 1 < N) {lam : Fin N → ℤ}
    (hd : -1 ≤ lam i - lam (⟨(i : ℕ) + 1, hi⟩ : Fin N)) :
    cellSections N k ({1, swapNext i hi} : Finset (Equiv.Perm (Fin N))) lam
      ≤ cellSections N k {(1 : Equiv.Perm (Fin N))} lam
        ⊔ cellSections N k {swapNext i hi} lam := by
  classical
  intro x hx
  have hxy : (x * (((cellTriv (1 : Equiv.Perm (Fin N)) lam)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k))
      * ((cellTriv (1 : Equiv.Perm (Fin N)) lam : (FlagLoc N k)ˣ) : FlagLoc N k) = x := by
    rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hy0 : (x * (((cellTriv (1 : Equiv.Perm (Fin N)) lam)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k))
      ∈ cellSections N k ({1, swapNext i hi} : Finset (Equiv.Perm (Fin N))) (fun _ => 0) := by
    refine (mem_cellSections_mul_cellTriv
      (Finset.mem_insert_self (1 : Equiv.Perm (Fin N)) {swapNext i hi}) lam).mp ?_
    rw [hxy]
    exact hx
  obtain ⟨m, p, hp⟩ := exists_cellCoordAlg_fibre_denom hi hy0
  have hy : (x * (((cellTriv (1 : Equiv.Perm (Fin N)) lam)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k))
      = cellCoordAlg p * fibrePow i hi (-(m : ℤ)) := by
    have hpow : fibrePow (k := k) i hi (m : ℤ) * fibrePow i hi (-(m : ℤ)) = 1 := by
      rw [← fibrePow_add, add_neg_cancel, fibrePow_zero]
    calc (x * (((cellTriv (1 : Equiv.Perm (Fin N)) lam)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k))
        = (x * (((cellTriv (1 : Equiv.Perm (Fin N)) lam)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k))
            * (fibrePow i hi (m : ℤ) * fibrePow i hi (-(m : ℤ))) := by rw [hpow, mul_one]
      _ = ((x * (((cellTriv (1 : Equiv.Perm (Fin N)) lam)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k))
            * (cellCoord (⟨(i : ℕ) + 1, hi⟩ : Fin N) i) ^ m) * fibrePow i hi (-(m : ℤ)) := by
          rw [fibrePow_natCast]
          ring
      _ = cellCoordAlg p * fibrePow i hi (-(m : ℤ)) := by rw [hp]
  obtain ⟨u, hu, v, hv, hsplit⟩ := exists_split_of_fibrePow (k := k) hi hd m (cellCoordAlg p)
    (cellCoordAlg_mem_cellSections p)
  obtain ⟨c, hc, hceq⟩ := fibrePow_mul_cellTriv (k := k) i hi lam
  have hxeq : x = u * ((cellTriv (1 : Equiv.Perm (Fin N)) lam : (FlagLoc N k)ˣ) : FlagLoc N k)
      + c • (v * ((cellTriv (swapNext i hi) lam : (FlagLoc N k)ˣ) : FlagLoc N k)) := by
    calc x = (x * (((cellTriv (1 : Equiv.Perm (Fin N)) lam)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k))
          * ((cellTriv (1 : Equiv.Perm (Fin N)) lam : (FlagLoc N k)ˣ) : FlagLoc N k) := hxy.symm
      _ = (u + fibrePow i hi (lam i - lam (⟨(i : ℕ) + 1, hi⟩ : Fin N)) * v)
          * ((cellTriv (1 : Equiv.Perm (Fin N)) lam : (FlagLoc N k)ˣ) : FlagLoc N k) := by
          rw [hy, hsplit]
      _ = u * ((cellTriv (1 : Equiv.Perm (Fin N)) lam : (FlagLoc N k)ˣ) : FlagLoc N k)
          + (fibrePow i hi (lam i - lam (⟨(i : ℕ) + 1, hi⟩ : Fin N))
            * ((cellTriv (1 : Equiv.Perm (Fin N)) lam : (FlagLoc N k)ˣ) : FlagLoc N k)) * v := by
          ring
      _ = u * ((cellTriv (1 : Equiv.Perm (Fin N)) lam : (FlagLoc N k)ˣ) : FlagLoc N k)
          + c • (v * ((cellTriv (swapNext i hi) lam : (FlagLoc N k)ˣ) : FlagLoc N k)) := by
          rw [hceq, smul_mul_assoc, mul_comm v]
  rw [hxeq]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_)
    (Submodule.mem_sup_right (Submodule.smul_mem _ c ?_))
  · exact (mem_cellSections_mul_cellTriv (Finset.mem_singleton_self _) lam).mpr hu
  · exact (mem_cellSections_mul_cellTriv (Finset.mem_singleton_self _) lam).mpr hv

end GaloisForLFunctions.HTGeometry.BorelWeil
