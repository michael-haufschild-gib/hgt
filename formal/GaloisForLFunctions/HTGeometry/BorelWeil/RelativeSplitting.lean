import GaloisForLFunctions.HTGeometry.BorelWeil.CellEquationWeight

/-!
# The splitting over a coset pair, relative to further cells

Multiplying by the cell equations of a further set of cells clears their denominators at the cost of
a weight shift, and the shift is nonnegative along the simple root, so it preserves the condition
`⟨λ, α_i^∨⟩ ≥ −1`.  Hence the splitting of the sections over a coset pair holds relative to any
further set of cells — which is the form the Čech assembly needs.

## Main results

* `mul_denomUnit_pow_mem`, `mul_denomUnit_inv_pow_mem` — trading denominators for weight.
* `cellSections_pair_le_sup_relative` — the relative splitting.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

theorem denomOf_union {I J : Finset (Equiv.Perm (Fin N))} (h : Disjoint I J) :
    denomOf N k (I ∪ J) = denomOf N k I * denomOf N k J := by
  classical
  rw [denomOf, denomOf, denomOf, Finset.prod_union h]

theorem pow_mem_flagSemiInv {ν : Fin N → ℤ} {x : FlagLoc N k} (hx : x ∈ flagSemiInv N k ν)
    (m : ℕ) : x ^ m ∈ flagSemiInv N k (fun l => (m : ℤ) * ν l) := by
  induction m with
  | zero =>
      rw [pow_zero]
      refine (flagSemiInv_congr ?_ _).mp one_mem_flagSemiInv_zero
      funext l
      simp
  | succ m ih =>
      rw [pow_succ]
      have h := mul_mem_flagSemiInv ih hx
      refine (flagSemiInv_congr ?_ _).mp h
      funext l
      push_cast
      ring

theorem inv_pow_mem_flagSemiInv {ν : Fin N → ℤ} {u : (FlagLoc N k)ˣ}
    (hu : ((u : (FlagLoc N k)ˣ) : FlagLoc N k) ∈ flagSemiInv N k ν) (m : ℕ) :
    (((u⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)) ^ m
      ∈ flagSemiInv N k (fun l => -((m : ℤ) * ν l)) := by
  have h := pow_mem_flagSemiInv (inv_mem_flagSemiInv hu) m
  refine (flagSemiInv_congr ?_ _).mp h
  funext l
  ring

/-- **Clearing the denominators along a set of cells, at the cost of a weight shift.** -/
theorem mul_denomUnit_pow_mem {J I' : Finset (Equiv.Perm (Fin N))} (hdisj : Disjoint J I')
    {lam : Fin N → ℤ} {x : FlagLoc N k} (hx : x ∈ cellSections N k (J ∪ I') lam) :
    ∃ m : ℕ, x * ((denomUnit N k J : (FlagLoc N k)ˣ) : FlagLoc N k) ^ m
      ∈ cellSections N k I' (fun l => lam l + (m : ℤ) * ((J.card : ℤ) * weightD N l)) := by
  classical
  obtain ⟨hsemi, m, p, hp⟩ := hx
  refine ⟨m, ?_, m, p, ?_⟩
  · rw [coe_denomUnit]
    exact mul_mem_flagSemiInv hsemi
      (pow_mem_flagSemiInv (algebraMap_denomOf_mem_flagSemiInv (k := k) J) m)
  · rw [coe_denomUnit, mul_assoc, ← mul_pow, ← map_mul, ← denomOf_union hdisj]
    exact hp

/-- **Reintroducing the denominators along a set of cells.** -/
theorem mul_denomUnit_inv_pow_mem {J I' : Finset (Equiv.Perm (Fin N))} (hdisj : Disjoint J I')
    {lam : Fin N → ℤ} (m : ℕ) {y : FlagLoc N k}
    (hy : y ∈ cellSections N k I' (fun l => lam l + (m : ℤ) * ((J.card : ℤ) * weightD N l))) :
    y * ((((denomUnit N k J)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)) ^ m
      ∈ cellSections N k (J ∪ I') lam := by
  classical
  obtain ⟨hsemi, n, q, hq⟩ := hy
  refine ⟨?_, max m n, q * (denomOf N k J) ^ (max m n - m) * (denomOf N k I') ^ (max m n - n), ?_⟩
  · have h1 := inv_pow_mem_flagSemiInv (u := denomUnit N k J)
      (by rw [coe_denomUnit]; exact algebraMap_denomOf_mem_flagSemiInv J) m
    have h2 := mul_mem_flagSemiInv hsemi h1
    refine (flagSemiInv_congr ?_ _).mp h2
    funext l
    ring
  · have hM : m + (max m n - m) = max m n := by omega
    have hN : n + (max m n - n) = max m n := by omega
    have hkey : (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k)
          (denomOf N k (J ∪ I'))) ^ (max m n)
        = ((denomUnit N k J : (FlagLoc N k)ˣ) : FlagLoc N k) ^ m
          * (algebraMap _ _ ((denomOf N k J) ^ (max m n - m)))
          * ((algebraMap _ _ (denomOf N k I')) ^ n
            * algebraMap _ _ ((denomOf N k I') ^ (max m n - n))) := by
      rw [denomOf_union hdisj, map_mul, mul_pow, coe_denomUnit, map_pow, map_pow, ← pow_add,
        ← pow_add, hM, hN]
    rw [hkey, map_mul, map_mul, map_pow, map_pow]
    have hcancel : y * ((((denomUnit N k J)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)) ^ m
        * (((denomUnit N k J : (FlagLoc N k)ˣ) : FlagLoc N k) ^ m
          * (algebraMap _ (FlagLoc N k) (denomOf N k J)) ^ (max m n - m)
          * ((algebraMap _ _ (denomOf N k I')) ^ n
            * (algebraMap _ _ (denomOf N k I')) ^ (max m n - n)))
        = (y * (algebraMap _ (FlagLoc N k) (denomOf N k I')) ^ n)
          * ((algebraMap _ _ (denomOf N k J)) ^ (max m n - m)
            * (algebraMap _ _ (denomOf N k I')) ^ (max m n - n))
          * ((((denomUnit N k J)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)
            * ((denomUnit N k J : (FlagLoc N k)ˣ) : FlagLoc N k)) ^ m := by
      rw [mul_pow]
      ring
    rw [hcancel, hq, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_pow, mul_one]
    ring

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- **The relative splitting.**  Relative to any further set of cells, the two cells of a coset pair
span the sections over their intersection as soon as the weight pairs to at least `−1` with the
coroot. -/
theorem cellSections_pair_le_sup_relative {i : Fin N} (hi : (i : ℕ) + 1 < N)
    {J : Finset (Equiv.Perm (Fin N))}
    (hJ : Disjoint J ({1, swapNext i hi} : Finset (Equiv.Perm (Fin N))))
    {lam : Fin N → ℤ} (hd : -1 ≤ lam i - lam (⟨(i : ℕ) + 1, hi⟩ : Fin N)) :
    cellSections N k (J ∪ {1, swapNext i hi}) lam
      ≤ cellSections N k (J ∪ {(1 : Equiv.Perm (Fin N))}) lam
        ⊔ cellSections N k (J ∪ {swapNext i hi}) lam := by
  classical
  have hJ1 : Disjoint J ({(1 : Equiv.Perm (Fin N))} : Finset (Equiv.Perm (Fin N))) :=
    hJ.mono_right (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
  have hJs : Disjoint J ({swapNext i hi} : Finset (Equiv.Perm (Fin N))) :=
    hJ.mono_right (Finset.singleton_subset_iff.mpr
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  intro x hx
  obtain ⟨m, hxm⟩ := mul_denomUnit_pow_mem hJ hx
  have hw := weightD_sub_nonneg (N := N) hi
  have hnn : (0 : ℤ) ≤ (m : ℤ) * ((J.card : ℤ)
      * (weightD N i - weightD N (⟨(i : ℕ) + 1, hi⟩ : Fin N))) :=
    mul_nonneg (Int.natCast_nonneg m) (mul_nonneg (Int.natCast_nonneg _) hw)
  have hd' : -1 ≤ (lam i + (m : ℤ) * ((J.card : ℤ) * weightD N i))
      - (lam (⟨(i : ℕ) + 1, hi⟩ : Fin N)
        + (m : ℤ) * ((J.card : ℤ) * weightD N (⟨(i : ℕ) + 1, hi⟩ : Fin N))) := by
    nlinarith [hd, hnn]
  have hsplit := cellSections_pair_le_sup_general (k := k) hi hd' hxm
  obtain ⟨y1, hy1, ys, hys, hsum⟩ := Submodule.mem_sup.mp hsplit
  have hunit : ((denomUnit N k J : (FlagLoc N k)ˣ) : FlagLoc N k) ^ m
      * ((((denomUnit N k J)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)) ^ m = 1 := by
    rw [← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow]
  have hxeq : x = y1 * ((((denomUnit N k J)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)) ^ m
      + ys * ((((denomUnit N k J)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)) ^ m := by
    calc x = x * (((denomUnit N k J : (FlagLoc N k)ˣ) : FlagLoc N k) ^ m
          * ((((denomUnit N k J)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)) ^ m) := by
          rw [hunit, mul_one]
      _ = (x * ((denomUnit N k J : (FlagLoc N k)ˣ) : FlagLoc N k) ^ m)
          * ((((denomUnit N k J)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)) ^ m := by ring
      _ = (y1 + ys) * ((((denomUnit N k J)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)) ^ m := by
          rw [hsum]
      _ = y1 * ((((denomUnit N k J)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)) ^ m
          + ys * ((((denomUnit N k J)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)) ^ m := by ring
  rw [hxeq]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · exact mul_denomUnit_inv_pow_mem hJ1 m hy1
  · exact mul_denomUnit_inv_pow_mem hJs m hys

end GaloisForLFunctions.HTGeometry.BorelWeil
