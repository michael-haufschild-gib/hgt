import GaloisForLFunctions.HTGeometry.BorelWeil.LocalTriviality

/-!
# Integer powers of the fibre coordinate

The fibre coordinate of a coset pair is a unit of the flag localization, so its integer powers are
defined; the nonnegative ones are regular on the first cell, the nonpositive ones on the second, and
the two cell trivializations of `L_λ` differ by the power `⟨λ, α_i^∨⟩` up to a scalar.

## Main definitions

* `fibreUnit`, `fibrePow`

## Main results

* `fibrePow_mem_one`, `fibrePow_neg_mem_swap`
* `fibrePow_mul_cellTriv` — the transition, as a scalar multiple.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- The fibre coordinate of a coset pair, as a unit. -/
noncomputable def fibreUnit (i : Fin N) (hi : (i : ℕ) + 1 < N) : (FlagLoc N k)ˣ :=
  (fibreCoord (1 : Equiv.Perm (Fin N)) hi)⁻¹

@[simp] theorem coe_fibreUnit (i : Fin N) (hi : (i : ℕ) + 1 < N) :
    ((fibreUnit (k := k) i hi : (FlagLoc N k)ˣ) : FlagLoc N k)
      = cellCoord (⟨(i : ℕ) + 1, hi⟩ : Fin N) i :=
  (cellCoord_succ_eq_fibreCoord_inv hi).symm

theorem coe_fibreUnit_inv (i : Fin N) (hi : (i : ℕ) + 1 < N) :
    (((fibreUnit (k := k) i hi)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)
      = weylSubst (swapNext i hi) (cellCoord (⟨(i : ℕ) + 1, hi⟩ : Fin N) i) := by
  rw [fibreUnit, inv_inv, weylSubst_cellCoord_succ]

/-- The integer powers of the fibre coordinate. -/
noncomputable def fibrePow (i : Fin N) (hi : (i : ℕ) + 1 < N) (n : ℤ) : FlagLoc N k :=
  ((fibreUnit i hi ^ n : (FlagLoc N k)ˣ) : FlagLoc N k)

@[simp] theorem fibrePow_zero (i : Fin N) (hi : (i : ℕ) + 1 < N) :
    fibrePow (k := k) i hi 0 = 1 := by
  rw [fibrePow, zpow_zero, Units.val_one]

theorem fibrePow_add (i : Fin N) (hi : (i : ℕ) + 1 < N) (m n : ℤ) :
    fibrePow (k := k) i hi (m + n) = fibrePow i hi m * fibrePow i hi n := by
  rw [fibrePow, fibrePow, fibrePow, zpow_add, Units.val_mul]

theorem fibrePow_natCast (i : Fin N) (hi : (i : ℕ) + 1 < N) (j : ℕ) :
    fibrePow (k := k) i hi (j : ℤ) = (cellCoord (⟨(i : ℕ) + 1, hi⟩ : Fin N) i) ^ j := by
  rw [fibrePow, zpow_natCast, Units.val_pow_eq_pow_val, coe_fibreUnit]

theorem fibrePow_neg_natCast (i : Fin N) (hi : (i : ℕ) + 1 < N) (j : ℕ) :
    fibrePow (k := k) i hi (-(j : ℤ))
      = (weylSubst (swapNext i hi) (cellCoord (⟨(i : ℕ) + 1, hi⟩ : Fin N) i)) ^ j := by
  rw [fibrePow, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, coe_fibreUnit_inv]

theorem fibrePow_mem_one (i : Fin N) (hi : (i : ℕ) + 1 < N) (j : ℕ) :
    fibrePow (k := k) i hi (j : ℤ) ∈ cellSubalg N k {(1 : Equiv.Perm (Fin N))} := by
  rw [fibrePow_natCast]
  exact Subalgebra.pow_mem _ (cellCoord_mem_cellSections _ _) j

theorem cellCoord_succ_weyl_mem_swap (i : Fin N) (hi : (i : ℕ) + 1 < N) :
    weylSubst (swapNext i hi) (cellCoord (k := k) (⟨(i : ℕ) + 1, hi⟩ : Fin N) i)
      ∈ cellSubalg N k {swapNext i hi} := by
  classical
  have h := weylSubst_mem_cellSections (k := k) (swapNext i hi)
    (I := ({(1 : Equiv.Perm (Fin N))} : Finset (Equiv.Perm (Fin N)))) (lam := fun _ => 0)
    (cellCoord_mem_cellSections (⟨(i : ℕ) + 1, hi⟩ : Fin N) i)
  have hinv : (swapNext i hi)⁻¹ = swapNext i hi := by
    rw [swapNext, Equiv.swap_inv]
  have himg : ({(1 : Equiv.Perm (Fin N))} : Finset (Equiv.Perm (Fin N))).image
      (fun τ => (swapNext i hi)⁻¹ * τ) = {swapNext i hi} := by
    rw [Finset.image_singleton, mul_one, hinv]
  rwa [himg] at h

theorem fibrePow_neg_mem_swap (i : Fin N) (hi : (i : ℕ) + 1 < N) (j : ℕ) :
    fibrePow (k := k) i hi (-(j : ℤ)) ∈ cellSubalg N k {swapNext i hi} := by
  rw [fibrePow_neg_natCast]
  exact Subalgebra.pow_mem _ (cellCoord_succ_weyl_mem_swap i hi) j

theorem charUnits_neg_one' : charUnits (N := N) (-1 : kˣ) = (-1 : (FlagLoc N k)ˣ) := by
  refine Units.ext ?_
  rw [coe_charUnits, Units.val_neg, Units.val_one, Units.val_neg, Units.val_one, map_neg, map_one]

/-- **The two trivializations differ by the fibre power of the coroot pairing.** -/
theorem fibrePow_mul_cellTriv (i : Fin N) (hi : (i : ℕ) + 1 < N) (lam : Fin N → ℤ) :
    ∃ c : k, c ≠ 0 ∧
      fibrePow i hi (lam i - lam (⟨(i : ℕ) + 1, hi⟩ : Fin N))
          * ((cellTriv (1 : Equiv.Perm (Fin N)) lam : (FlagLoc N k)ˣ) : FlagLoc N k)
        = c • ((cellTriv (swapNext i hi) lam : (FlagLoc N k)ˣ) : FlagLoc N k) := by
  have hone : (1 : Equiv.Perm (Fin N)) * swapNext i hi = swapNext i hi := one_mul _
  have htrans := cellTriv_div_cellTriv_swapNext (k := k) (1 : Equiv.Perm (Fin N)) hi lam
  rw [hone] at htrans
  have hfib : fibreCoord (1 : Equiv.Perm (Fin N)) hi = (fibreUnit (k := k) i hi)⁻¹ := by
    rw [fibreUnit, inv_inv]
  rw [hfib] at htrans
  have heq : cellTriv (1 : Equiv.Perm (Fin N)) lam
      = ((fibreUnit (k := k) i hi)⁻¹ ^ (lam i - lam (⟨(i : ℕ) + 1, hi⟩ : Fin N))
          * (-1 : (FlagLoc N k)ˣ) ^ (lam (⟨(i : ℕ) + 1, hi⟩ : Fin N)))
        * cellTriv (swapNext i hi) lam := div_eq_iff_eq_mul.mp htrans
  have hunits : fibreUnit (k := k) i hi ^ (lam i - lam (⟨(i : ℕ) + 1, hi⟩ : Fin N))
      * cellTriv (1 : Equiv.Perm (Fin N)) lam
      = ((-1 : (FlagLoc N k)ˣ) ^ (lam (⟨(i : ℕ) + 1, hi⟩ : Fin N)))
        * cellTriv (swapNext i hi) lam := by
    rw [heq, inv_zpow, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  refine ⟨(((-1 : kˣ) ^ (lam (⟨(i : ℕ) + 1, hi⟩ : Fin N)) : kˣ) : k), Units.ne_zero _, ?_⟩
  have hval := congrArg (fun u : (FlagLoc N k)ˣ => (u : FlagLoc N k)) hunits
  simp only [Units.val_mul] at hval
  rw [fibrePow, hval, Algebra.smul_def]
  congr 1
  rw [← charUnits_neg_one', ← map_zpow]
  rfl

end GaloisForLFunctions.HTGeometry.BorelWeil
