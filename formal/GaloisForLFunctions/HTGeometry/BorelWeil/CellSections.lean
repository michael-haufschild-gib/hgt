import GaloisForLFunctions.HTGeometry.BorelWeil.CellLocalization

/-!
# Sections of the line bundle over the Bruhat cells

For a set `I` of Weyl group elements, the sections of `L_λ` over the intersection of the
corresponding Bruhat cells are the `λ`-semi-invariant elements of the localization whose
denominators involve only the cell equations of `I`.  Both conditions are `k`-submodules of the
ambient localization `FlagLoc`, so the sections over every intersection of cells live in one place
and the inclusions between them are literal inclusions of submodules — which is what the Čech
differential of the Bruhat cover will be an alternating sum of.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.denomOf`, `denomBounded`
* `GaloisForLFunctions.HTGeometry.BorelWeil.flagSemiInv`
* `GaloisForLFunctions.HTGeometry.BorelWeil.cellSections`

## Main results

* `denomBounded_mono`, `cellSections_mono` — sections extend to smaller open sets.
* `algebraMap_mem_cellSections` — a global polynomial section is a section over every cell.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k]

/-- The product of the cell equations of a set of cells. -/
noncomputable def denomOf (N : ℕ) (k : Type*) [Field k] (I : Finset (Equiv.Perm (Fin N))) :
    MvPolynomial (Fin N × Fin N) k :=
  ∏ σ ∈ I, cellDenomPoly N k σ

theorem denomOf_dvd_of_subset {I J : Finset (Equiv.Perm (Fin N))} (h : I ⊆ J) :
    denomOf N k I ∣ denomOf N k J :=
  Finset.prod_dvd_prod_of_subset _ _ _ h

/-- Elements of the localization whose denominators come from the cells in `I`. -/
noncomputable def denomBounded (N : ℕ) (k : Type*) [Field k] (I : Finset (Equiv.Perm (Fin N))) :
    Submodule k (FlagLoc N k) where
  carrier := {x | ∃ (m : ℕ) (p : MvPolynomial (Fin N × Fin N) k),
    x * (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (denomOf N k I)) ^ m
      = algebraMap _ _ p}
  add_mem' := by
    rintro x y ⟨m, p, hp⟩ ⟨m', p', hp'⟩
    refine ⟨m + m', p * (denomOf N k I) ^ m' + p' * (denomOf N k I) ^ m, ?_⟩
    rw [pow_add, add_mul, map_add, map_mul, map_mul, map_pow, map_pow, ← hp, ← hp']
    ring
  zero_mem' := ⟨0, 0, by simp⟩
  smul_mem' := by
    rintro c x ⟨m, p, hp⟩
    refine ⟨m, MvPolynomial.C c * p, ?_⟩
    rw [map_mul, ← hp, Algebra.smul_def,
      IsScalarTower.algebraMap_apply k (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k)]
    simp only [MvPolynomial.algebraMap_eq]
    ring

theorem denomBounded_mono {I J : Finset (Equiv.Perm (Fin N))} (h : I ⊆ J) :
    denomBounded N k I ≤ denomBounded N k J := by
  rintro x ⟨m, p, hp⟩
  obtain ⟨q, hq⟩ := denomOf_dvd_of_subset (k := k) h
  refine ⟨m, p * q ^ m, ?_⟩
  rw [hq, map_mul, mul_pow, ← mul_assoc, hp, map_mul, map_pow]

theorem algebraMap_mem_denomBounded (p : MvPolynomial (Fin N × Fin N) k)
    (I : Finset (Equiv.Perm (Fin N))) :
    algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) p ∈ denomBounded N k I :=
  ⟨0, p, by simp⟩

theorem substRightAway_smul [Infinite k] {B : Matrix (Fin N) (Fin N) k} (hB : IsBorelMat B)
    (c : k) (x : FlagLoc N k) :
    substRightAway hB (c • x) = c • substRightAway hB x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k),
    substRightAway_algebraMap, AlgHom.commutes]

/-- The character of the Borel attached to an integer weight.  Integer weights are what the
`ρ`-shifted dot action produces, so they are the ones the Čech complex must be indexed by; on
natural-number weights this agrees with `borelCharMat`. -/
noncomputable def borelCharZ (lam : Fin N → ℤ) (B : Matrix (Fin N) (Fin N) k) : k :=
  ∏ i, (B i i) ^ (lam i)

theorem borelCharZ_natCast (lam : Fin N → ℕ) (B : Matrix (Fin N) (Fin N) k) :
    borelCharZ (fun i => (lam i : ℤ)) B = borelCharMat lam B :=
  Finset.prod_congr rfl fun _ _ => zpow_natCast _ _

/-- The `λ`-semi-invariants of the localization. -/
noncomputable def flagSemiInv (N : ℕ) (k : Type*) [Field k] [Infinite k] (lam : Fin N → ℤ) :
    Submodule k (FlagLoc N k) where
  carrier := {x | ∀ (B : Matrix (Fin N) (Fin N) k) (hB : IsBorelMat B),
    substRightAway hB x = borelCharZ lam B • x}
  add_mem' := by
    intro x y hx hy B hB
    rw [map_add, hx B hB, hy B hB, smul_add]
  zero_mem' := by
    intro B hB
    rw [map_zero, smul_zero]
  smul_mem' := by
    intro c x hx B hB
    rw [substRightAway_smul, hx B hB, smul_comm]

/-- **Sections of `L_λ` over the intersection of the cells in `I`.** -/
noncomputable def cellSections (N : ℕ) (k : Type*) [Field k] [Infinite k] (I : Finset (Equiv.Perm (Fin N)))
    (lam : Fin N → ℤ) : Submodule k (FlagLoc N k) :=
  flagSemiInv N k lam ⊓ denomBounded N k I

theorem cellSections_mono [Infinite k] {I J : Finset (Equiv.Perm (Fin N))} (h : I ⊆ J)
    (lam : Fin N → ℤ) : cellSections N k I lam ≤ cellSections N k J lam :=
  inf_le_inf_left _ (denomBounded_mono h)

theorem substRight_of_mem_polySections [Infinite k] {lam : Fin N → ℕ}
    {p : MvPolynomial (Fin N × Fin N) k} (hp : p ∈ polySections lam)
    {B : Matrix (Fin N) (Fin N) k} (hB : IsBorelMat B) :
    substRight B p = MvPolynomial.C (borelCharMat lam B) * p := by
  refine matEval_injective fun g => ?_
  have hC : matEval g (MvPolynomial.C (borelCharMat lam B)) = borelCharMat lam B := by
    simp [matEval]
  rw [matEval_substRight, matEval_mul, hC, hp g B hB]

/-- **A global polynomial section is a section over every cell.** -/
theorem algebraMap_mem_cellSections [Infinite k] {lam : Fin N → ℕ}
    {p : MvPolynomial (Fin N × Fin N) k} (hp : p ∈ polySections lam)
    (I : Finset (Equiv.Perm (Fin N))) :
    algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) p
      ∈ cellSections N k I (fun i => (lam i : ℤ)) := by
  refine ⟨fun B hB => ?_, algebraMap_mem_denomBounded p I⟩
  rw [substRightAway_algebraMap, substRight_of_mem_polySections hp hB, map_mul, Algebra.smul_def,
    IsScalarTower.algebraMap_apply k (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k),
    borelCharZ_natCast]
  simp only [MvPolynomial.algebraMap_eq]

end GaloisForLFunctions.HTGeometry.BorelWeil
