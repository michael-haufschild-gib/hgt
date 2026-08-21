import GaloisForLFunctions.HTGeometry.BorelWeil.BigCellEvaluation

/-!
# Trivializing the line bundle on a Bruhat cell

On the `σ`-cell every leading minor of the permuted generic matrix is invertible, so the ratios of
consecutive minors are units of the localization.  The `i`-th such ratio scales by the `i`-th
diagonal entry of a Borel element, so an arbitrary integer power product of them realizes an
arbitrary weight: the line bundle `L_λ` is trivial on each Bruhat cell, with an explicit
trivializing section.

## Main definitions

* `minorUnit`, `diagRatio` — the leading minors and their consecutive ratios, as units.
* `cellTriv` — the trivializing section of `L_λ` on the `σ`-cell.

## Main results

* `substRightAway_coe_diagRatio` — the ratio scales by one diagonal entry.
* `cellTriv_mem_flagSemiInv` — the trivializing section has weight `λ`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

theorem truncate_zero {R : Type*} [CommRing R] (A : Matrix (Fin N) (Fin N) R) :
    truncate 0 A = 1 := by
  ext i l
  rw [truncate_apply_of_not_left (by omega)]
  by_cases h : i = l
  · rw [if_pos h, h, Matrix.one_apply_eq]
  · rw [if_neg h, Matrix.one_apply_ne h]

theorem minorPolyAt_zero (σ : Equiv.Perm (Fin N)) : minorPolyAt N k σ 0 = 1 := by
  rw [minorPolyAt, truncate_zero, Matrix.det_one]

theorem minorPolyAt_dvd_totalDenom (σ : Equiv.Perm (Fin N)) {j : ℕ} (hj : j ≤ N) :
    minorPolyAt N k σ j ∣ totalDenom N k := by
  classical
  have hcell : cellDenomPoly N k σ ∣ totalDenom N k :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ σ)
  cases j with
  | zero => rw [minorPolyAt_zero]; exact one_dvd _
  | succ m =>
    have hm : m < N := by omega
    have hfac : ∀ j : Fin N, minorPolyAt N k σ ((j : ℕ) + 1) ∣ cellDenomPoly N k σ := by
      intro j
      rw [cellDenomPoly]
      exact Finset.dvd_prod_of_mem (fun j : Fin N => minorPolyAt N k σ ((j : ℕ) + 1))
        (Finset.mem_univ j)
    exact (hfac ⟨m, hm⟩).trans hcell

theorem isUnit_algebraMap_minorPolyAt (σ : Equiv.Perm (Fin N)) {j : ℕ} (hj : j ≤ N) :
    IsUnit (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (minorPolyAt N k σ j)) :=
  isUnit_of_dvd_unit (map_dvd _ (minorPolyAt_dvd_totalDenom σ hj)) isUnit_algebraMap_totalDenom

/-- The `j`-th leading minor of the `σ`-cell, as a unit of the localization. -/
noncomputable def minorUnit (σ : Equiv.Perm (Fin N)) (j : ℕ) (hj : j ≤ N) : (FlagLoc N k)ˣ :=
  (isUnit_algebraMap_minorPolyAt (k := k) σ hj).unit

@[simp] theorem coe_minorUnit (σ : Equiv.Perm (Fin N)) {j : ℕ} (hj : j ≤ N) :
    ((minorUnit (k := k) σ j hj : (FlagLoc N k)ˣ) : FlagLoc N k)
      = algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (minorPolyAt N k σ j) :=
  IsUnit.unit_spec _

/-- The character by which the `j`-th leading minor scales under the Borel. -/
noncomputable def minorChar (j : ℕ) (B : Matrix (Fin N) (Fin N) k) : k :=
  ∏ i : Fin N, (if (i : ℕ) < j then B i i else 1)

theorem minorChar_ne_zero {j : ℕ} {B : Matrix (Fin N) (Fin N) k} (hB : IsBorelMat B) :
    minorChar j B ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  by_cases h : (i : ℕ) < j
  · rw [if_pos h]; exact hB.2 i
  · rw [if_neg h]; exact one_ne_zero

theorem minorChar_succ (j : Fin N) (B : Matrix (Fin N) (Fin N) k) :
    minorChar ((j : ℕ) + 1) B = minorChar (j : ℕ) B * B j j := by
  classical
  have h1 : minorChar ((j : ℕ) + 1) B
      = (if (j : ℕ) < (j : ℕ) + 1 then B j j else 1)
        * ∏ i ∈ Finset.univ.erase j, (if (i : ℕ) < (j : ℕ) + 1 then B i i else 1) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
  have h2 : minorChar (j : ℕ) B
      = (if (j : ℕ) < (j : ℕ) then B j j else 1)
        * ∏ i ∈ Finset.univ.erase j, (if (i : ℕ) < (j : ℕ) then B i i else 1) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
  have h3 : ∏ i ∈ Finset.univ.erase j, (if (i : ℕ) < (j : ℕ) + 1 then B i i else 1)
      = ∏ i ∈ Finset.univ.erase j, (if (i : ℕ) < (j : ℕ) then B i i else 1) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hne : i ≠ j := (Finset.mem_erase.mp hi).1
    have hne' : (i : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.ext hc)
    by_cases h : (i : ℕ) < (j : ℕ)
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  rw [h1, h3, if_pos (by omega), h2, if_neg (by omega), one_mul]
  ring

theorem substRightAway_coe_minorUnit {B : Matrix (Fin N) (Fin N) k} (hB : IsBorelMat B)
    (σ : Equiv.Perm (Fin N)) {j : ℕ} (hj : j ≤ N) :
    substRightAway hB ((minorUnit (k := k) σ j hj : (FlagLoc N k)ˣ) : FlagLoc N k)
      = minorChar j B • ((minorUnit (k := k) σ j hj : (FlagLoc N k)ˣ) : FlagLoc N k) := by
  rw [coe_minorUnit, substRightAway_algebraMap, substRight_minorPolyAt σ j hB.1, map_mul,
    Algebra.smul_def, IsScalarTower.algebraMap_apply k (MvPolynomial (Fin N × Fin N) k)
      (FlagLoc N k)]
  simp only [MvPolynomial.algebraMap_eq, minorChar]

/-- Scalars of the field as units of the localization. -/
noncomputable def charUnits : kˣ →* (FlagLoc N k)ˣ :=
  Units.map (algebraMap k (FlagLoc N k)).toMonoidHom

@[simp] theorem coe_charUnits (c : kˣ) :
    ((charUnits (N := N) c : (FlagLoc N k)ˣ) : FlagLoc N k) = algebraMap k (FlagLoc N k) (c : k) :=
  rfl

theorem map_minorUnit {B : Matrix (Fin N) (Fin N) k} (hB : IsBorelMat B)
    (σ : Equiv.Perm (Fin N)) {j : ℕ} (hj : j ≤ N) :
    Units.map (substRightAway hB).toMonoidHom (minorUnit (k := k) σ j hj)
      = charUnits (Units.mk0 (minorChar j B) (minorChar_ne_zero hB)) * minorUnit σ j hj := by
  refine Units.ext ?_
  rw [Units.coe_map, Units.val_mul, coe_charUnits, Units.val_mk0]
  show substRightAway hB ((minorUnit (k := k) σ j hj : (FlagLoc N k)ˣ) : FlagLoc N k) = _
  rw [substRightAway_coe_minorUnit hB, Algebra.smul_def]

/-- The ratio of consecutive leading minors on the `σ`-cell. -/
noncomputable def diagRatio (σ : Equiv.Perm (Fin N)) (i : Fin N) : (FlagLoc N k)ˣ :=
  minorUnit σ ((i : ℕ) + 1) i.isLt / minorUnit σ (i : ℕ) (le_of_lt i.isLt)

theorem map_diagRatio {B : Matrix (Fin N) (Fin N) k} (hB : IsBorelMat B)
    (σ : Equiv.Perm (Fin N)) (i : Fin N) :
    Units.map (substRightAway hB).toMonoidHom (diagRatio (k := k) σ i)
      = charUnits (Units.mk0 (B i i) (hB.2 i)) * diagRatio σ i := by
  have hchar : Units.mk0 (minorChar ((i : ℕ) + 1) B) (minorChar_ne_zero hB)
      = Units.mk0 (minorChar (i : ℕ) B) (minorChar_ne_zero hB) * Units.mk0 (B i i) (hB.2 i) := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, minorChar_succ]
  rw [diagRatio, map_div, map_minorUnit hB, map_minorUnit hB, hchar, map_mul, mul_assoc,
    mul_div_mul_comm, div_self', one_mul, mul_div_assoc]

/-- **The trivializing section of `L_λ` on the `σ`-cell.** -/
noncomputable def cellTriv (σ : Equiv.Perm (Fin N)) (lam : Fin N → ℤ) : (FlagLoc N k)ˣ :=
  ∏ i : Fin N, (diagRatio σ i) ^ (lam i)

theorem map_cellTriv {B : Matrix (Fin N) (Fin N) k} (hB : IsBorelMat B)
    (σ : Equiv.Perm (Fin N)) (lam : Fin N → ℤ) :
    Units.map (substRightAway hB).toMonoidHom (cellTriv (k := k) σ lam)
      = charUnits (∏ i : Fin N, (Units.mk0 (B i i) (hB.2 i)) ^ (lam i)) * cellTriv σ lam := by
  rw [cellTriv, map_prod, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow, map_diagRatio hB, mul_zpow, map_zpow]

/-- **The trivializing section has weight `λ`.** -/
theorem cellTriv_mem_flagSemiInv (σ : Equiv.Perm (Fin N)) (lam : Fin N → ℤ) :
    ((cellTriv (k := k) σ lam : (FlagLoc N k)ˣ) : FlagLoc N k) ∈ flagSemiInv N k lam := by
  intro B hB
  have h := map_cellTriv hB σ lam
  have hval := congrArg (fun u : (FlagLoc N k)ˣ => (u : FlagLoc N k)) h
  simp only [Units.coe_map, Units.val_mul, coe_charUnits] at hval
  have hchar : ((∏ i : Fin N, (Units.mk0 (B i i) (hB.2 i)) ^ (lam i) : kˣ) : k)
      = borelCharZ lam B := by
    rw [Units.coe_prod, borelCharZ]
    exact Finset.prod_congr rfl fun i _ => by rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  rw [hchar] at hval
  show substRightAway hB ((cellTriv (k := k) σ lam : (FlagLoc N k)ˣ) : FlagLoc N k) = _
  rw [Algebra.smul_def]
  exact hval

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

theorem coe_cellTriv_inv (σ : Equiv.Perm (Fin N)) (lam : Fin N → ℤ) :
    ((cellTriv (k := k) σ lam)⁻¹ : (FlagLoc N k)ˣ) = cellTriv σ (fun i => -lam i) := by
  rw [cellTriv, cellTriv, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun i _ => (zpow_neg _ _).symm

theorem flagSemiInv_congr {lam mu : Fin N → ℤ} (h : lam = mu) (x : FlagLoc N k) :
    x ∈ flagSemiInv N k lam ↔ x ∈ flagSemiInv N k mu := by rw [h]

/-- **Twisting a semi-invariant by the cell trivialization.** -/
theorem mem_flagSemiInv_mul_cellTriv (σ : Equiv.Perm (Fin N)) (lam mu : Fin N → ℤ)
    {x : FlagLoc N k} :
    x * ((cellTriv σ lam : (FlagLoc N k)ˣ) : FlagLoc N k)
        ∈ flagSemiInv N k (fun i => mu i + lam i)
      ↔ x ∈ flagSemiInv N k mu := by
  constructor
  · intro h
    have h2 := mul_mem_flagSemiInv h
      (cellTriv_mem_flagSemiInv (k := k) σ (fun i => -lam i))
    have hx : x * ((cellTriv σ lam : (FlagLoc N k)ˣ) : FlagLoc N k)
        * ((cellTriv σ (fun i => -lam i) : (FlagLoc N k)ˣ) : FlagLoc N k) = x := by
      rw [← coe_cellTriv_inv, mul_assoc, Units.mul_inv, mul_one]
    rw [hx] at h2
    refine (flagSemiInv_congr ?_ x).mp h2
    funext i
    ring
  · intro h
    have h2 := mul_mem_flagSemiInv h (cellTriv_mem_flagSemiInv (k := k) σ lam)
    exact h2

/-- The units of the localization that preserve the denominator bound of a set of cells. -/
def denomStable (I : Finset (Equiv.Perm (Fin N))) : Subgroup (FlagLoc N k)ˣ where
  carrier := {u | (∀ x : FlagLoc N k, x ∈ denomBounded N k I →
      x * (u : FlagLoc N k) ∈ denomBounded N k I)
    ∧ (∀ x : FlagLoc N k, x ∈ denomBounded N k I →
      x * ((u⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k) ∈ denomBounded N k I)}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [Units.val_mul, ← mul_assoc]
      exact hb1 _ (ha1 x hx)
    · rw [mul_inv, Units.val_mul, ← mul_assoc]
      exact hb2 _ (ha2 x hx)
  one_mem' := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> simpa using hx
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    exact ⟨ha2, by simpa using ha1⟩

theorem minorUnit_mem_denomStable {I : Finset (Equiv.Perm (Fin N))} {σ : Equiv.Perm (Fin N)}
    (hσ : σ ∈ I) {j : ℕ} (hj : j ≤ N) :
    minorUnit (k := k) σ j hj ∈ denomStable I := by
  classical
  have hfac : ∀ j : Fin N, minorPolyAt N k σ ((j : ℕ) + 1) ∣ cellDenomPoly N k σ := by
    intro j
    rw [cellDenomPoly]
    exact Finset.dvd_prod_of_mem (fun j : Fin N => minorPolyAt N k σ ((j : ℕ) + 1))
      (Finset.mem_univ j)
  have hcellI : cellDenomPoly N k σ ∣ denomOf N k I := by
    rw [denomOf]
    exact Finset.dvd_prod_of_mem _ hσ
  have hdvd : minorPolyAt N k σ j ∣ denomOf N k I := by
    cases j with
    | zero => rw [minorPolyAt_zero]; exact one_dvd _
    | succ m =>
      have hm : m < N := by omega
      exact (hfac ⟨m, hm⟩).trans hcellI
  obtain ⟨s, hs⟩ := hdvd
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨m, p, hp⟩ := hx
    refine ⟨m, p * minorPolyAt N k σ j, ?_⟩
    rw [coe_minorUnit, map_mul, ← hp]
    ring
  · obtain ⟨m, p, hp⟩ := hx
    refine ⟨m + 1, p * s, ?_⟩
    have hkey : (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (denomOf N k I))
        ^ (m + 1)
        = (algebraMap _ _ (denomOf N k I)) ^ m
          * ((minorUnit (k := k) σ j hj : (FlagLoc N k)ˣ) : FlagLoc N k)
            * algebraMap _ _ s := by
      rw [pow_succ, hs, map_mul, coe_minorUnit]
      ring
    rw [hkey, map_mul, ← hp]
    have hinv : ((minorUnit (k := k) σ j hj)⁻¹ : (FlagLoc N k)ˣ)
        * (minorUnit (k := k) σ j hj : (FlagLoc N k)ˣ) = 1 := inv_mul_cancel _
    have hinv' : ((((minorUnit (k := k) σ j hj)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k))
        * (((minorUnit (k := k) σ j hj : (FlagLoc N k)ˣ) : FlagLoc N k)) = 1 := by
      rw [← Units.val_mul, hinv, Units.val_one]
    calc x * (((minorUnit (k := k) σ j hj)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)
          * ((algebraMap _ (FlagLoc N k) (denomOf N k I)) ^ m
            * ((minorUnit (k := k) σ j hj : (FlagLoc N k)ˣ) : FlagLoc N k)
            * algebraMap _ _ s)
        = x * (algebraMap _ (FlagLoc N k) (denomOf N k I)) ^ m * algebraMap _ _ s
          * ((((minorUnit (k := k) σ j hj)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)
            * (((minorUnit (k := k) σ j hj : (FlagLoc N k)ˣ) : FlagLoc N k))) := by ring
      _ = x * (algebraMap _ (FlagLoc N k) (denomOf N k I)) ^ m * algebraMap _ _ s := by
          rw [hinv', mul_one]

theorem cellTriv_mem_denomStable {I : Finset (Equiv.Perm (Fin N))} {σ : Equiv.Perm (Fin N)}
    (hσ : σ ∈ I) (lam : Fin N → ℤ) : cellTriv (k := k) σ lam ∈ denomStable I := by
  refine Subgroup.prod_mem _ fun i _ => Subgroup.zpow_mem _ ?_ _
  exact Subgroup.div_mem _ (minorUnit_mem_denomStable hσ _) (minorUnit_mem_denomStable hσ _)

/-- **The line bundle is trivial on each Bruhat cell.**  Multiplying by the trivializing section
identifies the invariant functions on the cell with the sections of `L_λ` over it. -/
theorem mem_cellSections_mul_cellTriv {I : Finset (Equiv.Perm (Fin N))}
    {σ : Equiv.Perm (Fin N)} (hσ : σ ∈ I) (lam : Fin N → ℤ) {x : FlagLoc N k} :
    x * ((cellTriv σ lam : (FlagLoc N k)ˣ) : FlagLoc N k)
        ∈ cellSections N k I lam
      ↔ x ∈ cellSections N k I (fun _ => 0) := by
  rw [cellSections, cellSections, Submodule.mem_inf, Submodule.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · refine (mem_flagSemiInv_mul_cellTriv σ lam (fun _ => 0)).mp ?_
      refine (flagSemiInv_congr ?_ _).mp h1
      funext i
      ring
    · have := (cellTriv_mem_denomStable (k := k) hσ lam).2 _ h2
      rwa [mul_assoc, Units.mul_inv, mul_one] at this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, (cellTriv_mem_denomStable (k := k) hσ lam).1 _ h2⟩
    have := (mem_flagSemiInv_mul_cellTriv σ lam (fun _ => 0)).mpr h1
    refine (flagSemiInv_congr ?_ _).mp this
    funext i
    ring

end GaloisForLFunctions.HTGeometry.BorelWeil
