import GaloisForLFunctions.HTGeometry.BorelWeil.LowerCellSubstitution

/-!
# Coordinates on the big cell

The big cell of the flag variety is the affine space of lower unitriangular matrices, and its
coordinates are ratios of minors: the `(i,j)` bordered minor — the leading `(j+1)`-minor with its
last row replaced by row `i` — divided by the `(j+1)`-st leading minor.  Both scale by the same
Borel character, so the ratio is an invariant section, and on a lower unitriangular matrix it
evaluates to the `(i,j)` entry.

## Main definitions

* `borderPoly`, `cellCoord`

## Main results

* `leadingMinorMat_update_of_isLowerUni` — the bordered minor of a lower unitriangular matrix is the
  corresponding entry.
* `flagEval_cellCoord` — the coordinate evaluates to the matrix entry.
* `cellCoord_mem_flagSemiInv` — the coordinates are invariant.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

theorem submatrix_mul_row (g B : Matrix (Fin N) (Fin N) k) (f : Fin N → Fin N) :
    (g * B).submatrix f id = (g.submatrix f id) * B := by
  ext i l
  simp [Matrix.mul_apply]

/-- The `(i,j)` bordered minor: the leading `(j+1)`-minor with its last row replaced by row `i`. -/
noncomputable def borderPoly (i j : Fin N) : MvPolynomial (Fin N × Fin N) k :=
  (truncate ((j : ℕ) + 1)
    ((genericMatrix N k).submatrix (Function.update (id : Fin N → Fin N) j i) id)).det

theorem matEval_borderPoly (i j : Fin N) (g : Matrix (Fin N) (Fin N) k) :
    matEval g (borderPoly i j)
      = leadingMinorMat ((j : ℕ) + 1)
          (g.submatrix (Function.update (id : Fin N → Fin N) j i) id) := by
  classical
  have hmap : (truncate ((j : ℕ) + 1)
      ((genericMatrix N k).submatrix (Function.update (id : Fin N → Fin N) j i) id)).map
      (MvPolynomial.eval (fun ij : Fin N × Fin N => g ij.1 ij.2))
      = truncate ((j : ℕ) + 1) (g.submatrix (Function.update (id : Fin N → Fin N) j i) id) := by
    ext r c
    by_cases h1 : (r : ℕ) < (j : ℕ) + 1
    · by_cases h2 : (c : ℕ) < (j : ℕ) + 1
      · simp [Matrix.map_apply, truncate_apply_of_both h1 h2, genericMatrix]
      · rw [Matrix.map_apply, truncate_apply_of_not_right h2, truncate_apply_of_not_right h2]
        by_cases h3 : r = c <;> simp [h3]
    · rw [Matrix.map_apply, truncate_apply_of_not_left h1, truncate_apply_of_not_left h1]
      by_cases h3 : r = c <;> simp [h3]
  rw [borderPoly, leadingMinorMat, matEval, ← hmap, RingHom.map_det]
  rfl

/-- **The bordered minor of a lower unitriangular matrix is the corresponding entry.** -/
theorem leadingMinorMat_update_of_isLowerUni {L : Matrix (Fin N) (Fin N) k} (hL : IsLowerUni L)
    (i j : Fin N) :
    leadingMinorMat ((j : ℕ) + 1) (L.submatrix (Function.update (id : Fin N → Fin N) j i) id)
      = L i j := by
  classical
  set f : Fin N → Fin N := Function.update (id : Fin N → Fin N) j i with hf
  have hfj : f j = i := by rw [hf, Function.update_self]
  have hfne : ∀ r : Fin N, r ≠ j → f r = r := by
    intro r hr
    rw [hf, Function.update_of_ne hr]
    rfl
  have htri : (truncate ((j : ℕ) + 1) (L.submatrix f id)).BlockTriangular
      (OrderDual.toDual : Fin N → (Fin N)ᵒᵈ) := by
    intro r c hrc
    have hlt : r < c := hrc
    by_cases h1 : (r : ℕ) < (j : ℕ) + 1
    · by_cases h2 : (c : ℕ) < (j : ℕ) + 1
      · rw [truncate_apply_of_both h1 h2, Matrix.submatrix_apply, id_eq]
        by_cases hrj : r = j
        · exfalso
          have : (j : ℕ) < (c : ℕ) := by rw [← hrj]; exact hlt
          omega
        · rw [hfne r hrj]
          exact hL.1 r c hlt
      · rw [truncate_apply_of_not_right h2, if_neg (ne_of_lt hlt)]
    · rw [truncate_apply_of_not_left h1, if_neg (ne_of_lt hlt)]
  have hdiag : ∀ r : Fin N, r ≠ j → (truncate ((j : ℕ) + 1) (L.submatrix f id)) r r = 1 := by
    intro r hr
    by_cases h1 : (r : ℕ) < (j : ℕ) + 1
    · rw [truncate_apply_of_both h1 h1, Matrix.submatrix_apply, id_eq, hfne r hr, hL.2]
    · rw [truncate_apply_of_not_left h1, if_pos rfl]
  rw [leadingMinorMat, Matrix.det_of_lowerTriangular _ htri,
    Finset.prod_eq_single j (fun r _ hr => hdiag r hr) (fun h => absurd (Finset.mem_univ j) h),
    truncate_apply_of_both (by omega) (by omega), Matrix.submatrix_apply, id_eq, hfj]

theorem borelCharZ_indicator (j : Fin N) (B : Matrix (Fin N) (Fin N) k) :
    borelCharZ (fun l : Fin N => if (l : ℕ) < (j : ℕ) + 1 then (1 : ℤ) else 0) B
      = minorChar ((j : ℕ) + 1) B := by
  rw [borelCharZ, minorChar]
  refine Finset.prod_congr rfl fun l _ => ?_
  by_cases h : (l : ℕ) < (j : ℕ) + 1
  · rw [if_pos h, if_pos h, zpow_one]
  · rw [if_neg h, if_neg h, zpow_zero]

theorem substRight_borderPoly (i j : Fin N) {B : Matrix (Fin N) (Fin N) k}
    (hB : B.BlockTriangular id) :
    substRight B (borderPoly i j)
      = MvPolynomial.C (minorChar ((j : ℕ) + 1) B) * borderPoly (k := k) i j := by
  refine matEval_injective fun g => ?_
  have hC : matEval g (MvPolynomial.C (minorChar ((j : ℕ) + 1) B))
      = minorChar ((j : ℕ) + 1) B := by simp [matEval]
  rw [matEval_substRight, matEval_borderPoly, matEval_mul, hC, matEval_borderPoly,
    submatrix_mul_row, leadingMinorMat_mul_borel _ _ hB, minorChar, mul_comm]

theorem algebraMap_borderPoly_mem_flagSemiInv (i j : Fin N) :
    algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (borderPoly i j)
      ∈ flagSemiInv N k (fun l : Fin N => if (l : ℕ) < (j : ℕ) + 1 then (1 : ℤ) else 0) := by
  intro B hB
  rw [substRightAway_algebraMap, substRight_borderPoly i j hB.1, map_mul, borelCharZ_indicator,
    Algebra.smul_def, IsScalarTower.algebraMap_apply k (MvPolynomial (Fin N × Fin N) k)
      (FlagLoc N k)]
  simp only [MvPolynomial.algebraMap_eq]

/-- The inverse of a semi-invariant unit is semi-invariant of the opposite weight. -/
theorem inv_mem_flagSemiInv {lam : Fin N → ℤ} {u : (FlagLoc N k)ˣ}
    (hu : ((u : (FlagLoc N k)ˣ) : FlagLoc N k) ∈ flagSemiInv N k lam) :
    (((u⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)) ∈ flagSemiInv N k (fun i => -lam i) := by
  intro B hB
  have hc : borelCharZ lam B ≠ 0 := borelCharZ_ne_zero hB
  have hune : ((u : (FlagLoc N k)ˣ) : FlagLoc N k) ≠ 0 := Units.ne_zero u
  have hkey : substRightAway hB (((u⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k))
      * (borelCharZ lam B • ((u : (FlagLoc N k)ˣ) : FlagLoc N k)) = 1 := by
    rw [← hu B hB, ← map_mul]
    rw [show (((u⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)) * ((u : (FlagLoc N k)ˣ) : FlagLoc N k) = 1 by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]]
    exact map_one _
  have hother : borelCharZ (fun i => -lam i) B • (((u⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k))
      * (borelCharZ lam B • ((u : (FlagLoc N k)ˣ) : FlagLoc N k)) = 1 := by
    have hchar : borelCharZ (fun i => -lam i) B = (borelCharZ lam B)⁻¹ := by
      rw [borelCharZ, borelCharZ, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun l _ => by rw [zpow_neg]
    rw [hchar, smul_mul_smul_comm, inv_mul_cancel₀ hc,
      show (((u⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)) * ((u : (FlagLoc N k)ˣ) : FlagLoc N k) = 1 by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one],
      one_smul]
  refine mul_right_cancel₀ ?_ (hkey.trans hother.symm)
  intro hzero
  rcases smul_eq_zero.mp hzero with h | h
  · exact hc h
  · exact hune h

/-- The `(i,j)` coordinate on the big cell: a ratio of minors. -/
noncomputable def cellCoord (i j : Fin N) : FlagLoc N k :=
  algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (borderPoly i j)
    * (((minorUnit (1 : Equiv.Perm (Fin N)) ((j : ℕ) + 1) j.isLt)⁻¹ : (FlagLoc N k)ˣ) :
        FlagLoc N k)

theorem coe_minorUnit_mem_flagSemiInv (σ : Equiv.Perm (Fin N)) (j : Fin N) :
    ((minorUnit (k := k) σ ((j : ℕ) + 1) j.isLt : (FlagLoc N k)ˣ) : FlagLoc N k)
      ∈ flagSemiInv N k (fun l : Fin N => if (l : ℕ) < (j : ℕ) + 1 then (1 : ℤ) else 0) := by
  intro B hB
  rw [substRightAway_coe_minorUnit hB, borelCharZ_indicator]

/-- **The cell coordinates are invariant sections.** -/
theorem cellCoord_mem_flagSemiInv (i j : Fin N) :
    cellCoord (k := k) i j ∈ flagSemiInv N k (fun _ => 0) := by
  have h1 := algebraMap_borderPoly_mem_flagSemiInv (k := k) i j
  have h2 := inv_mem_flagSemiInv (coe_minorUnit_mem_flagSemiInv (k := k) (1 : Equiv.Perm (Fin N)) j)
  have h3 := mul_mem_flagSemiInv h1 h2
  refine (flagSemiInv_congr ?_ _).mp h3
  funext l
  ring

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

theorem flagEval_units_inv {g : Matrix (Fin N) (Fin N) k} (hg : matEval g (totalDenom N k) ≠ 0)
    (u : (FlagLoc N k)ˣ) :
    flagEval hg (((u⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k))
      = (flagEval hg ((u : (FlagLoc N k)ˣ) : FlagLoc N k))⁻¹ := by
  have hmul : flagEval hg (((u⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k))
      * flagEval hg ((u : (FlagLoc N k)ˣ) : FlagLoc N k) = 1 := by
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  exact eq_inv_of_mul_eq_one_left hmul

theorem matEval_denomOf_one_of_isLowerUni {L : Matrix (Fin N) (Fin N) k} (hL : IsLowerUni L) :
    matEval L (denomOf N k {(1 : Equiv.Perm (Fin N))}) = 1 := by
  rw [denomOf_singleton, matEval_cellDenomPoly_one_of_isLowerUni hL]

/-- **The cell coordinate evaluates to the matrix entry.** -/
theorem flagEval_cellCoord {L : Matrix (Fin N) (Fin N) k} (hL : IsLowerUni L)
    (hLT : matEval L (totalDenom N k) ≠ 0) (i j : Fin N) :
    flagEval hLT (cellCoord i j) = L i j := by
  have hsub : L.submatrix (⇑(1 : Equiv.Perm (Fin N))) id = L := by
    ext r s
    rfl
  rw [cellCoord, map_mul, flagEval_algebraMap, matEval_borderPoly,
    leadingMinorMat_update_of_isLowerUni hL, flagEval_units_inv, coe_minorUnit,
    flagEval_algebraMap, matEval_minorPolyAt, hsub, leadingMinorMat_of_isLowerUni hL,
    inv_one, mul_one]

/-- Substituting the cell coordinates into a polynomial. -/
noncomputable def cellCoordAlg : MvPolynomial (Fin N × Fin N) k →ₐ[k] FlagLoc N k :=
  MvPolynomial.aeval fun ij : Fin N × Fin N => cellCoord ij.1 ij.2

theorem flagEval_cellCoordAlg {L : Matrix (Fin N) (Fin N) k} (hL : IsLowerUni L)
    (hLT : matEval L (totalDenom N k) ≠ 0) (p : MvPolynomial (Fin N × Fin N) k) :
    flagEval hLT (cellCoordAlg p) = matEval L p := by
  have hcomp : (flagEval hLT).comp (cellCoordAlg (k := k) (N := N)).toRingHom
      = MvPolynomial.eval fun ij : Fin N × Fin N => L ij.1 ij.2 := by
    apply MvPolynomial.ringHom_ext
    · intro r
      show flagEval hLT (cellCoordAlg (MvPolynomial.C r)) = _
      rw [cellCoordAlg, MvPolynomial.aeval_C]
      rw [flagEval_algebraMap_field]
      simp
    · intro ij
      show flagEval hLT (cellCoordAlg (MvPolynomial.X ij)) = _
      rw [cellCoordAlg, MvPolynomial.aeval_X, flagEval_cellCoord hL hLT, MvPolynomial.eval_X]
  exact congrFun (congrArg (fun φ : MvPolynomial (Fin N × Fin N) k →+* k => (φ : _ → k)) hcomp) p

theorem denomBounded_mul {I : Finset (Equiv.Perm (Fin N))} {x y : FlagLoc N k}
    (hx : x ∈ denomBounded N k I) (hy : y ∈ denomBounded N k I) :
    x * y ∈ denomBounded N k I := by
  obtain ⟨m, p, hp⟩ := hx
  obtain ⟨n, q, hq⟩ := hy
  refine ⟨m + n, p * q, ?_⟩
  rw [pow_add, map_mul, ← hp, ← hq]
  ring

theorem one_mem_denomBounded (I : Finset (Equiv.Perm (Fin N))) :
    (1 : FlagLoc N k) ∈ denomBounded N k I := by
  have h := algebraMap_mem_denomBounded (k := k) (1 : MvPolynomial (Fin N × Fin N) k) I
  rwa [map_one] at h

theorem one_mem_flagSemiInv_zero : (1 : FlagLoc N k) ∈ flagSemiInv N k (fun _ => 0) := by
  intro B hB
  rw [map_one, borelCharZ]
  simp

theorem mul_mem_flagSemiInv_zero {x y : FlagLoc N k} (hx : x ∈ flagSemiInv N k (fun _ => 0))
    (hy : y ∈ flagSemiInv N k (fun _ => 0)) : x * y ∈ flagSemiInv N k (fun _ => 0) := by
  have h := mul_mem_flagSemiInv hx hy
  refine (flagSemiInv_congr ?_ _).mp h
  funext i
  ring

theorem cellCoord_mem_cellSections (i j : Fin N) :
    cellCoord (k := k) i j ∈ cellSections N k {(1 : Equiv.Perm (Fin N))} (fun _ => 0) := by
  refine ⟨cellCoord_mem_flagSemiInv i j, ?_⟩
  refine denomBounded_mul (algebraMap_mem_denomBounded _ _) ?_
  have h := (minorUnit_mem_denomStable (k := k) (1 : Equiv.Perm (Fin N))
    (j := (j : ℕ) + 1) j.isLt).2 1 (one_mem_denomBounded _)
  rwa [one_mul] at h

theorem cellCoordAlg_mem_cellSections (p : MvPolynomial (Fin N × Fin N) k) :
    cellCoordAlg p ∈ cellSections N k {(1 : Equiv.Perm (Fin N))} (fun _ => 0) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r =>
      rw [cellCoordAlg, MvPolynomial.aeval_C]
      have hone : (1 : FlagLoc N k) ∈ cellSections N k {(1 : Equiv.Perm (Fin N))} (fun _ => 0) :=
        ⟨one_mem_flagSemiInv_zero, one_mem_denomBounded _⟩
      have hsm := Submodule.smul_mem _ r hone
      rwa [Algebra.smul_def, mul_one] at hsm
  | add q r hq hr =>
      rw [map_add]
      exact Submodule.add_mem _ hq hr
  | mul_X q ij hq =>
      rw [map_mul, cellCoordAlg, MvPolynomial.aeval_X]
      exact ⟨mul_mem_flagSemiInv_zero hq.1 (cellCoord_mem_flagSemiInv ij.1 ij.2),
        denomBounded_mul hq.2 (cellCoord_mem_cellSections ij.1 ij.2).2⟩

/-- **The invariant sections on the big cell are exactly the polynomials in the cell
coordinates.** -/
theorem exists_cellCoordAlg_eq {x : FlagLoc N k}
    (hx : x ∈ cellSections N k {(1 : Equiv.Perm (Fin N))} (fun _ => 0)) :
    ∃ p : MvPolynomial (Fin N × Fin N) k, x = cellCoordAlg p := by
  obtain ⟨hsemi, m, p, hp⟩ := hx
  refine ⟨p, ?_⟩
  have hdiff : x - cellCoordAlg p = 0 := by
    refine eq_zero_of_flagEval_lowerUni_eq_zero (lam := fun _ => 0) ?_ ?_
    · exact Submodule.sub_mem _ hsemi (cellCoordAlg_mem_cellSections p).1
    · intro L hL hLT
      rw [map_sub, flagEval_cellCoordAlg hL hLT]
      have hval := congrArg (flagEval hLT) hp
      rw [map_mul, map_pow, flagEval_algebraMap, flagEval_algebraMap,
        matEval_denomOf_one_of_isLowerUni hL, one_pow, mul_one] at hval
      rw [hval, sub_self]
  exact sub_eq_zero.mp hdiff

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

theorem borderPoly_diag (j : Fin N) :
    borderPoly (k := k) j j = minorPolyAt N k (1 : Equiv.Perm (Fin N)) ((j : ℕ) + 1) := by
  rw [borderPoly, minorPolyAt]
  congr 2
  ext r c
  rw [Matrix.submatrix_apply, Matrix.submatrix_apply, id_eq, id_eq]
  by_cases h : r = j
  · rw [h, Function.update_self]
    rfl
  · rw [Function.update_of_ne h]
    rfl

@[simp] theorem cellCoord_diag (j : Fin N) : cellCoord (k := k) j j = 1 := by
  rw [cellCoord, borderPoly_diag, ← coe_minorUnit (1 : Equiv.Perm (Fin N)) j.isLt,
    ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem borderPoly_eq_zero_of_lt {i j : Fin N} (hij : i < j) : borderPoly (k := k) i j = 0 := by
  classical
  have hne : i ≠ j := ne_of_lt hij
  refine Matrix.det_zero_of_row_eq hne ?_
  funext c
  have hi : (i : ℕ) < (j : ℕ) + 1 := by have : (i : ℕ) < (j : ℕ) := hij; omega
  have hj : (j : ℕ) < (j : ℕ) + 1 := by omega
  by_cases hc : (c : ℕ) < (j : ℕ) + 1
  · rw [truncate_apply_of_both hi hc, truncate_apply_of_both hj hc, Matrix.submatrix_apply,
      Matrix.submatrix_apply, Function.update_of_ne hne, Function.update_self]
    rfl
  · rw [truncate_apply_of_not_right hc, truncate_apply_of_not_right hc,
      if_neg (fun h => by rw [h] at hi; omega), if_neg (fun h => by rw [h] at hj; omega)]

@[simp] theorem cellCoord_eq_zero_of_lt {i j : Fin N} (hij : i < j) :
    cellCoord (k := k) i j = 0 := by
  rw [cellCoord, borderPoly_eq_zero_of_lt hij, map_zero, zero_mul]

theorem flagEval_cellCoordAlg_lowerSubst {L : Matrix (Fin N) (Fin N) k} (hL : IsLowerUni L)
    (hLT : matEval L (totalDenom N k) ≠ 0) (p : MvPolynomial (Fin N × Fin N) k) :
    flagEval hLT (cellCoordAlg (lowerSubst p)) = matEval L p := by
  rw [flagEval_cellCoordAlg hL hLT, matEval_lowerSubst, lowerMat_of_isLowerUni hL]

/-- **The sections over an intersection of cells are the chart functions with denominators the
restricted cell equations.** -/
theorem exists_cellCoordAlg_denom {I : Finset (Equiv.Perm (Fin N))} {x : FlagLoc N k}
    (hx : x ∈ cellSections N k I (fun _ => 0)) :
    ∃ (m : ℕ) (p : MvPolynomial (Fin N × Fin N) k),
      x * (cellCoordAlg (lowerSubst (denomOf N k I))) ^ m = cellCoordAlg p := by
  obtain ⟨hsemi, m, p, hp⟩ := hx
  refine ⟨m, p, ?_⟩
  have hdiff : x * (cellCoordAlg (lowerSubst (denomOf N k I))) ^ m - cellCoordAlg p = 0 := by
    refine eq_zero_of_flagEval_lowerUni_eq_zero (lam := fun _ => 0) ?_ ?_
    · refine Submodule.sub_mem _ ?_ (cellCoordAlg_mem_cellSections p).1
      refine mul_mem_flagSemiInv_zero hsemi ?_
      have hpow : ∀ n : ℕ, (cellCoordAlg (lowerSubst (denomOf N k I))) ^ n
          ∈ flagSemiInv N k (fun _ : Fin N => 0) := by
        intro n
        induction n with
        | zero => rw [pow_zero]; exact one_mem_flagSemiInv_zero
        | succ q ih =>
            rw [pow_succ]
            exact mul_mem_flagSemiInv_zero ih (cellCoordAlg_mem_cellSections _).1
      exact hpow m
    · intro L hL hLT
      rw [map_sub, map_mul, map_pow, flagEval_cellCoordAlg_lowerSubst hL hLT,
        flagEval_cellCoordAlg hL hLT]
      have hval := congrArg (flagEval hLT) hp
      rw [map_mul, map_pow, flagEval_algebraMap, flagEval_algebraMap] at hval
      rw [hval, sub_self]
  exact sub_eq_zero.mp hdiff

end GaloisForLFunctions.HTGeometry.BorelWeil
