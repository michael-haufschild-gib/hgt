import GaloisForLFunctions.HTGeometry.BorelWeil.CellAlgebra

/-!
# The base coordinates of a `ℙ¹` fibration

The functions regular on both cells of a coset pair are the ones pulled back from the base of the
fibration `G/B → G/P_i`.  Two families of them are visible directly: the cell coordinates whose
denominator is a leading minor other than the `(i+1)`-st — those minors agree up to sign with the
ones of the reflected cell — and, for each row below the step, the ratio of the `(i+2)`-minor with
rows `(0,…,i−1,i+1,r)` to the `(i+2)`-nd leading minor.  On the big cell the latter is
`t · c_{r,i+1} − c_{r,i}`, so modulo the fibre coordinate it recovers the one coordinate that is not
already a base coordinate.

## Main results

* `det_of_almost_lowerTriangular` — a determinant that is lower triangular apart from one entry.
* `leadingMinorMat_pairUpdate_of_isLowerUni` — the `(i+2)`-minor of a lower unitriangular matrix
  with rows `(0,…,i−1,i+1,b)`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- **A determinant that is lower triangular apart from one entry.**  If a matrix vanishes above the
diagonal except at the single position `(i, i')` with `i' = i + 1`, has `1` there, and has unit
diagonal away from `i` and `i'`, its determinant is the `2 × 2` determinant of the exceptional
block. -/
theorem det_of_almost_lowerTriangular {M : Matrix (Fin N) (Fin N) k} {i i' : Fin N}
    (hii' : (i' : ℕ) = (i : ℕ) + 1) (hone : M i i' = 1)
    (hzero : ∀ ρ c : Fin N, (ρ : ℕ) < (c : ℕ) → ¬ (ρ = i ∧ c = i') → M ρ c = 0)
    (hdiag : ∀ ρ : Fin N, ρ ≠ i → ρ ≠ i' → M ρ ρ = 1) :
    M.det = M i i * M i' i' - M i' i := by
  classical
  have hne : i ≠ i' := by
    intro hc
    rw [hc] at hii'
    omega
  have hswapi : (Equiv.swap i i') i = i' := Equiv.swap_apply_left i i'
  have hswapi' : (Equiv.swap i i') i' = i := Equiv.swap_apply_right i i'
  have hSdet : (M.submatrix id ⇑(Equiv.swap i i')).det = - M.det := by
    rw [Matrix.det_permute', Equiv.Perm.sign_swap hne]
    simp
  have hTdet : ((M.submatrix id ⇑(Equiv.swap i i')).updateCol i'
      (fun ρ => (M.submatrix id ⇑(Equiv.swap i i')) ρ i'
        + (-(M i i)) • (M.submatrix id ⇑(Equiv.swap i i')) ρ i)).det
      = (M.submatrix id ⇑(Equiv.swap i i')).det :=
    Matrix.det_updateCol_add_smul_self _ (Ne.symm hne) _
  have hTapply : ∀ ρ c : Fin N,
      ((M.submatrix id ⇑(Equiv.swap i i')).updateCol i'
        (fun ρ => (M.submatrix id ⇑(Equiv.swap i i')) ρ i'
          + (-(M i i)) • (M.submatrix id ⇑(Equiv.swap i i')) ρ i)) ρ c
        = if c = i' then M ρ i + (-(M i i)) * M ρ i' else M ρ ((Equiv.swap i i') c) := by
    intro ρ c
    rw [Matrix.updateCol_apply]
    by_cases hc : c = i'
    · rw [if_pos hc, if_pos hc]
      simp only [Matrix.submatrix_apply, id_eq, hswapi, hswapi', smul_eq_mul]
    · rw [if_neg hc, if_neg hc]
      simp only [Matrix.submatrix_apply, id_eq]
  have htri : ((M.submatrix id ⇑(Equiv.swap i i')).updateCol i'
      (fun ρ => (M.submatrix id ⇑(Equiv.swap i i')) ρ i'
        + (-(M i i)) • (M.submatrix id ⇑(Equiv.swap i i')) ρ i)).BlockTriangular
      (OrderDual.toDual : Fin N → (Fin N)ᵒᵈ) := by
    intro ρ c hrc
    have hlt : ρ < c := hrc
    rw [hTapply]
    by_cases hc : c = i'
    · rw [if_pos hc]
      have hrle : (ρ : ℕ) ≤ (i : ℕ) := by
        have : (ρ : ℕ) < (c : ℕ) := hlt
        rw [hc] at this
        omega
      by_cases hri : ρ = i
      · rw [hri, hone, mul_one]
        ring
      · have hrlt : (ρ : ℕ) < (i : ℕ) := by
          have : (ρ : ℕ) ≠ (i : ℕ) := fun hcon => hri (Fin.ext hcon)
          omega
        have h1 : M ρ i = 0 := hzero ρ i hrlt (fun hcon => hri hcon.1)
        have h2 : M ρ i' = 0 := hzero ρ i' (by omega) (fun hcon => hri hcon.1)
        rw [h1, h2, mul_zero, add_zero]
    · rw [if_neg hc]
      by_cases hci : c = i
      · rw [hci, hswapi]
        refine hzero ρ i' ?_ ?_
        · have : (ρ : ℕ) < (c : ℕ) := hlt
          rw [hci] at this
          omega
        · rintro ⟨hcon, -⟩
          rw [hcon, hci] at hlt
          exact absurd hlt (lt_irrefl _)
      · rw [Equiv.swap_apply_of_ne_of_ne hci hc]
        exact hzero ρ c hlt (fun hcon => hc hcon.2)
  have hdiagT : ∀ ρ : Fin N,
      ((M.submatrix id ⇑(Equiv.swap i i')).updateCol i'
        (fun ρ => (M.submatrix id ⇑(Equiv.swap i i')) ρ i'
          + (-(M i i)) • (M.submatrix id ⇑(Equiv.swap i i')) ρ i)) ρ ρ
        = if ρ = i' then M i' i + (-(M i i)) * M i' i' else 1 := by
    intro ρ
    rw [hTapply]
    by_cases hri' : ρ = i'
    · rw [if_pos hri', if_pos hri', hri']
    · rw [if_neg hri', if_neg hri']
      by_cases hri : ρ = i
      · rw [hri, hswapi, hone]
      · rw [Equiv.swap_apply_of_ne_of_ne hri hri']
        exact hdiag ρ hri hri'
  have hprod : ((M.submatrix id ⇑(Equiv.swap i i')).updateCol i'
      (fun ρ => (M.submatrix id ⇑(Equiv.swap i i')) ρ i'
        + (-(M i i)) • (M.submatrix id ⇑(Equiv.swap i i')) ρ i)).det
      = M i' i + (-(M i i)) * M i' i' := by
    rw [Matrix.det_of_lowerTriangular _ htri,
      Finset.prod_congr rfl fun ρ (_ : ρ ∈ Finset.univ) => hdiagT ρ,
      Finset.prod_eq_single i' (fun ρ _ hρ => by rw [if_neg hρ]) (fun h => absurd
        (Finset.mem_univ i') h), if_pos rfl]
  rw [hTdet, hSdet] at hprod
  have hfin : -M.det = M i' i + (-(M i i)) * M i' i' := hprod
  linear_combination -hfin

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- **The `(i+2)`-minor of a lower unitriangular matrix with rows `(0,…,i−1,i+1,b)`.** -/
theorem leadingMinorMat_pairUpdate_of_isLowerUni {L : Matrix (Fin N) (Fin N) k} (hL : IsLowerUni L)
    (i : Fin N) (hi : (i : ℕ) + 1 < N) (b : Fin N) :
    leadingMinorMat ((i : ℕ) + 2)
        (L.submatrix (Function.update (Function.update (id : Fin N → Fin N) i
          (⟨(i : ℕ) + 1, hi⟩ : Fin N)) (⟨(i : ℕ) + 1, hi⟩ : Fin N) b) id)
      = L (⟨(i : ℕ) + 1, hi⟩ : Fin N) i * L b (⟨(i : ℕ) + 1, hi⟩ : Fin N) - L b i := by
  classical
  have hi'val : ((⟨(i : ℕ) + 1, hi⟩ : Fin N) : ℕ) = (i : ℕ) + 1 := rfl
  have hne : i ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin N) := by
    intro hc
    have := congrArg (Fin.val) hc
    omega
  have hfi : (Function.update (Function.update (id : Fin N → Fin N) i
      (⟨(i : ℕ) + 1, hi⟩ : Fin N)) (⟨(i : ℕ) + 1, hi⟩ : Fin N) b) i
      = (⟨(i : ℕ) + 1, hi⟩ : Fin N) := by
    rw [Function.update_of_ne hne, Function.update_self]
  have hfi' : (Function.update (Function.update (id : Fin N → Fin N) i
      (⟨(i : ℕ) + 1, hi⟩ : Fin N)) (⟨(i : ℕ) + 1, hi⟩ : Fin N) b) (⟨(i : ℕ) + 1, hi⟩ : Fin N)
      = b := Function.update_self _ _ _
  have hfo : ∀ ρ : Fin N, ρ ≠ i → ρ ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin N) →
      (Function.update (Function.update (id : Fin N → Fin N) i
        (⟨(i : ℕ) + 1, hi⟩ : Fin N)) (⟨(i : ℕ) + 1, hi⟩ : Fin N) b) ρ = ρ := by
    intro ρ h1 h2
    rw [Function.update_of_ne h2, Function.update_of_ne h1]
    rfl
  have hval : ∀ ρ c : Fin N, (ρ : ℕ) < (i : ℕ) + 2 → (c : ℕ) < (i : ℕ) + 2 →
      truncate ((i : ℕ) + 2) (L.submatrix (Function.update (Function.update
        (id : Fin N → Fin N) i (⟨(i : ℕ) + 1, hi⟩ : Fin N)) (⟨(i : ℕ) + 1, hi⟩ : Fin N) b) id) ρ c
      = L ((Function.update (Function.update (id : Fin N → Fin N) i
          (⟨(i : ℕ) + 1, hi⟩ : Fin N)) (⟨(i : ℕ) + 1, hi⟩ : Fin N) b) ρ) c := by
    intro ρ c h1 h2
    rw [truncate_apply_of_both h1 h2, Matrix.submatrix_apply, id_eq]
  have hout : ∀ ρ c : Fin N, (¬ ((ρ : ℕ) < (i : ℕ) + 2) ∨ ¬ ((c : ℕ) < (i : ℕ) + 2)) →
      truncate ((i : ℕ) + 2) (L.submatrix (Function.update (Function.update
        (id : Fin N → Fin N) i (⟨(i : ℕ) + 1, hi⟩ : Fin N)) (⟨(i : ℕ) + 1, hi⟩ : Fin N) b) id) ρ c
      = if ρ = c then 1 else 0 := by
    rintro ρ c (h | h)
    · rw [truncate_apply_of_not_left h]
    · rw [truncate_apply_of_not_right h]
  have hone : truncate ((i : ℕ) + 2) (L.submatrix (Function.update (Function.update
      (id : Fin N → Fin N) i (⟨(i : ℕ) + 1, hi⟩ : Fin N)) (⟨(i : ℕ) + 1, hi⟩ : Fin N) b) id)
      i (⟨(i : ℕ) + 1, hi⟩ : Fin N) = 1 := by
    rw [hval i _ (by omega) (by omega), hfi, hL.2]
  have hzero : ∀ ρ c : Fin N, (ρ : ℕ) < (c : ℕ) → ¬ (ρ = i ∧ c = (⟨(i : ℕ) + 1, hi⟩ : Fin N)) →
      truncate ((i : ℕ) + 2) (L.submatrix (Function.update (Function.update
        (id : Fin N → Fin N) i (⟨(i : ℕ) + 1, hi⟩ : Fin N)) (⟨(i : ℕ) + 1, hi⟩ : Fin N) b) id)
        ρ c = 0 := by
    intro ρ c hlt hnec
    have hrc : ρ ≠ c := fun hc => absurd (congrArg Fin.val hc) (ne_of_lt hlt)
    by_cases h1 : (ρ : ℕ) < (i : ℕ) + 2
    · by_cases h2 : (c : ℕ) < (i : ℕ) + 2
      · rw [hval ρ c h1 h2]
        by_cases hri : ρ = i
        · exfalso
          refine hnec ⟨hri, Fin.ext ?_⟩
          have hic : (i : ℕ) < (c : ℕ) := by
            have := congrArg Fin.val hri
            omega
          omega
        · by_cases hri' : ρ = (⟨(i : ℕ) + 1, hi⟩ : Fin N)
          · exfalso
            have := congrArg Fin.val hri'
            omega
          · rw [hfo ρ hri hri']
            exact hL.1 ρ c hlt
      · rw [hout ρ c (Or.inr h2), if_neg hrc]
    · rw [hout ρ c (Or.inl h1), if_neg hrc]
  have hdiag : ∀ ρ : Fin N, ρ ≠ i → ρ ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin N) →
      truncate ((i : ℕ) + 2) (L.submatrix (Function.update (Function.update
        (id : Fin N → Fin N) i (⟨(i : ℕ) + 1, hi⟩ : Fin N)) (⟨(i : ℕ) + 1, hi⟩ : Fin N) b) id)
        ρ ρ = 1 := by
    intro ρ h1 h2
    by_cases h : (ρ : ℕ) < (i : ℕ) + 2
    · rw [hval ρ ρ h h, hfo ρ h1 h2, hL.2]
    · rw [hout ρ ρ (Or.inl h), if_pos rfl]
  have hdet := det_of_almost_lowerTriangular (M := truncate ((i : ℕ) + 2)
    (L.submatrix (Function.update (Function.update (id : Fin N → Fin N) i
      (⟨(i : ℕ) + 1, hi⟩ : Fin N)) (⟨(i : ℕ) + 1, hi⟩ : Fin N) b) id)) (i := i)
    (i' := (⟨(i : ℕ) + 1, hi⟩ : Fin N)) rfl hone hzero hdiag
  rw [leadingMinorMat, hdet, hval i i (by omega) (by omega),
    hval (⟨(i : ℕ) + 1, hi⟩ : Fin N) (⟨(i : ℕ) + 1, hi⟩ : Fin N) (by omega) (by omega),
    hval (⟨(i : ℕ) + 1, hi⟩ : Fin N) i (by omega) (by omega), hfi, hfi']

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- The minor with prescribed rows and the first columns. -/
noncomputable def rowMinorPoly (N : ℕ) (k : Type*) [Field k] (f : Fin N → Fin N) (j : ℕ) :
    MvPolynomial (Fin N × Fin N) k :=
  (truncate j ((genericMatrix N k).submatrix f id)).det

theorem matEval_rowMinorPoly (f : Fin N → Fin N) (j : ℕ) (g : Matrix (Fin N) (Fin N) k) :
    matEval g (rowMinorPoly N k f j) = leadingMinorMat j (g.submatrix f id) := by
  classical
  have hmap : (truncate j ((genericMatrix N k).submatrix f id)).map
      (MvPolynomial.eval (fun ij : Fin N × Fin N => g ij.1 ij.2))
      = truncate j (g.submatrix f id) := by
    refine Matrix.ext fun r c => ?_
    by_cases h1 : (r : ℕ) < j
    · by_cases h2 : (c : ℕ) < j
      · simp [Matrix.map_apply, truncate_apply_of_both h1 h2, genericMatrix]
      · rw [Matrix.map_apply, truncate_apply_of_not_right h2, truncate_apply_of_not_right h2]
        by_cases h3 : r = c <;> simp [h3]
    · rw [Matrix.map_apply, truncate_apply_of_not_left h1, truncate_apply_of_not_left h1]
      by_cases h3 : r = c <;> simp [h3]
  rw [rowMinorPoly, leadingMinorMat, matEval, ← hmap, RingHom.map_det]
  rfl

theorem substRight_rowMinorPoly (f : Fin N → Fin N) (j : ℕ) {B : Matrix (Fin N) (Fin N) k}
    (hB : B.BlockTriangular id) :
    substRight B (rowMinorPoly N k f j)
      = MvPolynomial.C (minorChar j B) * rowMinorPoly N k f j := by
  refine matEval_injective fun g => ?_
  have hC : matEval g (MvPolynomial.C (minorChar j B)) = minorChar j B := by simp [matEval]
  rw [matEval_substRight, matEval_rowMinorPoly, matEval_mul, hC, matEval_rowMinorPoly,
    submatrix_mul_row, leadingMinorMat_mul_borel _ _ hB, minorChar, mul_comm]

theorem borelCharZ_indicator' (j : ℕ) (B : Matrix (Fin N) (Fin N) k) :
    borelCharZ (fun l : Fin N => if (l : ℕ) < j then (1 : ℤ) else 0) B = minorChar j B := by
  rw [borelCharZ, minorChar]
  refine Finset.prod_congr rfl fun l _ => ?_
  by_cases h : (l : ℕ) < j
  · rw [if_pos h, if_pos h, zpow_one]
  · rw [if_neg h, if_neg h, zpow_zero]

theorem algebraMap_rowMinorPoly_mem_flagSemiInv (f : Fin N → Fin N) (j : ℕ) :
    algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (rowMinorPoly N k f j)
      ∈ flagSemiInv N k (fun l : Fin N => if (l : ℕ) < j then (1 : ℤ) else 0) := by
  intro B hB
  rw [substRightAway_algebraMap, substRight_rowMinorPoly f j hB.1, map_mul, borelCharZ_indicator',
    Algebra.smul_def, IsScalarTower.algebraMap_apply k (MvPolynomial (Fin N × Fin N) k)
      (FlagLoc N k)]
  simp only [MvPolynomial.algebraMap_eq]

theorem coe_minorUnit_mem_flagSemiInv' (σ : Equiv.Perm (Fin N)) {j : ℕ} (hj : j ≤ N) :
    ((minorUnit (k := k) σ j hj : (FlagLoc N k)ˣ) : FlagLoc N k)
      ∈ flagSemiInv N k (fun l : Fin N => if (l : ℕ) < j then (1 : ℤ) else 0) := by
  intro B hB
  rw [substRightAway_coe_minorUnit hB, borelCharZ_indicator']

/-- **Ratios of minors at the same level are invariant.** -/
theorem ratio_mem_flagSemiInv_zero (f : Fin N → Fin N) {j : ℕ} (hj : j ≤ N) :
    algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (rowMinorPoly N k f j)
        * (((minorUnit (1 : Equiv.Perm (Fin N)) j hj)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)
      ∈ flagSemiInv N k (fun _ => 0) := by
  have h1 := algebraMap_rowMinorPoly_mem_flagSemiInv (k := k) f j
  have h2 := inv_mem_flagSemiInv (coe_minorUnit_mem_flagSemiInv' (k := k)
    (1 : Equiv.Perm (Fin N)) hj)
  have h3 := mul_mem_flagSemiInv h1 h2
  refine (flagSemiInv_congr ?_ _).mp h3
  funext l
  ring

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

theorem inv_minorUnit_mem_denomBounded {I : Finset (Equiv.Perm (Fin N))}
    {σ : Equiv.Perm (Fin N)} (hσ : σ ∈ I) {j : ℕ} (hj : j ≤ N) :
    (((minorUnit (k := k) σ j hj)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k) ∈ denomBounded N k I := by
  have h := (minorUnit_mem_denomStable (k := k) hσ hj).2 1 (one_mem_denomBounded _)
  rwa [one_mul] at h

/-- **Every leading minor except the exceptional one is invertible on the reflected cell.** -/
theorem inv_minorUnit_one_mem_denomBounded_swap {i : Fin N} (hi : (i : ℕ) + 1 < N) {j : ℕ}
    (hj : j ≤ N) (hji : j ≠ (i : ℕ) + 1) :
    (((minorUnit (k := k) (1 : Equiv.Perm (Fin N)) j hj)⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)
      ∈ denomBounded N k {swapNext i hi} := by
  have hone : (1 : Equiv.Perm (Fin N)) * swapNext i hi = swapNext i hi := one_mul _
  rcases Nat.lt_or_ge (i : ℕ) j with hcase | hcase
  · have hgt : (i : ℕ) + 1 < j := by omega
    have heq := minorUnit_mul_swapNext_of_gt (k := k) (1 : Equiv.Perm (Fin N)) hi hgt hj
    rw [hone] at heq
    have heq2 : minorUnit (k := k) (1 : Equiv.Perm (Fin N)) j hj
        = - minorUnit (swapNext i hi) j hj := by
      rw [heq, neg_neg]
    have hinv : ((minorUnit (k := k) (1 : Equiv.Perm (Fin N)) j hj)⁻¹ : (FlagLoc N k)ˣ)
        = -((minorUnit (swapNext i hi) j hj)⁻¹) := by
      rw [heq2]
      refine inv_eq_of_mul_eq_one_right ?_
      rw [neg_mul_neg, mul_inv_cancel]
    rw [hinv, Units.val_neg]
    exact Submodule.neg_mem _
      (inv_minorUnit_mem_denomBounded (Finset.mem_singleton_self _) hj)
  · have heq := minorUnit_mul_swapNext_of_le (k := k) (1 : Equiv.Perm (Fin N)) hi hcase hj
    rw [hone] at heq
    rw [← heq]
    exact inv_minorUnit_mem_denomBounded (Finset.mem_singleton_self _) hj

/-- The second base coordinate attached to a row below the step: the ratio of the `(i+2)`-minor
with rows `(0,…,i−1,i+1,b)` to the `(i+2)`-nd leading minor. -/
noncomputable def baseCoord (i : Fin N) (hi : (i : ℕ) + 1 < N) (b : Fin N) : FlagLoc N k :=
  algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k)
      (rowMinorPoly N k (Function.update (Function.update (id : Fin N → Fin N) i
        (⟨(i : ℕ) + 1, hi⟩ : Fin N)) (⟨(i : ℕ) + 1, hi⟩ : Fin N) b) ((i : ℕ) + 2))
    * (((minorUnit (1 : Equiv.Perm (Fin N)) ((i : ℕ) + 2) (by omega))⁻¹ : (FlagLoc N k)ˣ) :
        FlagLoc N k)

theorem baseCoord_mem_flagSemiInv (i : Fin N) (hi : (i : ℕ) + 1 < N) (b : Fin N) :
    baseCoord (k := k) i hi b ∈ flagSemiInv N k (fun _ => 0) :=
  ratio_mem_flagSemiInv_zero _ (by omega)

theorem baseCoord_mem_denomBounded_one (i : Fin N) (hi : (i : ℕ) + 1 < N) (b : Fin N) :
    baseCoord (k := k) i hi b ∈ denomBounded N k {(1 : Equiv.Perm (Fin N))} :=
  denomBounded_mul (algebraMap_mem_denomBounded _ _)
    (inv_minorUnit_mem_denomBounded (Finset.mem_singleton_self _) (by omega))

theorem baseCoord_mem_denomBounded_swap (i : Fin N) (hi : (i : ℕ) + 1 < N) (b : Fin N) :
    baseCoord (k := k) i hi b ∈ denomBounded N k {swapNext i hi} :=
  denomBounded_mul (algebraMap_mem_denomBounded _ _)
    (inv_minorUnit_one_mem_denomBounded_swap hi (by omega) (by omega))

/-- **The base coordinate is regular on both cells of the pair.** -/
theorem baseCoord_mem_cellSubalg (i : Fin N) (hi : (i : ℕ) + 1 < N) (b : Fin N) :
    baseCoord (k := k) i hi b ∈ cellSubalg N k {(1 : Equiv.Perm (Fin N))}
      ∧ baseCoord (k := k) i hi b ∈ cellSubalg N k {swapNext i hi} :=
  ⟨⟨baseCoord_mem_flagSemiInv i hi b, baseCoord_mem_denomBounded_one i hi b⟩,
    ⟨baseCoord_mem_flagSemiInv i hi b, baseCoord_mem_denomBounded_swap i hi b⟩⟩

/-- **The cell coordinates away from the step are regular on both cells.** -/
theorem cellCoord_mem_cellSubalg_swap {i : Fin N} (hi : (i : ℕ) + 1 < N) (r j : Fin N)
    (hj : j ≠ i) : cellCoord (k := k) r j ∈ cellSubalg N k {swapNext i hi} := by
  refine ⟨cellCoord_mem_flagSemiInv r j, ?_⟩
  refine denomBounded_mul (algebraMap_mem_denomBounded _ _) ?_
  refine inv_minorUnit_one_mem_denomBounded_swap hi j.isLt ?_
  intro hc
  exact hj (Fin.ext (by omega))

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

theorem flagEval_baseCoord {L : Matrix (Fin N) (Fin N) k} (hL : IsLowerUni L)
    (hLT : matEval L (totalDenom N k) ≠ 0) (i : Fin N) (hi : (i : ℕ) + 1 < N) (b : Fin N) :
    flagEval hLT (baseCoord i hi b)
      = L (⟨(i : ℕ) + 1, hi⟩ : Fin N) i * L b (⟨(i : ℕ) + 1, hi⟩ : Fin N) - L b i := by
  have hsub : L.submatrix (⇑(1 : Equiv.Perm (Fin N))) id = L := by
    ext r s
    rfl
  rw [baseCoord, map_mul, flagEval_algebraMap, matEval_rowMinorPoly,
    leadingMinorMat_pairUpdate_of_isLowerUni hL, flagEval_units_inv, coe_minorUnit,
    flagEval_algebraMap, matEval_minorPolyAt, hsub, leadingMinorMat_of_isLowerUni hL, inv_one,
    mul_one]

/-- **The base coordinate in terms of the chart coordinates.** -/
theorem baseCoord_eq (i : Fin N) (hi : (i : ℕ) + 1 < N) (b : Fin N) :
    baseCoord (k := k) i hi b
      = cellCoord (⟨(i : ℕ) + 1, hi⟩ : Fin N) i * cellCoord b (⟨(i : ℕ) + 1, hi⟩ : Fin N)
        - cellCoord b i := by
  refine eq_of_flagEval_lowerUni_eq (baseCoord_mem_flagSemiInv i hi b) ?_ fun L hL hLT => ?_
  · exact Submodule.sub_mem _ (mul_mem_flagSemiInv_zero (cellCoord_mem_flagSemiInv _ _)
      (cellCoord_mem_flagSemiInv _ _)) (cellCoord_mem_flagSemiInv _ _)
  · rw [flagEval_baseCoord hL hLT, map_sub, map_mul, flagEval_cellCoord hL hLT,
      flagEval_cellCoord hL hLT, flagEval_cellCoord hL hLT]

/-- **Every cell coordinate is the fibre coordinate times a chart function plus a function regular
on both cells.** -/
theorem cellCoord_eq_fibre_mul_add {i : Fin N} (hi : (i : ℕ) + 1 < N) (r j : Fin N) :
    ∃ y : FlagLoc N k, y ∈ cellSubalg N k {(1 : Equiv.Perm (Fin N))}
      ∧ y ∈ cellSubalg N k {swapNext i hi}
      ∧ ∃ w : FlagLoc N k, w ∈ cellSubalg N k {(1 : Equiv.Perm (Fin N))}
        ∧ cellCoord (k := k) r j
          = cellCoord (⟨(i : ℕ) + 1, hi⟩ : Fin N) i * w + y := by
  classical
  by_cases hji : j = i
  · subst hji
    refine ⟨-baseCoord j hi r, Submodule.neg_mem _ (baseCoord_mem_cellSubalg j hi r).1,
      Submodule.neg_mem _ (baseCoord_mem_cellSubalg j hi r).2,
      cellCoord r (⟨(j : ℕ) + 1, hi⟩ : Fin N), cellCoord_mem_cellSections _ _, ?_⟩
    rw [baseCoord_eq]
    ring
  · exact ⟨cellCoord r j, cellCoord_mem_cellSections r j,
      cellCoord_mem_cellSubalg_swap hi r j hji, 0, Submodule.zero_mem _, by rw [mul_zero, zero_add]⟩

end GaloisForLFunctions.HTGeometry.BorelWeil
