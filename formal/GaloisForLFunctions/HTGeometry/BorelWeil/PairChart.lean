import GaloisForLFunctions.HTGeometry.BorelWeil.FibreCoordinate

/-!
# The chart of a coset pair

Restricted to the big cell, the cell equation of `s_i` is — up to a nonzero scalar — the coordinate
along the simple root, because all of its leading minors restrict to `±1` except the exceptional one,
which restricts to that coordinate.  So the sections over the intersection of the two cells of a
coset pair are the chart functions with denominators a power of the fibre coordinate: the
intersection is the big cell with the zero locus of the fibre coordinate removed.

## Main results

* `cellCoordAlg_lowerSubst_cellDenomPoly_one` — the identity cell equation restricts to `1`.
* `exists_smul_cellCoordAlg_lowerSubst_swapNext` — the reflected cell equation restricts to the
  fibre coordinate up to a scalar.
* `exists_cellCoordAlg_fibre_denom` — the chart description of the pair intersection.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- Two weight-zero sections with the same restriction to the big cell agree. -/
theorem eq_of_flagEval_lowerUni_eq {x y : FlagLoc N k}
    (hx : x ∈ flagSemiInv N k (fun _ => 0)) (hy : y ∈ flagSemiInv N k (fun _ => 0))
    (h : ∀ (L : Matrix (Fin N) (Fin N) k), IsLowerUni L →
      ∀ hL : matEval L (totalDenom N k) ≠ 0, flagEval hL x = flagEval hL y) : x = y := by
  have hdiff : x - y = 0 := by
    refine eq_zero_of_flagEval_lowerUni_eq_zero (lam := fun _ => 0)
      (Submodule.sub_mem _ hx hy) ?_
    intro L hL hLT
    rw [map_sub, h L hL hLT, sub_self]
  exact sub_eq_zero.mp hdiff

theorem cellCoordAlg_lowerSubst_cellDenomPoly_one :
    cellCoordAlg (lowerSubst (cellDenomPoly N k (1 : Equiv.Perm (Fin N)))) = (1 : FlagLoc N k) := by
  refine eq_of_flagEval_lowerUni_eq (cellCoordAlg_mem_cellSections _).1 one_mem_flagSemiInv_zero
    fun L hL hLT => ?_
  rw [flagEval_cellCoordAlg_lowerSubst hL hLT, matEval_cellDenomPoly_one_of_isLowerUni hL, map_one]

/-- **The reflected cell equation restricts to the fibre coordinate, up to a scalar.** -/
theorem exists_smul_cellCoordAlg_lowerSubst_swapNext {i : Fin N} (hi : (i : ℕ) + 1 < N) :
    ∃ c : k, c ≠ 0 ∧
      cellCoordAlg (lowerSubst (cellDenomPoly N k (swapNext i hi)))
        = c • cellCoord (⟨(i : ℕ) + 1, hi⟩ : Fin N) i := by
  classical
  refine ⟨∏ j ∈ Finset.univ.erase i, (if (j : ℕ) < (i : ℕ) then (1 : k) else -1), ?_, ?_⟩
  · refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    by_cases h : (j : ℕ) < (i : ℕ)
    · rw [if_pos h]; exact one_ne_zero
    · rw [if_neg h]; exact neg_ne_zero.mpr one_ne_zero
  · refine eq_of_flagEval_lowerUni_eq (cellCoordAlg_mem_cellSections _).1
      (Submodule.smul_mem _ _ (cellCoord_mem_flagSemiInv _ _)) fun L hL hLT => ?_
    have hsub : L.submatrix (⇑(1 : Equiv.Perm (Fin N))) id = L := by
      ext r s
      rfl
    have hone : (1 : Equiv.Perm (Fin N)) * swapNext i hi = swapNext i hi := one_mul _
    have hminor : ∀ j : Fin N,
        matEval L (minorPolyAt N k (swapNext i hi) ((j : ℕ) + 1))
          = (if (j : ℕ) < (i : ℕ) then (1 : k) else if j = i then L (⟨(i : ℕ) + 1, hi⟩) i else -1) := by
      intro j
      by_cases h1 : (j : ℕ) < (i : ℕ)
      · rw [if_pos h1, ← hone, minorPolyAt_mul_swapNext_of_le (1 : Equiv.Perm (Fin N)) hi
          (by omega : (j : ℕ) + 1 ≤ (i : ℕ)), matEval_minorPolyAt, hsub,
          leadingMinorMat_of_isLowerUni hL]
      · rw [if_neg h1]
        by_cases h2 : j = i
        · rw [if_pos h2, h2, ← borderPoly_succ_eq_minorPolyAt_swapNext hi, matEval_borderPoly,
            leadingMinorMat_update_of_isLowerUni hL]
        · have h3 : (i : ℕ) + 1 < (j : ℕ) + 1 := by
            have : (i : ℕ) ≠ (j : ℕ) := fun hc => h2 (Fin.ext hc.symm)
            omega
          rw [if_neg h2, ← hone, minorPolyAt_mul_swapNext_of_gt (1 : Equiv.Perm (Fin N)) hi h3,
            ← matEvalHom_apply, map_neg, matEvalHom_apply, matEval_minorPolyAt, hsub,
            leadingMinorMat_of_isLowerUni hL]
    rw [flagEval_cellCoordAlg_lowerSubst hL hLT, flagEval_smul, flagEval_cellCoord hL hLT,
      cellDenomPoly, matEval_prod]
    rw [Finset.prod_congr rfl fun j (_ : j ∈ Finset.univ) => hminor j]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), if_neg (by omega : ¬ ((i : ℕ) < (i : ℕ))),
      if_pos rfl, mul_comm (L (⟨(i : ℕ) + 1, hi⟩ : Fin N) i)]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    by_cases h : (j : ℕ) < (i : ℕ)
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, if_neg (Finset.mem_erase.mp hj).1]

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

theorem swapNext_ne_one {i : Fin N} (hi : (i : ℕ) + 1 < N) :
    (1 : Equiv.Perm (Fin N)) ≠ swapNext i hi := by
  intro hc
  have h := congrArg (fun w : Equiv.Perm (Fin N) => w i) hc
  simp only [Equiv.Perm.coe_one, id_eq] at h
  rw [swapNext, Equiv.swap_apply_left] at h
  have h2 := congrArg (Fin.val) h
  simp at h2

theorem denomOf_pair {i : Fin N} (hi : (i : ℕ) + 1 < N) :
    denomOf N k ({1, swapNext i hi} : Finset (Equiv.Perm (Fin N)))
      = cellDenomPoly N k 1 * cellDenomPoly N k (swapNext i hi) := by
  rw [denomOf, Finset.prod_pair (swapNext_ne_one hi)]

/-- **The chart description of the sections over the intersection of a coset pair.**  They are the
chart functions with denominators a power of the fibre coordinate. -/
theorem exists_cellCoordAlg_fibre_denom {i : Fin N} (hi : (i : ℕ) + 1 < N) {x : FlagLoc N k}
    (hx : x ∈ cellSections N k ({1, swapNext i hi} : Finset (Equiv.Perm (Fin N))) (fun _ => 0)) :
    ∃ (m : ℕ) (p : MvPolynomial (Fin N × Fin N) k),
      x * (cellCoord (⟨(i : ℕ) + 1, hi⟩ : Fin N) i) ^ m = cellCoordAlg p := by
  classical
  obtain ⟨m, p, hp⟩ := exists_cellCoordAlg_denom hx
  obtain ⟨c, hc, hceq⟩ := exists_smul_cellCoordAlg_lowerSubst_swapNext (k := k) hi
  have hQ : cellCoordAlg (lowerSubst (denomOf N k ({1, swapNext i hi} : Finset _)))
      = c • cellCoord (k := k) (⟨(i : ℕ) + 1, hi⟩ : Fin N) i := by
    rw [denomOf_pair, map_mul, map_mul, cellCoordAlg_lowerSubst_cellDenomPoly_one, one_mul, hceq]
  rw [hQ, smul_pow, mul_smul_comm] at hp
  refine ⟨m, (c ^ m)⁻¹ • p, ?_⟩
  rw [map_smul, ← hp, smul_smul, inv_mul_cancel₀ (pow_ne_zero m hc), one_smul]

theorem isUnit_cellCoord_succ {i : Fin N} (hi : (i : ℕ) + 1 < N) :
    IsUnit (cellCoord (k := k) (⟨(i : ℕ) + 1, hi⟩ : Fin N) i) := by
  rw [cellCoord_succ_eq_fibreCoord_inv hi]
  exact Units.isUnit _

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- **The reflected cell equation on a lower unitriangular matrix is a scalar times the entry along
the simple root.** -/
theorem exists_matEval_cellDenomPoly_swapNext {i : Fin N} (hi : (i : ℕ) + 1 < N) :
    ∃ c : k, c ≠ 0 ∧ ∀ L : Matrix (Fin N) (Fin N) k, IsLowerUni L →
      matEval L (cellDenomPoly N k (swapNext i hi)) = c * L (⟨(i : ℕ) + 1, hi⟩) i := by
  classical
  refine ⟨∏ j ∈ Finset.univ.erase i, (if (j : ℕ) < (i : ℕ) then (1 : k) else -1), ?_, ?_⟩
  · refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    by_cases h : (j : ℕ) < (i : ℕ)
    · rw [if_pos h]; exact one_ne_zero
    · rw [if_neg h]; exact neg_ne_zero.mpr one_ne_zero
  · intro L hL
    have hsub : L.submatrix (⇑(1 : Equiv.Perm (Fin N))) id = L := by
      ext r s
      rfl
    have hone : (1 : Equiv.Perm (Fin N)) * swapNext i hi = swapNext i hi := one_mul _
    have hminor : ∀ j : Fin N,
        matEval L (minorPolyAt N k (swapNext i hi) ((j : ℕ) + 1))
          = (if (j : ℕ) < (i : ℕ) then (1 : k)
              else if j = i then L (⟨(i : ℕ) + 1, hi⟩) i else -1) := by
      intro j
      by_cases h1 : (j : ℕ) < (i : ℕ)
      · rw [if_pos h1, ← hone, minorPolyAt_mul_swapNext_of_le (1 : Equiv.Perm (Fin N)) hi
          (by omega : (j : ℕ) + 1 ≤ (i : ℕ)), matEval_minorPolyAt, hsub,
          leadingMinorMat_of_isLowerUni hL]
      · rw [if_neg h1]
        by_cases h2 : j = i
        · rw [if_pos h2, h2, ← borderPoly_succ_eq_minorPolyAt_swapNext hi, matEval_borderPoly,
            leadingMinorMat_update_of_isLowerUni hL]
        · have h3 : (i : ℕ) + 1 < (j : ℕ) + 1 := by
            have : (i : ℕ) ≠ (j : ℕ) := fun hc => h2 (Fin.ext hc.symm)
            omega
          rw [if_neg h2, ← hone, minorPolyAt_mul_swapNext_of_gt (1 : Equiv.Perm (Fin N)) hi h3,
            ← matEvalHom_apply, map_neg, matEvalHom_apply, matEval_minorPolyAt, hsub,
            leadingMinorMat_of_isLowerUni hL]
    rw [cellDenomPoly, matEval_prod,
      Finset.prod_congr rfl fun j (_ : j ∈ Finset.univ) => hminor j,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), if_neg (by omega : ¬ ((i : ℕ) < (i : ℕ))),
      if_pos rfl, mul_comm (L (⟨(i : ℕ) + 1, hi⟩ : Fin N) i)]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    by_cases h : (j : ℕ) < (i : ℕ)
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, if_neg (Finset.mem_erase.mp hj).1]

end GaloisForLFunctions.HTGeometry.BorelWeil
