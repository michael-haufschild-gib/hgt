import GaloisForLFunctions.HTGeometry.BorelWeil.RankTwoBott

/-!
# The affine coordinate is transcendental

Evaluating at the explicit lower unitriangular matrices `[[1,0],[c,1]]` sends the affine coordinate
of the big cell to `c`, and the cover equation is nonzero there for every `c ≠ 0`.  So a polynomial
relation satisfied by the coordinate has infinitely many roots and therefore vanishes: the chart
ring is a genuine polynomial ring, and the Laurent monomials are linearly independent.

## Main results

* `matEval_totalDenom_lowerTwo` — the cover equation is nonzero on those matrices.
* `aeval_tCoord_injective` — the affine coordinate is transcendental.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- Evaluation at a point of the big cell, as a `k`-algebra map. -/
noncomputable def flagEvalAlg {g : Matrix (Fin N) (Fin N) k}
    (hg : matEval g (totalDenom N k) ≠ 0) : FlagLoc N k →ₐ[k] k where
  toFun := flagEval hg
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' r := flagEval_algebraMap_field hg r

@[simp] theorem flagEvalAlg_apply {g : Matrix (Fin N) (Fin N) k}
    (hg : matEval g (totalDenom N k) ≠ 0) (x : FlagLoc N k) :
    flagEvalAlg hg x = flagEval hg x := rfl

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {k : Type*} [Field k] [Infinite k]

/-- The lower unitriangular `2 × 2` matrix with off-diagonal entry `c`. -/
noncomputable def lowerTwo (c : k) : Matrix (Fin 2) (Fin 2) k :=
  lowerMat (Matrix.of fun _ _ => c)

theorem isLowerUni_lowerTwo (c : k) : IsLowerUni (lowerTwo c) :=
  isLowerUni_lowerMat _

theorem lowerTwo_apply (c : k) : lowerTwo c (1 : Fin 2) (0 : Fin 2) = c := by
  rw [lowerTwo, lowerMat]
  simp only [Matrix.of_apply]
  rw [if_pos (by norm_num : ((0 : Fin 2) : ℕ) < ((1 : Fin 2) : ℕ))]

theorem totalDenom_two_eq :
    totalDenom 2 k = cellDenomPoly 2 k 1 * cellDenomPoly 2 k swapTwo := by
  classical
  rw [totalDenom, univ_perm_fin_two, Finset.prod_pair one_ne_swapTwo]

theorem matEval_totalDenom_lowerTwo {c : k} (hc : c ≠ 0) :
    matEval (lowerTwo c) (totalDenom 2 k) ≠ 0 := by
  obtain ⟨e, he, heq⟩ := exists_matEval_cellDenomPoly_swapNext (k := k) zero_succ_lt_two
  rw [totalDenom_two_eq, matEval_mul,
    matEval_cellDenomPoly_one_of_isLowerUni (isLowerUni_lowerTwo c), one_mul]
  have hswap : cellDenomPoly 2 k swapTwo = cellDenomPoly 2 k (swapNext (0 : Fin 2) zero_succ_lt_two) :=
    rfl
  rw [hswap, heq (lowerTwo c) (isLowerUni_lowerTwo c)]
  have hidx : (⟨((0 : Fin 2) : ℕ) + 1, zero_succ_lt_two⟩ : Fin 2) = (1 : Fin 2) := rfl
  rw [hidx, lowerTwo_apply]
  exact mul_ne_zero he hc

theorem flagEval_tCoord_lowerTwo {c : k} (hc : c ≠ 0) :
    flagEval (matEval_totalDenom_lowerTwo hc) (tCoord k) = c := by
  have hidx : (⟨((0 : Fin 2) : ℕ) + 1, zero_succ_lt_two⟩ : Fin 2) = (1 : Fin 2) := rfl
  rw [tCoord_eq_cellCoord, hidx,
    flagEval_cellCoord (isLowerUni_lowerTwo c) (matEval_totalDenom_lowerTwo hc), lowerTwo_apply]

/-- **The affine coordinate of the big cell is transcendental over `k`.** -/
theorem aeval_tCoord_eq_zero {q : Polynomial k} (hq : Polynomial.aeval (tCoord k) q = 0) :
    q = 0 := by
  classical
  refine Polynomial.eq_zero_of_infinite_isRoot q ?_
  have hsub : {c : k | c ≠ 0} ⊆ {c : k | q.IsRoot c} := by
    intro c hc
    have hcz : c ≠ 0 := hc
    have hval : Polynomial.aeval (flagEvalAlg (matEval_totalDenom_lowerTwo hcz) (tCoord k)) q
        = flagEvalAlg (matEval_totalDenom_lowerTwo hcz) (Polynomial.aeval (tCoord k) q) :=
      Polynomial.aeval_algHom_apply _ _ _
    rw [hq, map_zero, flagEvalAlg_apply, flagEval_tCoord_lowerTwo hcz] at hval
    show q.eval c = 0
    rw [← Polynomial.coe_aeval_eq_eval]
    exact hval
  refine Set.Infinite.mono hsub ?_
  have hcompl : {c : k | c ≠ 0} = ({0} : Set k)ᶜ := by
    ext c
    simp [Set.mem_compl_iff]
  rw [hcompl]
  exact Set.Finite.infinite_compl (Set.finite_singleton 0)

theorem aeval_tCoord_injective :
    Function.Injective (Polynomial.aeval (tCoord k) : Polynomial k → FlagLoc 2 k) := by
  intro q r hqr
  have : Polynomial.aeval (tCoord k) (q - r) = 0 := by
    rw [map_sub, hqr, sub_self]
  exact sub_eq_zero.mp (aeval_tCoord_eq_zero this)

end GaloisForLFunctions.HTGeometry.BorelWeil
