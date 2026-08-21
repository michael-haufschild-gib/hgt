import GaloisForLFunctions.HTGeometry.BorelWeil.FlagDetTwist
import GaloisForLFunctions.HTGeometry.BorelWeil.LUDecomposition
import GaloisForLFunctions.HTGeometry.BorelWeil.ColumnScaling

/-!
# Evaluating sections on the big cell

A section of `L_λ` lives in the localization of the polynomial ring at the product of the cell
equations, so it can be evaluated at any matrix where that product does not vanish.  Evaluation
intertwines the right Borel translation with matrix multiplication, and the `LU` factorization says
that any such matrix is a lower unitriangular matrix times a Borel one.  Consequently a section is
determined by its values on the lower unitriangular matrices: the big cell coordinates.

This is the coordinate system in which the `ℙ¹`-fibrations `G/B → G/P_i` become explicit.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.flagEval` — evaluation of a section at a matrix.

## Main results

* `flagEval_substRightAway` — evaluation intertwines translation with multiplication.
* `flagEval_of_mem_flagSemiInv` — the semi-invariance seen through evaluation.
* `eq_zero_of_flagEval_lowerUni_eq_zero` — a section vanishing on the big cell vanishes.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- Evaluation of a section at a matrix where the cover equation does not vanish. -/
noncomputable def flagEval {g : Matrix (Fin N) (Fin N) k}
    (hg : matEval g (totalDenom N k) ≠ 0) : FlagLoc N k →+* k :=
  IsLocalization.Away.lift (S := FlagLoc N k) (totalDenom N k) (g := matEvalHom g) hg.isUnit

@[simp] theorem flagEval_algebraMap {g : Matrix (Fin N) (Fin N) k}
    (hg : matEval g (totalDenom N k) ≠ 0) (p : MvPolynomial (Fin N × Fin N) k) :
    flagEval hg (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) p) = matEval g p := by
  rw [flagEval, IsLocalization.Away.lift_eq]
  rfl

theorem flagEval_algebraMap_field {g : Matrix (Fin N) (Fin N) k}
    (hg : matEval g (totalDenom N k) ≠ 0) (c : k) :
    flagEval hg (algebraMap k (FlagLoc N k) c) = c := by
  rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k),
    flagEval_algebraMap]
  simp [matEval, MvPolynomial.algebraMap_eq]

theorem flagEval_smul {g : Matrix (Fin N) (Fin N) k} (hg : matEval g (totalDenom N k) ≠ 0)
    (c : k) (x : FlagLoc N k) : flagEval hg (c • x) = c * flagEval hg x := by
  rw [Algebra.smul_def, map_mul, flagEval_algebraMap_field]

/-- The cover equation is nonzero at a Borel translate exactly when it is at the matrix. -/
theorem matEval_totalDenom_mul {g B : Matrix (Fin N) (Fin N) k} (hB : IsBorelMat B) :
    matEval (g * B) (totalDenom N k)
      = (∏ σ : Equiv.Perm (Fin N), cellChar N k σ B) * matEval g (totalDenom N k) := by
  have h := substRight_totalDenom (k := k) hB.1
  have h2 := congrArg (matEval g) h
  rw [matEval_substRight, matEval_mul] at h2
  rw [h2]
  congr 1
  simp [matEval]

theorem matEval_totalDenom_mul_ne_zero {g B : Matrix (Fin N) (Fin N) k} (hB : IsBorelMat B)
    (hg : matEval g (totalDenom N k) ≠ 0) : matEval (g * B) (totalDenom N k) ≠ 0 := by
  rw [matEval_totalDenom_mul hB]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun σ _ => cellChar_ne_zero σ hB) hg

/-- **Evaluation intertwines right translation with matrix multiplication.** -/
theorem flagEval_substRightAway {B : Matrix (Fin N) (Fin N) k} (hB : IsBorelMat B)
    {g : Matrix (Fin N) (Fin N) k} (hg : matEval g (totalDenom N k) ≠ 0) (x : FlagLoc N k) :
    flagEval hg (substRightAway hB x)
      = flagEval (matEval_totalDenom_mul_ne_zero hB hg) x := by
  have hext : (flagEval hg).comp (substRightAway hB)
      = flagEval (matEval_totalDenom_mul_ne_zero hB hg) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (totalDenom N k)) (RingHom.ext fun p => ?_)
    show flagEval hg (substRightAway hB (algebraMap _ _ p))
      = flagEval (matEval_totalDenom_mul_ne_zero hB hg) (algebraMap _ _ p)
    rw [substRightAway_algebraMap, flagEval_algebraMap, flagEval_algebraMap, matEval_substRight]
  exact congrFun (congrArg (fun f : FlagLoc N k →+* k => (f : FlagLoc N k → k)) hext) x

/-- **Semi-invariance seen through evaluation.** -/
theorem flagEval_of_mem_flagSemiInv {lam : Fin N → ℤ} {x : FlagLoc N k}
    (hx : x ∈ flagSemiInv N k lam) {B : Matrix (Fin N) (Fin N) k} (hB : IsBorelMat B)
    {g : Matrix (Fin N) (Fin N) k} (hg : matEval g (totalDenom N k) ≠ 0) :
    flagEval (matEval_totalDenom_mul_ne_zero hB hg) x = borelCharZ lam B * flagEval hg x := by
  rw [← flagEval_substRightAway hB hg, hx B hB, flagEval_smul]

/-- The cell equations of the identity cell are the leading minors, so a matrix where the cover
equation is nonzero admits an `LU` factorization. -/
theorem exists_lu_of_matEval_totalDenom_ne_zero {g : Matrix (Fin N) (Fin N) k}
    (hg : matEval g (totalDenom N k) ≠ 0) :
    ∃ L B : Matrix (Fin N) (Fin N) k, IsLowerUni L ∧ IsBorelMat B ∧ g = L * B := by
  classical
  refine exists_lu_of_leadingMinor_ne_zero g fun j => ?_
  intro hzero
  refine hg ?_
  have hdvd : cellDenomPoly N k (1 : Equiv.Perm (Fin N)) ∣ totalDenom N k :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ (1 : Equiv.Perm (Fin N)))
  obtain ⟨s, hs⟩ := hdvd
  have hcell : matEval g (cellDenomPoly N k (1 : Equiv.Perm (Fin N))) = 0 := by
    rw [cellDenomPoly, matEval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    rw [matEval_minorPolyAt]
    have hsub : g.submatrix (⇑(1 : Equiv.Perm (Fin N))) id = g := by
      ext r s
      rfl
    rw [hsub]
    exact hzero
  rw [hs, matEval_mul, hcell, zero_mul]

/-- **A section vanishing on the big cell vanishes.**  Semi-invariant sections are determined by
their restriction to the lower unitriangular matrices. -/
theorem eq_zero_of_flagEval_lowerUni_eq_zero {lam : Fin N → ℤ} {x : FlagLoc N k}
    (hx : x ∈ flagSemiInv N k lam)
    (h : ∀ (L : Matrix (Fin N) (Fin N) k), IsLowerUni L →
      ∀ hL : matEval L (totalDenom N k) ≠ 0, flagEval hL x = 0) : x = 0 := by
  classical
  have hall : ∀ (g : Matrix (Fin N) (Fin N) k) (hg : matEval g (totalDenom N k) ≠ 0),
      flagEval hg x = 0 := by
    intro g hg
    obtain ⟨L, B, hL, hB, rfl⟩ := exists_lu_of_matEval_totalDenom_ne_zero hg
    have hLne : matEval L (totalDenom N k) ≠ 0 := by
      intro hzero
      exact hg (by rw [matEval_totalDenom_mul hB, hzero, mul_zero])
    have := flagEval_of_mem_flagSemiInv hx hB hLne
    rw [h L hL hLne, mul_zero] at this
    have hcongr : matEval_totalDenom_mul_ne_zero hB hLne = hg := rfl
    rw [← this]
  obtain ⟨⟨p, c⟩, hpc⟩ := IsLocalization.surj (M := Submonoid.powers (totalDenom N k)) x
  have hp : p = 0 := by
    have hzero : ∀ g : Matrix (Fin N) (Fin N) k,
        matEval g (p * totalDenom N k) = matEval g (0 : MvPolynomial (Fin N × Fin N) k) := by
      intro g
      by_cases hg : matEval g (totalDenom N k) = 0
      · rw [matEval_mul, hg, mul_zero]
        simp [matEval]
      · have := congrArg (flagEval hg) hpc
        rw [map_mul, flagEval_algebraMap, flagEval_algebraMap, hall g hg, zero_mul] at this
        rw [matEval_mul, ← this, zero_mul]
        simp [matEval]
    have hmul : p * totalDenom N k = 0 := matEval_injective hzero
    exact (mul_eq_zero.mp hmul).resolve_right totalDenom_ne_zero
  rw [hp, map_zero] at hpc
  obtain ⟨n, hn⟩ := c.2
  have hc : algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (c : _) ≠ 0 := by
    rw [← hn]
    exact fun hzero => (pow_ne_zero n totalDenom_ne_zero)
      (algebraMap_flagLoc_inj (by rw [hzero, map_zero]))
  exact (mul_eq_zero.mp hpc).resolve_right hc

end GaloisForLFunctions.HTGeometry.BorelWeil
