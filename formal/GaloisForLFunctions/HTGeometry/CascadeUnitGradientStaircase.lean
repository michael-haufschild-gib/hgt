import GaloisForLFunctions.HTGeometry.TowerGradientDegree
import GaloisForLFunctions.HTGeometry.CascadeFieldWeightedDegree
import GaloisForLFunctions.HTGeometry.DegreeDeterminantNonCancellation

/-!
# Tower-gradient noncancellation under lower-degree unit perturbations

Suppose normalized logarithmic states have the form `Pₖ u`, where `Pₖ` is the product of the first
`k` cascade coordinates and `u - 1` has strictly negative weighted degree.  Then `u` has degree
zero, its coordinate derivative has degree strictly below the derivative of `Pₖ`, and the gradient
of `Pₖ u` has the same staircase profile as the gradient of `Pₖ`.

The reversal assignment is therefore the unique maximal determinant term.  This module packages
the complete last step from normalized-unit estimates to a nonzero chain-gradient determinant.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-- A perturbation strictly below `1` has degree-zero sum with `1`. -/
theorem cascadeDeg_eq_zero_of_sub_one_lt_zero (w : ℕ → ℕ) {u : CascadeField}
    (hu : cascadeDeg w (u - 1) < (0 : WithBot ℤ)) :
    cascadeDeg w u = 0 := by
  have heq : u = 1 + (u - 1) := by ring
  rw [heq]
  have hone : cascadeDeg w (1 : CascadeField) = 0 := (isDegree_cascadeDeg w).map_one
  have hu' : cascadeDeg w (u - 1) < cascadeDeg w (1 : CascadeField) := by
    simpa only [hone] using hu
  rw [(isDegree_cascadeDeg w).map_add_of_lt hu', hone]

/-- The derivative of a normalized unit lies strictly below the negative coordinate weight. -/
theorem cascadeDeg_fpderiv_lt_neg_weight_of_sub_one_lt_zero
    (w : ℕ → ℕ) (j : ℕ) {u : CascadeField}
    (hu : cascadeDeg w (u - 1) < (0 : WithBot ℤ)) :
    cascadeDeg w (fpderiv j u) < ((-(w j : ℤ) : ℤ) : WithBot ℤ) := by
  have hder : fpderiv j u = fpderiv j (u - 1) := by
    rw [map_sub, Derivation.map_one_eq_zero, sub_zero]
  rw [hder]
  have hle := cascadeDeg_fpderiv_add_le w j (u - 1)
  have hsum : cascadeDeg w (fpderiv j (u - 1)) + (((w j : ℤ) : ℤ) : WithBot ℤ)
      < (0 : WithBot ℤ) := lt_of_le_of_lt hle hu
  by_cases hd0 : fpderiv j (u - 1) = 0
  · rw [hd0, ((isDegree_cascadeDeg w).eq_bot 0).mpr rfl]
    exact WithBot.bot_lt_coe _
  · have hsumZ : degZ (cascadeDeg w) (fpderiv j (u - 1)) + (w j : ℤ) < 0 := by
      rw [← coe_degZ (isDegree_cascadeDeg w) hd0] at hsum
      exact_mod_cast hsum
    rw [← coe_degZ (isDegree_cascadeDeg w) hd0, WithBot.coe_lt_coe]
    omega

/-- A tower monomial multiplied by a degree-zero unit. -/
noncomputable def towerUnitState (k : ℕ) (u : CascadeField) : CascadeField :=
  algebraMap (MvPolynomial ℕ ℂ) CascadeField (towerMonomial k) * u

/-- Error term in a differentiated tower-unit state is strictly below its model degree. -/
theorem cascadeDeg_towerMonomial_mul_fpderiv_lt
    (w : ℕ → ℕ) (k j : ℕ) {u : CascadeField}
    (hu : cascadeDeg w (u - 1) < (0 : WithBot ℤ)) :
    cascadeDeg w
        (algebraMap (MvPolynomial ℕ ℂ) CascadeField (towerMonomial k) * fpderiv j u)
      < (((towerWeight w k - (w j : ℤ) : ℤ)) : WithBot ℤ) := by
  have hdu := cascadeDeg_fpderiv_lt_neg_weight_of_sub_one_lt_zero w j hu
  by_cases hd0 : fpderiv j u = 0
  · rw [hd0, mul_zero, ((isDegree_cascadeDeg w).eq_bot 0).mpr rfl]
    exact WithBot.bot_lt_coe _
  · have hduZ : degZ (cascadeDeg w) (fpderiv j u) < -(w j : ℤ) := by
      rw [← coe_degZ (isDegree_cascadeDeg w) hd0, WithBot.coe_lt_coe] at hdu
      exact hdu
    rw [(isDegree_cascadeDeg w).map_mul, cascadeDeg_algebraMap, wdeg_towerMonomial,
      ← coe_degZ (isDegree_cascadeDeg w) hd0, ← WithBot.coe_add, WithBot.coe_lt_coe]
    omega

/-- On an active coordinate, the perturbed gradient has the exact tower-monomial degree. -/
theorem cascadeDeg_fpderiv_towerUnitState_eq
    (w : ℕ → ℕ) {k j : ℕ} {u : CascadeField}
    (hj : j ∈ Finset.Icc 1 k)
    (hu : cascadeDeg w (u - 1) < (0 : WithBot ℤ)) :
    cascadeDeg w (fpderiv j (towerUnitState k u)) =
      (((towerWeight w k - (w j : ℤ) : ℤ)) : WithBot ℤ) := by
  rw [towerUnitState, Derivation.leibniz, fpderiv_algebraMap_cascadeFieldWeightedDegree]
  simp only [smul_eq_mul]
  have hu0 := cascadeDeg_eq_zero_of_sub_one_lt_zero w hu
  have hmain : cascadeDeg w
      (u * algebraMap (MvPolynomial ℕ ℂ) CascadeField (pderiv j (towerMonomial k))) =
      (((towerWeight w k - (w j : ℤ) : ℤ)) : WithBot ℤ) := by
    rw [(isDegree_cascadeDeg w).map_mul, cascadeDeg_algebraMap,
      wdeg_pderiv_towerMonomial w hj, hu0, zero_add]
  have herr := cascadeDeg_towerMonomial_mul_fpderiv_lt w k j hu
  rw [add_comm, (isDegree_cascadeDeg w).map_add_of_lt (hmain ▸ herr), hmain]

/-- Off the active coordinates, the perturbed gradient lies strictly below the staircase degree. -/
theorem cascadeDeg_fpderiv_towerUnitState_lt
    (w : ℕ → ℕ) {k j : ℕ} {u : CascadeField}
    (hj : j ∉ Finset.Icc 1 k)
    (hu : cascadeDeg w (u - 1) < (0 : WithBot ℤ)) :
    cascadeDeg w (fpderiv j (towerUnitState k u)) <
      (((towerWeight w k - (w j : ℤ) : ℤ)) : WithBot ℤ) := by
  rw [towerUnitState, Derivation.leibniz, fpderiv_algebraMap_cascadeFieldWeightedDegree,
    pderiv_towerMonomial_eq_zero hj, map_zero]
  simp only [smul_eq_mul, mul_zero, add_zero]
  exact cascadeDeg_towerMonomial_mul_fpderiv_lt w k j hu

/-- Reversal permutation on a finite index set. -/
def finRevPerm (N : ℕ) : Equiv.Perm (Fin N) :=
  Function.Involutive.toPerm (fun i => i.rev) (fun i => Fin.rev_rev i)

@[simp] theorem finRevPerm_apply {N : ℕ} (i : Fin N) : finRevPerm N i = i.rev := rfl

/-- Gradient matrix of tower monomials carrying degree-zero unit perturbations. -/
noncomputable def towerUnitGradientMatrix {N : ℕ}
    (u : Fin N → CascadeField) : Matrix (Fin N) (Fin N) CascadeField :=
  fun i j => fpderiv ((j : ℕ) + 1) (towerUnitState (N - (i : ℕ)) (u i))

/-- **Unit perturbations preserve the tower-gradient determinant.** -/
theorem towerUnitGradientMatrix_det_ne_zero (w : ℕ → ℕ) {N : ℕ}
    (u : Fin N → CascadeField)
    (hu : ∀ i, cascadeDeg w (u i - 1) < (0 : WithBot ℤ)) :
    (towerUnitGradientMatrix u).det ≠ 0 := by
  refine det_ne_zero_of_staircase_deg (isDegree_cascadeDeg w)
    (towerUnitGradientMatrix u)
    (fun i => -(w ((i : ℕ) + 1) : ℤ))
    (fun i => -towerWeight w (N - (i : ℕ)))
    (finRevPerm N) ?_ ?_
  · intro i j hji
    have hactive : (i : ℕ) + 1 ∈ Finset.Icc 1 (N - (j : ℕ)) := by
      rw [Finset.mem_Icc]
      constructor
      · omega
      · change (j : ℕ) ≤ (finRevPerm N i : Fin N) at hji
        rw [finRevPerm_apply, Fin.val_rev] at hji
        omega
    have h := cascadeDeg_fpderiv_towerUnitState_eq w hactive (hu j)
    change cascadeDeg w
      (fpderiv ((i : ℕ) + 1) (towerUnitState (N - (j : ℕ)) (u j))) = _
    simpa only [sub_neg_eq_add, sub_eq_add_neg, neg_neg, add_comm] using h
  · intro i j hji
    have hinactive : (i : ℕ) + 1 ∉ Finset.Icc 1 (N - (j : ℕ)) := by
      intro hmem
      rw [Finset.mem_Icc] at hmem
      change (finRevPerm N i : Fin N) < j at hji
      rw [finRevPerm_apply] at hji
      change (i.rev : ℕ) < (j : ℕ) at hji
      rw [Fin.val_rev] at hji
      omega
    have h := cascadeDeg_fpderiv_towerUnitState_lt w hinactive (hu j)
    change cascadeDeg w
      (fpderiv ((i : ℕ) + 1) (towerUnitState (N - (j : ℕ)) (u j))) < _
    simpa only [sub_neg_eq_add, sub_eq_add_neg, neg_neg, add_comm] using h

end GaloisForLFunctions.HTGeometry
