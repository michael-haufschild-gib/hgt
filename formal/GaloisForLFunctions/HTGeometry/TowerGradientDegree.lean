import GaloisForLFunctions.HTGeometry.TowerWeightedDegree

/-!
# Gradients of the tower monomials

A tower monomial is a product of distinct coordinates, so its partial derivative is the same product
with one factor removed — or zero when the coordinate does not occur.  Its weighted degree therefore
drops by exactly the weight of that coordinate.

This is the first row of the chain-gradient matrix in closed form, and the model against which the
higher rows are compared.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-- A partial derivative kills a product of coordinates not containing it. -/
theorem pderiv_prod_X_of_notMem (j : ℕ) : ∀ (s : Finset ℕ), j ∉ s →
    pderiv j (∏ i ∈ s, (MvPolynomial.X i : MvPolynomial ℕ ℂ)) = 0 := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert b t hb ih =>
      intro hj
      have hjb : b ≠ j := fun h => hj (h ▸ Finset.mem_insert_self b t)
      have hjt : j ∉ t := fun h => hj (Finset.mem_insert_of_mem h)
      rw [Finset.prod_insert hb, Derivation.leibniz, ih hjt,
        MvPolynomial.pderiv_X_of_ne hjb]
      simp

/-- The weighted degree of a product of distinct coordinates. -/
theorem wdeg_prod_X (w : ℕ → ℕ) (s : Finset ℕ) :
    wdeg w (∏ i ∈ s, (MvPolynomial.X i : MvPolynomial ℕ ℂ))
      = (((∑ i ∈ s, (w i : ℤ)) : ℤ) : WithBot ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, (isDegree_wdeg w).map_one]
      rfl
  | insert b t hb ih =>
      rw [Finset.prod_insert hb, Finset.sum_insert hb, (isDegree_wdeg w).map_mul, ih, wdeg_X,
        ← WithBot.coe_add, add_comm]

/-- **The gradient of a tower monomial.** -/
theorem pderiv_towerMonomial {j k : ℕ} (hj : j ∈ Finset.Icc 1 k) :
    pderiv j (towerMonomial k) = ∏ i ∈ (Finset.Icc 1 k).erase j, (MvPolynomial.X i) := by
  classical
  rw [towerMonomial, ← Finset.prod_erase_mul _ _ hj, Derivation.leibniz,
    pderiv_prod_X_of_notMem j _ (Finset.notMem_erase j _), MvPolynomial.pderiv_X_self]
  simp

theorem pderiv_towerMonomial_eq_zero {j k : ℕ} (hj : j ∉ Finset.Icc 1 k) :
    pderiv j (towerMonomial k) = 0 :=
  pderiv_prod_X_of_notMem j _ hj

/-- **The weighted degree of the gradient of a tower monomial.** -/
theorem wdeg_pderiv_towerMonomial (w : ℕ → ℕ) {j k : ℕ} (hj : j ∈ Finset.Icc 1 k) :
    wdeg w (pderiv j (towerMonomial k)) = (((towerWeight w k - (w j : ℤ)) : ℤ) : WithBot ℤ) := by
  classical
  rw [pderiv_towerMonomial hj, wdeg_prod_X]
  congr 1
  have h := Finset.sum_erase_add (Finset.Icc 1 k) (fun i => (w i : ℤ)) hj
  rw [towerWeight]
  omega

end GaloisForLFunctions.HTGeometry

end
