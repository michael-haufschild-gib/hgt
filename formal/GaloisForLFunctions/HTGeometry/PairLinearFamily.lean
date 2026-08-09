import GaloisForLFunctions.HTGeometry.PairOrbitScaling

/-!
# The linear first-order family

The two-coordinate law does not raise the newest degree exactly when each placed polynomial is at
most linear in its second variable, and the constituent equation is then

`h' = a(z)·h + b(z)`,

linear of first order with polynomial coefficients.  Its factor is `a(X_j)·X_(j+1) + b(X_j)`: a
univariate factor of the earlier coordinate times the newer coordinate, plus a second univariate
factor.  Both pieces are the corpus's `fact`, so the whole univariate degree layer applies to them.

The two facts the peel reads off here are that the factor is nonzero as soon as `a` is — its
partial derivative in the newer coordinate is `a(X_j)` — and that its degree in the newer coordinate
is exactly one, so its inverse has degree `−1` and the logarithmic residue at the border is `1`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial

/-! ## A univariate polynomial in the first of two variables -/

/-- A univariate polynomial placed in the first of two variables. -/
noncomputable def firstVar (a : Polynomial ℂ) : MvPolynomial (Fin 2) ℂ :=
  Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) a

theorem firstVar_C (c : ℂ) : firstVar (Polynomial.C c) = MvPolynomial.C c := by
  simp [firstVar]

theorem firstVar_add (a b : Polynomial ℂ) : firstVar (a + b) = firstVar a + firstVar b := by
  simp [firstVar]

theorem firstVar_monomial (c : ℂ) (n : ℕ) :
    firstVar (Polynomial.C c * Polynomial.X ^ n)
      = MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2)) ^ n := by
  simp [firstVar]

theorem degreeOf_one_firstVar (a : Polynomial ℂ) : degreeOf 1 (firstVar a) = 0 := by
  induction a using Polynomial.induction_on with
  | C c =>
      rw [firstVar_C]
      exact degreeOf_C _ _
  | add q r hq hr =>
      rw [firstVar_add]
      have := degreeOf_add_le 1 (firstVar q) (firstVar r)
      omega
  | monomial n c _ =>
      rw [firstVar_monomial]
      have hX : degreeOf 1 ((MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) ^ (n + 1)) = 0 := by
        refine Nat.le_zero.mp (le_trans (degreeOf_pow_le _ _ _) ?_)
        rw [degreeOf_X, if_neg (by decide : ¬ (1 : Fin 2) = 0)]
        simp
      have := degreeOf_mul_le 1 (MvPolynomial.C c : MvPolynomial (Fin 2) ℂ)
        ((MvPolynomial.X (0 : Fin 2)) ^ (n + 1))
      rw [degreeOf_C] at this
      omega

theorem pairPoly_firstVar (a : Polynomial ℂ) (j : ℕ) :
    pairPoly (firstVar a) j = univFactor a j := by
  rw [pairPoly, firstVar, ← Polynomial.aeval_algHom_apply]
  simp [univFactor]

/-! ## The factor of a linear first-order equation -/

/-- The two-variable polynomial of `h' = a(z)·h + b(z)`. -/
noncomputable def affinePair (a b : Polynomial ℂ) : MvPolynomial (Fin 2) ℂ :=
  firstVar a * MvPolynomial.X 1 + firstVar b

theorem degreeOf_one_affinePair (a b : Polynomial ℂ) : degreeOf 1 (affinePair a b) ≤ 1 := by
  rw [affinePair]
  have h1 : degreeOf 1 ((MvPolynomial.X (1 : Fin 2)) : MvPolynomial (Fin 2) ℂ) = 1 := by
    rw [degreeOf_X, if_pos rfl]
  have h2 := degreeOf_mul_le 1 (firstVar a) (MvPolynomial.X (1 : Fin 2))
  have h3 := degreeOf_add_le 1 (firstVar a * MvPolynomial.X 1) (firstVar b)
  rw [degreeOf_one_firstVar] at h2
  rw [h1] at h2
  have h4 := degreeOf_one_firstVar b
  omega

theorem pairPoly_affinePair (a b : Polynomial ℂ) (j : ℕ) :
    pairPoly (affinePair a b) j
      = univFactor a j * MvPolynomial.X (j + 1) + univFactor b j := by
  rw [affinePair, pairPoly_add, pairPoly_mul_X, pairPoly_firstVar, pairPoly_firstVar]
  norm_num

theorem pairFactor_affinePair (a b : Polynomial ℂ) (j : ℕ) :
    pairFactor (affinePair a b) j = fact a j * fx (j + 1) + fact b j := by
  rw [pairFactor, pairPoly_affinePair, map_add, map_mul]
  rfl

/-! ## Nonvanishing -/

theorem pderiv_univFactor_of_ne {k j : ℕ} (h : k ≠ j) (q : Polynomial ℂ) :
    MvPolynomial.pderiv k (univFactor q j) = 0 := by
  rw [derivation_univFactor (MvPolynomial.pderiv k) q j, pderiv_X_of_ne h.symm]
  simp

/-- **The newer coordinate reads off the leading coefficient of the equation.** -/
theorem pderiv_pairPoly_affinePair (a b : Polynomial ℂ) (j : ℕ) :
    MvPolynomial.pderiv (j + 1) (pairPoly (affinePair a b) j) = univFactor a j := by
  rw [pairPoly_affinePair, map_add, Derivation.leibniz,
    pderiv_univFactor_of_ne (by omega) a, pderiv_X_self, pderiv_univFactor_of_ne (by omega) b]
  simp

theorem pairPoly_affinePair_ne_zero {a : Polynomial ℂ} (ha : a ≠ 0) (b : Polynomial ℂ) (j : ℕ) :
    pairPoly (affinePair a b) j ≠ 0 := by
  intro h0
  have hd : MvPolynomial.pderiv (j + 1) (pairPoly (affinePair a b) j) = 0 := by
    rw [h0, map_zero]
  rw [pderiv_pairPoly_affinePair] at hd
  exact univFactor_ne_zero ha j hd

theorem pairFactor_affinePair_ne_zero {a : Polynomial ℂ} (ha : a ≠ 0) (b : Polynomial ℂ) (j : ℕ) :
    pairFactor (affinePair a b) j ≠ 0 := by
  rw [pairFactor]
  intro h0
  refine pairPoly_affinePair_ne_zero ha b j ?_
  have hinj : Function.Injective
      (algebraMap (MvPolynomial ℕ ℂ) CascadeField) := IsFractionRing.injective _ _
  exact hinj (by rw [h0, map_zero])

/-! ## The degree in the newer coordinate is exactly one -/

theorem degreeOf_pairPoly_affinePair_top {a : Polynomial ℂ} (ha : a ≠ 0) (b : Polynomial ℂ)
    (j : ℕ) : degreeOf (j + 1) (pairPoly (affinePair a b) j) = 1 := by
  have hle : degreeOf (j + 1) (pairPoly (affinePair a b) j) ≤ 1 :=
    le_trans (degreeOf_pairPoly_top j (affinePair a b)) (degreeOf_one_affinePair a b)
  have hne : MvPolynomial.pderiv (j + 1) (pairPoly (affinePair a b) j) ≠ 0 := by
    rw [pderiv_pairPoly_affinePair]
    exact univFactor_ne_zero ha j
  have hlt := degreeOf_pderiv_lt hne
  omega

/-- **The factor's inverse has degree `−1` in the newer coordinate.** -/
theorem topDegLE_inv_pairFactor_affine {a : Polynomial ℂ} (ha : a ≠ 0) (b : Polynomial ℂ)
    (j : ℕ) : TopDegLE (j + 1) (-1) ((pairFactor (affinePair a b) j)⁻¹) := by
  have hne : pairFactor (affinePair a b) j ≠ 0 := pairFactor_affinePair_ne_zero ha b j
  refine ⟨1, pairPoly (affinePair a b) j, ?_, ?_, ?_⟩
  · intro hc
    exact hne (by rw [pairFactor, hc, map_zero])
  · rw [show algebraMap (MvPolynomial ℕ ℂ) CascadeField (pairPoly (affinePair a b) j)
        = pairFactor (affinePair a b) j from rfl, mul_inv_cancel₀ hne, map_one]
  · rw [degreeOf_pairPoly_affinePair_top ha]
    simp

/-! ## The logarithmic residue at the border is one -/

theorem fpderiv_pairFactor_affinePair_top (a b : Polynomial ℂ) (j : ℕ) :
    fpderiv (j + 1) (pairFactor (affinePair a b) j) = fact a j := by
  rw [pairFactor_affinePair, map_add, Derivation.leibniz,
    fpderiv_fact_of_ne (by omega : j ≠ j + 1), fpderiv_fx_self,
    fpderiv_fact_of_ne (by omega : j ≠ j + 1)]
  simp

/-- **The residue at infinity of the border entry is one.**  The factor is exactly linear in the
newer coordinate, so its logarithmic derivative there behaves like `1/X`. -/
theorem topLim_fx_mul_pairLogTerm_affine {a : Polynomial ℂ} (ha : a ≠ 0) (b : Polynomial ℂ)
    (j : ℕ) {p : ℕ → MvPolynomial (Fin 2) ℂ} (hp : p j = affinePair a b) :
    TopLim (j + 1) (fx (j + 1) * pairLogTerm p j (j + 1)) 1 := by
  have hne : pairFactor (affinePair a b) j ≠ 0 := pairFactor_affinePair_ne_zero ha b j
  have hval : fx (j + 1) * pairLogTerm p j (j + 1) - 1
      = -(fact b j) * (pairFactor (affinePair a b) j)⁻¹ := by
    rw [pairLogTerm, hp, fpderiv_pairFactor_affinePair_top, div_eq_mul_inv]
    field_simp
    rw [pairFactor_affinePair]
    ring
  rw [TopLim, hval]
  have hb : TopFree (j + 1) (-(fact b j)) :=
    TopFree.neg (topFree_fact (by omega : j + 1 ≠ j) b)
  have h := TopDegLE.mul hb.topDegLE (topDegLE_inv_pairFactor_affine ha b j)
  simpa using h

end GaloisForLFunctions.HTGeometry
