import GaloisForLFunctions.HTGeometry.HorizonFibreJetInverse

/-!
# The critical presentation differential is a Sylvester matrix

Differentiating the truncated compatibility equations gives, column by column, the coefficients of
the completed reciprocal jet in the raw unknowns and of the completed raw jet in the reciprocal
unknowns.  Evaluated in the fibre algebra, that is exactly the Sylvester matrix of the two jets:

```text
horizonPresentation_val, horizonEval_eq_aeval    the quotient map IS the presentation evaluation
horizonSylvester                                 [ T(recip jet) | T(raw jet) ]
horizonRawJetFibre_coeff, horizonRecipJetFibre_coeff
transpose_toMatrix'_aevalDifferential
    ** the presentation differential, transposed, is the Sylvester matrix **
```

`LinearMap.toMatrix'` indexes rows by variables and columns by relations, so the transpose is what
matches the Sylvester convention; determinants are unaffected, but the transpose decides which side
the identity columns appear on after multiplying by the Toeplitz matrix of the reciprocal jet.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial MvPolynomial Matrix

variable (A : Type*) [CommRing A] (m n : ℕ) (P Q : A[X])

theorem horizonPresentation_val :
    (horizonPresentation A m n P Q).val
      = fun i => Ideal.Quotient.mk (Ideal.span <| Set.range (horizonRelation A m n P Q))
          (MvPolynomial.X i) := rfl

/-- The quotient map is the presentation's evaluation. -/
theorem horizonEval_eq_aeval (p : MvPolynomial (Fin (m + n)) A) :
    horizonEval A m n P Q p
      = MvPolynomial.aeval (horizonPresentation A m n P Q).val p := by
  classical
  have h := MvPolynomial.aeval_unique
    (Ideal.Quotient.mkₐ A (Ideal.span <| Set.range (horizonRelation A m n P Q)))
  have hval := congrArg (fun φ => φ p) h
  rw [horizonPresentation_val]
  simpa [horizonEval, Function.comp_def] using hval

/-- The Sylvester matrix of the two completed jets in the fibre algebra: rows are the truncated
compatibility equations, columns the low unknowns. -/
noncomputable def horizonSylvester :
    Matrix (Fin (m + n)) (Fin (m + n)) (horizonFibreAlgebra A m n P Q) :=
  fun k v =>
    if h : (v : ℕ) < m then
      toeplitz (m + n) (horizonRecipJetFibre A m n P Q) k ⟨(v : ℕ), by omega⟩
    else
      toeplitz (m + n) (horizonRawJetFibre A m n P Q) k ⟨(v : ℕ) - m, by omega⟩

theorem horizonRawJetFibre_coeff (i : ℕ) :
    (horizonRawJetFibre A m n P Q).coeff i
      = MvPolynomial.aeval (horizonPresentation A m n P Q).val
          (horizonRawCoeff A m n P i) := by
  rw [horizonRawJetFibre, Polynomial.coeff_map, horizonRawJet_coeff, horizonEval_eq_aeval]

theorem horizonRecipJetFibre_coeff (j : ℕ) :
    (horizonRecipJetFibre A m n P Q).coeff j
      = MvPolynomial.aeval (horizonPresentation A m n P Q).val
          (horizonRecipCoeff A m n Q j) := by
  rw [horizonRecipJetFibre, Polynomial.coeff_map, horizonRecipJet_coeff, horizonEval_eq_aeval]

/-- **The presentation differential is the Sylvester matrix of the two completed jets.** -/
theorem transpose_toMatrix'_aevalDifferential :
    (LinearMap.toMatrix' (horizonPresentation A m n P Q).aevalDifferential)ᵀ
      = horizonSylvester A m n P Q := by
  classical
  ext k v
  rw [Matrix.transpose_apply, LinearMap.toMatrix'_apply,
    Algebra.PreSubmersivePresentation.aevalDifferential_single,
    horizonPresentation_map, horizonPresentation_relation, horizonSylvester]
  by_cases hv : (v : ℕ) < m
  · rw [dif_pos hv]
    have hpd := pderiv_horizonRelation_rawVar (A := A) (m := m) (n := n) (P := P) (Q := Q)
      (v : ℕ) hv k
    have hveq : (⟨(v : ℕ), by omega⟩ : Fin (m + n)) = v := Fin.ext rfl
    rw [hveq] at hpd
    rw [_root_.id, hpd, toeplitz_apply]
    by_cases hle : (v : ℕ) ≤ (k : ℕ)
    · rw [if_pos hle, if_pos hle, ← horizonRecipJetFibre_coeff]
    · rw [if_neg hle, if_neg hle, map_zero]
  · rw [dif_neg hv]
    have hj : (v : ℕ) - m < n := by omega
    have hpd := pderiv_horizonRelation_recipVar (A := A) (m := m) (n := n) (P := P) (Q := Q)
      ((v : ℕ) - m) hj k
    have hveq : (⟨m + ((v : ℕ) - m), by omega⟩ : Fin (m + n)) = v :=
      Fin.ext (show m + ((v : ℕ) - m) = (v : ℕ) by omega)
    rw [hveq] at hpd
    rw [_root_.id, hpd, toeplitz_apply]
    by_cases hle : (v : ℕ) - m ≤ (k : ℕ)
    · rw [if_pos hle, if_pos hle, ← horizonRawJetFibre_coeff]
    · rw [if_neg hle, if_neg hle, map_zero]

end

end GaloisForLFunctions.HTGeometry
