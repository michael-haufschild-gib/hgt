import GaloisForLFunctions.HTGeometry.HorizonSylvesterDifferential
import GaloisForLFunctions.HTGeometry.IdentityCornerDeterminant
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchurCaustic

/-!
# The critical presentation Jacobian is the rectangular Schur determinant

Multiplying the Sylvester matrix of the two completed jets by the Toeplitz matrix of the reciprocal
jet turns the raw block into standard basis vectors — the two jets are inverse to the horizon in the
fibre algebra — and the reciprocal block into the Toeplitz matrix of the reciprocal square:

```text
toeplitz_mul_horizonSylvester
    T(Y) · [ T(Y) | T(A) ] = [ T(Y²) | 1 ]
associated_jacobian_rectangularSchurToeplitz
    ** the presentation Jacobian is ASSOCIATED to
       det (rectangularSchurToeplitz ((Y·Y).coeff) n m) **
```

The identity corner is stripped by `IdentityCornerDeterminant`, and `det T(Y)` is a unit, so only an
association is lost.  The right-hand determinant is the corpus's `criticalReciprocalJacobian` up to
sign, so this identifies the abstract presentation Jacobian — the one the Jacobian–different bridge
consumes — with the concrete Schur equation of the horizon map.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial MvPolynomial Matrix

variable (A : Type*) [CommRing A] (m n : ℕ) (P Q : A[X])

/-- Multiplying the Sylvester matrix by the Toeplitz matrix of the reciprocal jet. -/
theorem toeplitz_mul_horizonSylvester (k v : Fin (m + n)) :
    (toeplitz (m + n) (horizonRecipJetFibre A m n P Q) * horizonSylvester A m n P Q) k v
      = if h : (v : ℕ) < m then
          toeplitz (m + n)
            (horizonRecipJetFibre A m n P Q * horizonRecipJetFibre A m n P Q) k ⟨(v : ℕ), by omega⟩
        else (1 : Matrix (Fin (m + n)) (Fin (m + n)) (horizonFibreAlgebra A m n P Q)) k
          ⟨(v : ℕ) - m, by omega⟩ := by
  classical
  rw [Matrix.mul_apply]
  by_cases hv : (v : ℕ) < m
  · rw [dif_pos hv, ← toeplitz_mul, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [horizonSylvester, dif_pos hv]
  · rw [dif_neg hv]
    have hinv : (Polynomial.X : (horizonFibreAlgebra A m n P Q)[X]) ^ (m + n) ∣
        horizonRecipJetFibre A m n P Q * horizonRawJetFibre A m n P Q - 1 := by
      have h := X_pow_dvd_horizonJet_mul_sub_one A m n P Q
      rwa [show horizonRecipJetFibre A m n P Q * horizonRawJetFibre A m n P Q - 1
        = horizonRawJetFibre A m n P Q * horizonRecipJetFibre A m n P Q - 1 by ring]
    rw [← toeplitz_mul_toeplitz_of_inverse (m + n) hinv, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [horizonSylvester, dif_neg hv]

/-- **The presentation Jacobian is the rectangular Schur determinant of the reciprocal square.** -/
theorem associated_jacobian_rectangularSchurToeplitz :
    Associated (horizonPresentation A m n P Q).jacobian
      (Matrix.det (rectangularSchurToeplitz
        (fun t => (horizonRecipJetFibre A m n P Q *
          horizonRecipJetFibre A m n P Q).coeff t) n m)) := by
  classical
  set N : Matrix (Fin (m + n)) (Fin (m + n)) (horizonFibreAlgebra A m n P Q) :=
    toeplitz (m + n) (horizonRecipJetFibre A m n P Q) * horizonSylvester A m n P Q with hN
  have hcol : ∀ (j : Fin n) (k : Fin (m + n)),
      N k (finSumFinEquiv (Sum.inr j)) = if (k : ℕ) = (j : ℕ) then 1 else 0 := by
    intro j k
    rw [hN, toeplitz_mul_horizonSylvester, dif_neg (by show ¬ m + (j : ℕ) < m; omega)]
    rw [Matrix.one_apply]
    by_cases hkj : (k : ℕ) = (j : ℕ)
    · rw [if_pos (Fin.ext (by show (k : ℕ) = m + (j : ℕ) - m; omega)), if_pos hkj]
    · rw [if_neg (by
        intro hc
        exact hkj (by have := congrArg Fin.val hc; simp at this; omega)), if_neg hkj]
  have hassoc := associated_det_of_identity_columns N hcol
  have hblock : (Matrix.of fun r i : Fin m => N (rowSplit m n (Sum.inl r))
      (finSumFinEquiv (Sum.inl i)))
      = rectangularSchurToeplitz
        (fun t => (horizonRecipJetFibre A m n P Q *
          horizonRecipJetFibre A m n P Q).coeff t) n m := by
    ext r i
    rw [Matrix.of_apply, hN, toeplitz_mul_horizonSylvester,
      dif_pos (show ((finSumFinEquiv (Sum.inl i) : Fin (m + n)) : ℕ) < m by
        show (i : ℕ) < m; omega)]
    rw [toeplitz_apply, rectangularSchurToeplitz]
    rfl
  rw [hblock] at hassoc
  have hunit : IsUnit (toeplitz (m + n) (horizonRecipJetFibre A m n P Q)).det := by
    refine isUnit_det_toeplitz_of_inverse (m + n) (G := horizonRawJetFibre A m n P Q) ?_
    have h := X_pow_dvd_horizonJet_mul_sub_one A m n P Q
    rwa [show horizonRecipJetFibre A m n P Q * horizonRawJetFibre A m n P Q - 1
      = horizonRawJetFibre A m n P Q * horizonRecipJetFibre A m n P Q - 1 by ring]
  have hdetN : N.det = (toeplitz (m + n) (horizonRecipJetFibre A m n P Q)).det *
      (horizonSylvester A m n P Q).det := by
    rw [hN, Matrix.det_mul]
  have hjac : (horizonPresentation A m n P Q).jacobian = (horizonSylvester A m n P Q).det := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_det_aevalDifferential,
      ← LinearMap.det_toMatrix', ← Matrix.det_transpose,
      transpose_toMatrix'_aevalDifferential]
  rw [hjac]
  obtain ⟨u, hu⟩ := hunit
  refine Associated.trans ⟨u, ?_⟩ hassoc
  rw [hdetN, ← hu]
  ring

end

end GaloisForLFunctions.HTGeometry
