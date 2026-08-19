import GaloisForLFunctions.HTGeometry.DifferenceSigmaSimple

/-!
# The coordinate ring of a fundamental matrix as a difference ring

A Picard--Vessiot ring for the difference system `σ v = A v` is built from the coordinate ring of
`GL_n` over the base difference field, with the automorphism acting on the matrix of indeterminates
by left multiplication by `A`.  This file constructs that action and proves it is an automorphism
whenever `A` is invertible.

Concretely, on `K[X_{i j}]` the map sends a constant `a` to `σ a` and the indeterminate `X_{i j}` to
`Σ_k A_{i k} X_{k j}`, so the matrix of indeterminates is a formal fundamental solution matrix.  Its
inverse is the same construction for `σ⁻¹` and the entrywise `σ⁻¹`-image of `A⁻¹`, so no choice or
surjectivity argument enters and the resulting equivalence is definitionally invertible.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [CommRing K] {n : ℕ}

/-- The matrix of indeterminates: the formal fundamental solution matrix. -/
def fundamentalMatrix (K : Type*) [CommRing K] (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) K) :=
  fun i j => X (i, j)

/-- The difference action on the coordinate ring of a fundamental matrix: constants are shifted by
`σ` and the fundamental matrix is multiplied on the left by `A`. -/
def sigmaCoordHom (σ : K ≃+* K) (A : Matrix (Fin n) (Fin n) K) :
    MvPolynomial (Fin n × Fin n) K →+* MvPolynomial (Fin n × Fin n) K :=
  eval₂Hom ((C : K →+* MvPolynomial (Fin n × Fin n) K).comp (σ : K →+* K))
    (fun p : Fin n × Fin n => ∑ k, C (A p.1 k) * X (k, p.2))

@[simp] theorem sigmaCoordHom_C (σ : K ≃+* K) (A : Matrix (Fin n) (Fin n) K) (a : K) :
    sigmaCoordHom σ A (C a) = C (σ a) := by
  simp [sigmaCoordHom]

@[simp] theorem sigmaCoordHom_X (σ : K ≃+* K) (A : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) :
    sigmaCoordHom σ A (X (i, j)) = ∑ k, C (A i k) * X (k, j) := by
  simp [sigmaCoordHom]

/-- **The fundamental matrix is a formal solution.**  The action sends each entry of the
fundamental matrix to the corresponding entry of `A` times that matrix. -/
theorem sigmaCoordHom_fundamentalMatrix (σ : K ≃+* K) (A : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) :
    sigmaCoordHom σ A (fundamentalMatrix K n i j) =
      ((A.map (C : K →+* MvPolynomial (Fin n × Fin n) K)) * fundamentalMatrix K n) i j := by
  simp [fundamentalMatrix, Matrix.mul_apply, Matrix.map_apply]

/-- Composing the actions of `(σ, A)` and `(τ, B)` gives the action of `(τ.trans σ, σ(B) · A)`. -/
theorem sigmaCoordHom_comp (σ τ : K ≃+* K) (A B : Matrix (Fin n) (Fin n) K) :
    (sigmaCoordHom σ A).comp (sigmaCoordHom τ B) =
      sigmaCoordHom (τ.trans σ) ((B.map (σ : K →+* K)) * A) := by
  apply ringHom_ext
  · intro a
    simp [RingHom.comp_apply]
  · rintro ⟨i, j⟩
    simp only [RingHom.comp_apply, sigmaCoordHom_X, map_sum, map_mul, sigmaCoordHom_C]
    have hR : ∀ k : Fin n,
        C (((B.map (σ : K →+* K)) * A) i k) * (X (k, j) : MvPolynomial (Fin n × Fin n) K)
          = ∑ x : Fin n, C (σ (B i x)) * C (A x k) * X (k, j) := by
      intro k
      rw [Matrix.mul_apply]
      simp only [Matrix.map_apply, map_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by rw [map_mul]; rfl
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hR k), Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

/-- The trivial action is the identity. -/
theorem sigmaCoordHom_refl_one :
    sigmaCoordHom (RingEquiv.refl K) (1 : Matrix (Fin n) (Fin n) K) =
      RingHom.id (MvPolynomial (Fin n × Fin n) K) := by
  apply ringHom_ext
  · intro a
    simp
  · rintro ⟨i, j⟩
    simp [sigmaCoordHom_X, Matrix.one_apply, ite_mul, Finset.sum_ite_eq]

/-- **The difference action on the coordinate ring of an invertible system is an automorphism.**
The inverse is the same construction for `σ⁻¹` and the entrywise `σ⁻¹`-image of the inverse matrix,
so the equivalence carries an explicit two-sided inverse. -/
def sigmaCoordEquiv (σ : K ≃+* K) (A A' : Matrix (Fin n) (Fin n) K)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1) :
    MvPolynomial (Fin n × Fin n) K ≃+* MvPolynomial (Fin n × Fin n) K :=
  RingEquiv.ofRingHom (sigmaCoordHom σ A)
    (sigmaCoordHom σ.symm (A'.map (σ.symm : K →+* K)))
    (by
      rw [sigmaCoordHom_comp, RingEquiv.symm_trans_self]
      have hmap : ((A'.map (σ.symm : K →+* K)).map (σ : K →+* K)) = A' := by
        refine Matrix.ext fun i j => ?_
        simp [Matrix.map_apply]
      rw [hmap, hA'A, sigmaCoordHom_refl_one])
    (by
      rw [sigmaCoordHom_comp, RingEquiv.self_trans_symm]
      have hmap : (A.map (σ.symm : K →+* K)) * (A'.map (σ.symm : K →+* K))
          = (1 : Matrix (Fin n) (Fin n) K) := by
        rw [← Matrix.map_mul, hAA']
        exact Matrix.map_one _ (map_zero _) (map_one _)
      rw [hmap, sigmaCoordHom_refl_one])

@[simp] theorem sigmaCoordEquiv_apply (σ : K ≃+* K) (A A' : Matrix (Fin n) (Fin n) K)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1) (p : MvPolynomial (Fin n × Fin n) K) :
    sigmaCoordEquiv σ A A' hAA' hA'A p = sigmaCoordHom σ A p := rfl

/-- The determinant of the fundamental matrix is scaled by the determinant of the system. -/
theorem sigmaCoordHom_det (σ : K ≃+* K) (A : Matrix (Fin n) (Fin n) K) :
    sigmaCoordHom σ A ((fundamentalMatrix K n).det) =
      C (A.det) * (fundamentalMatrix K n).det := by
  have hmap : ((fundamentalMatrix K n).map (sigmaCoordHom σ A))
      = (A.map (C : K →+* MvPolynomial (Fin n × Fin n) K)) * fundamentalMatrix K n :=
    Matrix.ext fun i j => sigmaCoordHom_fundamentalMatrix σ A i j
  calc sigmaCoordHom σ A ((fundamentalMatrix K n).det)
      = ((fundamentalMatrix K n).map (sigmaCoordHom σ A)).det :=
        RingHom.map_det _ _
    _ = ((A.map (C : K →+* MvPolynomial (Fin n × Fin n) K)) * fundamentalMatrix K n).det := by
        rw [hmap]
    _ = C (A.det) * (fundamentalMatrix K n).det := by
        rw [Matrix.det_mul]
        congr 1
        rw [RingHom.map_det (C : K →+* MvPolynomial (Fin n × Fin n) K) A,
          RingHom.mapMatrix_apply]


end

end GaloisForLFunctions.HTGeometry
