import GaloisForLFunctions.HTGeometry.ProjectiveHorizonPageTransition
import GaloisForLFunctions.HTGeometry.FreeCoordinateField

/-!
# The Cramer system that recovers the missing jets of a transverse coordinate

Once the reciprocal chart coordinate and all of its jets are known, the two horizons supply the jets
of a transverse coordinate and of its product with the reciprocal coordinate from a given order on.
Subtracting the already known high-order terms of the Leibniz expansion leaves a square linear
system whose matrix has entries `binom(n+i,k)` against the jets of the reciprocal coordinate.

Setting every displayed jet of the reciprocal coordinate to one turns that matrix into a
consecutive shifted Pascal minor, whose determinant is one.  Since the specialisation is a ring
homomorphism, the determinant of the system is a nonzero jet polynomial, so over the free jet field
the system has a unique solution and Cramer's rule recovers every missing jet.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The Cramer matrix -/

/-- The matrix of the reconstruction system: rows are the jet orders `n, ..., n+r-1` and columns the
unknown jet orders `0, ..., r-1`. -/
def cramerJetMatrix (R : Type*) [CommRing R] (n r : ℕ) (b : ℕ → R) :
    Matrix (Fin r) (Fin r) R :=
  Matrix.of fun i k => (Nat.choose (n + (i : ℕ)) (k : ℕ) : R) * b (n + (i : ℕ) - (k : ℕ))

theorem cramerJetMatrix_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (n r : ℕ) (b : ℕ → R) :
    (cramerJetMatrix R n r b).map φ = cramerJetMatrix S n r fun j => φ (b j) := by
  ext i k
  rw [Matrix.map_apply, cramerJetMatrix, cramerJetMatrix, Matrix.of_apply, Matrix.of_apply,
    map_mul, map_natCast]

/-- With every displayed jet set to one the Cramer matrix is the consecutive shifted Pascal
minor, whose determinant is one. -/
theorem det_cramerJetMatrix_one (R : Type*) [CommRing R] (n r : ℕ) :
    (cramerJetMatrix R n r fun _ => 1).det = 1 := by
  have hmap : (cramerJetMatrix R n r fun _ => 1) =
      (shiftedPascalMatrix n r).map (Int.castRingHom R) := by
    ext i k
    rw [cramerJetMatrix, Matrix.of_apply, mul_one, Matrix.map_apply, shiftedPascalMatrix]
    simp
  rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, shiftedPascalMatrix_det, map_one]

/-! ## Nonvanishing over the free jet polynomial ring -/

/-- **The Cramer determinant is a nonzero jet polynomial.**  The specialisation sending every jet
to one is a ring homomorphism carrying the determinant to the Pascal determinant `1`. -/
theorem det_cramerJetMatrix_X_ne_zero {K : Type*} [Field K] (n r : ℕ) :
    (cramerJetMatrix (MvPolynomial ℕ K) n r MvPolynomial.X).det ≠ 0 := by
  intro hzero
  have hφ := congrArg (MvPolynomial.eval fun _ => (1 : K)) hzero
  rw [map_zero, RingHom.map_det, RingHom.mapMatrix_apply, cramerJetMatrix_map] at hφ
  have hone : (fun j : ℕ => (MvPolynomial.eval fun _ => (1 : K)) (MvPolynomial.X j)) =
      fun _ : ℕ => (1 : K) := by
    funext j
    rw [MvPolynomial.eval_X]
  rw [hone, det_cramerJetMatrix_one] at hφ
  exact one_ne_zero hφ

/-! ## The system over the free jet field -/

/-- The Cramer matrix over the free rational jet field. -/
def cramerJetMatrixField (K : Type*) [Field K] (n r : ℕ) :
    Matrix (Fin r) (Fin r) (FreeCoordinateRationalField K ℕ) :=
  cramerJetMatrix (FreeCoordinateRationalField K ℕ) n r fun j => freeCoordinate K ℕ j

theorem det_cramerJetMatrixField_ne_zero {K : Type*} [Field K] (n r : ℕ) :
    (cramerJetMatrixField K n r).det ≠ 0 := by
  intro hzero
  refine det_cramerJetMatrix_X_ne_zero (K := K) n r ?_
  refine (map_eq_zero_iff (algebraMap (MvPolynomial ℕ K) (FreeCoordinateRationalField K ℕ))
    (IsFractionRing.injective _ _)).1 ?_
  rw [RingHom.map_det, RingHom.mapMatrix_apply, cramerJetMatrix_map]
  exact hzero

/-- **Cramer's rule for the missing jets.**  Over the free jet field the reconstruction system has
exactly one solution, so every missing jet of the transverse coordinate is recovered. -/
theorem cramerJetSystem_existsUnique {K : Type*} [Field K] (n r : ℕ)
    (c : Fin r → FreeCoordinateRationalField K ℕ) :
    ∃! v : Fin r → FreeCoordinateRationalField K ℕ,
      (cramerJetMatrixField K n r).mulVec v = c := by
  have hunit : IsUnit (cramerJetMatrixField K n r).det :=
    (det_cramerJetMatrixField_ne_zero (K := K) n r).isUnit
  refine ⟨(cramerJetMatrixField K n r)⁻¹.mulVec c, ?_, ?_⟩
  · show (cramerJetMatrixField K n r).mulVec ((cramerJetMatrixField K n r)⁻¹.mulVec c) = c
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  · intro v hv
    show v = (cramerJetMatrixField K n r)⁻¹.mulVec c
    rw [← hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]

end

end GaloisForLFunctions.HTGeometry
