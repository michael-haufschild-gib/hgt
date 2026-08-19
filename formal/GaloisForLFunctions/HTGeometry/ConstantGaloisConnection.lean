import GaloisForLFunctions.HTGeometry.IsomonodromyGaugeInvariance

/-!
# A constant Galois group forces a connection over the base

If every Galois matrix `Y⁻¹ φ(Y)` of a fundamental matrix has constant entries, then the
logarithmic derivative `ℓδ Y` is fixed by the whole Galois group, because the crossed-homomorphism
law contributes `Y (ℓδ g) Y⁻¹ = 0`.  When the invariants of the Galois action are the base, `ℓδ Y`
therefore has entries in the base: the system carries a connection.

This is the direction of the parameterized translation that turns "the Galois group is conjugate to
its constant points" into isomonodromy.
-/

open scoped Differential
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R] [Differential R]

omit [Differential R] in
theorem map_invOf (σ : R →+* R) {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n R) [Invertible T] [Invertible (T.map σ)] :
    (⅟T).map σ = ⅟(T.map σ) := by
  refine (invOf_eq_right_inv ?_).symm
  rw [← Matrix.map_mul, mul_invOf_self]
  exact matrix_map_one σ

/-- The logarithmic derivative is natural for a ring endomorphism commuting with the derivation. -/
theorem logDerivMatrix_map (σ : R →+* R)
    (hσδ : ∀ x : R, σ (Differential.deriv x) = Differential.deriv (σ x))
    {n : Type*} [Fintype n] [DecidableEq n] (Y : Matrix n n R) [Invertible Y]
    [Invertible (Y.map σ)] :
    (logDerivMatrix Y).map σ = logDerivMatrix (Y.map σ) := by
  simp only [logDerivMatrix]
  rw [Matrix.map_mul, matrixDeriv_map σ hσδ, map_invOf σ Y]

/-- **A constant Galois matrix fixes the logarithmic derivative.** -/
theorem logDerivMatrix_map_eq_self (σ : R →+* R)
    (hσδ : ∀ x : R, σ (Differential.deriv x) = Differential.deriv (σ x))
    {n : Type*} [Fintype n] [DecidableEq n] (Y g : Matrix n n R)
    [Invertible Y] [Invertible g] [Invertible (Y.map σ)]
    (hYg : Y.map σ = Y * g) (hconst : matrixDeriv g = 0) :
    (logDerivMatrix Y).map σ = logDerivMatrix Y := by
  have hinv : ⅟(Y.map σ) = ⅟g * ⅟Y := by
    refine invOf_eq_right_inv ?_
    rw [hYg, mul_assoc, ← mul_assoc g, mul_invOf_self g, one_mul, mul_invOf_self Y]
  have hd : (matrixDeriv Y).map σ = matrixDeriv Y * g := by
    rw [← matrixDeriv_map σ hσδ, hYg, matrixDeriv_mul, hconst, mul_zero, add_zero]
  simp only [logDerivMatrix, Matrix.map_mul]
  rw [map_invOf σ Y, hd, hinv, mul_assoc, ← mul_assoc g, mul_invOf_self g, one_mul]

/-- **A constant Galois group forces a connection over the base.** -/
theorem exists_base_logDerivMatrix_of_galois_constant
    {K : Type*} [CommRing K] [Algebra K R]
    {n : Type*} [Fintype n] [DecidableEq n] (Y : Matrix n n R) [Invertible Y]
    (G : Set (R ≃ₐ[K] R))
    (hGδ : ∀ φ ∈ G, ∀ x : R, φ (Differential.deriv x) = Differential.deriv (φ x))
    (hconst : ∀ φ ∈ G, matrixDeriv (⅟Y * Y.map ((φ : R ≃+* R) : R →+* R)) = 0)
    (hfix : ∀ x : R, (∀ φ ∈ G, φ x = x) → ∃ a : K, x = algebraMap K R a) :
    ∀ i j, ∃ a : K, logDerivMatrix Y i j = algebraMap K R a := by
  intro i j
  refine hfix _ ?_
  intro φ hφ
  letI hYσ : Invertible (Y.map ((φ : R ≃+* R) : R →+* R)) :=
    invertibleMapRingHom ((φ : R ≃+* R) : R →+* R) Y
  letI hg : Invertible (⅟Y * Y.map ((φ : R ≃+* R) : R →+* R)) :=
    { invOf := ⅟(Y.map ((φ : R ≃+* R) : R →+* R)) * Y
      invOf_mul_self := by
        rw [mul_assoc, ← mul_assoc Y, mul_invOf_self Y, one_mul,
          invOf_mul_self (Y.map ((φ : R ≃+* R) : R →+* R))]
      mul_invOf_self := by
        rw [mul_assoc, ← mul_assoc (Y.map ((φ : R ≃+* R) : R →+* R)),
          mul_invOf_self (Y.map ((φ : R ≃+* R) : R →+* R)), one_mul, invOf_mul_self Y] }
  have hYg : Y.map ((φ : R ≃+* R) : R →+* R)
      = Y * (⅟Y * Y.map ((φ : R ≃+* R) : R →+* R)) := by
    rw [← mul_assoc, mul_invOf_self Y, one_mul]
  have h := logDerivMatrix_map_eq_self ((φ : R ≃+* R) : R →+* R) (hGδ φ hφ) Y
    (⅟Y * Y.map ((φ : R ≃+* R) : R →+* R)) hYg (hconst φ hφ)
  have h2 := congrFun (congrFun h i) j
  simpa [Matrix.map_apply] using h2

end

end GaloisForLFunctions.HTGeometry
