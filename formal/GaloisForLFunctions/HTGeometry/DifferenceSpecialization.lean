import GaloisForLFunctions.HTGeometry.DifferenceTensorGeneration

/-!
# Specialising the tensor square produces Galois data

A point of the difference Galois group is a specialisation of the tensor square: a `K`-algebra map
`R ⊗_K R → R` restricting to the identity on the left copy.  Its right component is then a
`K`-algebra endomorphism of `R`, it commutes with the difference operator as soon as the
specialisation does, and it moves the fundamental matrix by the specialised comparison matrix, which
is invertible.

That is the whole bridge from a point of the group to an element of the Galois group; what remains
for the correspondence is the existence of enough specialisations, which is the torsor
decomposition together with the Nullstellensatz.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

/-- The right component of a specialisation of the tensor square. -/
def rightComponent (ψ : (R ⊗[K] R) →ₐ[K] R) : R →ₐ[K] R :=
  ψ.comp (Algebra.TensorProduct.includeRight)

@[simp] theorem rightComponent_apply (ψ : (R ⊗[K] R) →ₐ[K] R) (y : R) :
    rightComponent ψ y = ψ ((1 : R) ⊗ₜ[K] y) := rfl

/-- **The right component commutes with the difference operator.** -/
theorem rightComponent_commutes (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (ψ : (R ⊗[K] R) →ₐ[K] R)
    (hψ : ∀ v : R ⊗[K] R, ψ (differenceTensorEquiv σK σR hcompat v) = σR (ψ v)) (y : R) :
    rightComponent ψ (σR y) = σR (rightComponent ψ y) := by
  have h1 : differenceTensorEquiv σK σR hcompat ((1 : R) ⊗ₜ[K] y) = (1 : R) ⊗ₜ[K] σR y := by
    rw [differenceTensorEquiv_tmul, map_one]
  simp only [rightComponent_apply]
  rw [← h1, hψ]

variable {n : ℕ}

/-- **The right component moves the fundamental matrix by the specialised comparison matrix.** -/
theorem rightComponent_fundamental (ψ : (R ⊗[K] R) →ₐ[K] R)
    (hleft : ∀ x : R, ψ (x ⊗ₜ[K] (1 : R)) = x)
    (Y : Matrix (Fin n) (Fin n) R) (Z : Matrix (Fin n) (Fin n) (R ⊗[K] R))
    (hZ : leftFundamental K Y * Z = rightFundamental K Y) (i j : Fin n) :
    rightComponent ψ (Y i j) = (Y * Z.map (ψ : (R ⊗[K] R) → R)) i j := by
  have h := congrFun (congrFun hZ i) j
  simp only [Matrix.mul_apply, leftFundamental, rightFundamental, Matrix.map_apply] at h
  simp only [rightComponent_apply, Matrix.mul_apply, Matrix.map_apply]
  rw [← h, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_mul, hleft]

/-- **The specialised comparison matrix is invertible.** -/
theorem isUnit_det_specialization (ψ : (R ⊗[K] R) →ₐ[K] R)
    (Z : Matrix (Fin n) (Fin n) (R ⊗[K] R)) (w : R ⊗[K] R) (hw : Z.det * w = 1) :
    IsUnit (Z.map (ψ : (R ⊗[K] R) → R)).det := by
  have hdet : (Z.map (ψ : (R ⊗[K] R) → R)).det = ψ Z.det := by
    have h := RingHom.map_det (ψ.toRingHom) Z
    rw [RingHom.mapMatrix_apply] at h
    exact h.symm
  rw [hdet]
  refine ⟨⟨ψ Z.det, ψ w, ?_, ?_⟩, rfl⟩
  · rw [← map_mul, hw, map_one]
  · rw [← map_mul, mul_comm, hw, map_one]

/-- **The right component is determined by the specialised comparison matrix.**  Two specialisations
agreeing on the comparison matrix have the same right component on the fundamental matrix. -/
theorem rightComponent_eq_of_map_eq (ψ φ : (R ⊗[K] R) →ₐ[K] R)
    (hψleft : ∀ x : R, ψ (x ⊗ₜ[K] (1 : R)) = x) (hφleft : ∀ x : R, φ (x ⊗ₜ[K] (1 : R)) = x)
    (Y : Matrix (Fin n) (Fin n) R) (Z : Matrix (Fin n) (Fin n) (R ⊗[K] R))
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hmap : Z.map (ψ : (R ⊗[K] R) → R) = Z.map (φ : (R ⊗[K] R) → R)) (i j : Fin n) :
    rightComponent ψ (Y i j) = rightComponent φ (Y i j) := by
  rw [rightComponent_fundamental ψ hψleft Y Z hZ, rightComponent_fundamental φ hφleft Y Z hZ,
    hmap]

end

end GaloisForLFunctions.HTGeometry
