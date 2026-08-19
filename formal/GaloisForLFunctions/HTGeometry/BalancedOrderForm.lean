import GaloisForLFunctions.HTGeometry.OrderBlockEmbedding

/-!
# Balanced forms over an order

A real quadratic form on `R ⊗ ℝ`-space is *balanced* when multiplication by every ring element is
self-adjoint for it.  Balanced forms are a linear subspace, and the subspace is preserved by
congruence with the regular representation of any matrix over the ring, because scalars are central.

Intersecting the balanced subspace with the symmetric matrices gives the linear space in which the
symmetric space of `SL_n(R)` sits, as the positive definite locus.

* `orderRepR` : the regular representation, over `ℝ`.
* `balancedSubspace` : the balanced forms.
* `balancedSubspace_congr` : **balancedness is preserved by congruence.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {nb d : ℕ} {R : Type*} [CommRing R]

/-- The regular representation, read over `ℝ`. -/
noncomputable def orderRepR (ω : Module.Basis (Fin d) ℤ R) (M : Matrix (Fin nb) (Fin nb) R) :
    Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ :=
  (orderRep ω M).map (fun z : ℤ => (z : ℝ))

theorem orderRepR_one (ω : Module.Basis (Fin d) ℤ R) :
    orderRepR (nb := nb) ω 1 = 1 := by
  rw [orderRepR, orderRep_one]
  exact map_one ((Int.castRingHom ℝ).mapMatrix)

theorem orderRepR_mul (ω : Module.Basis (Fin d) ℤ R) (M N : Matrix (Fin nb) (Fin nb) R) :
    orderRepR ω (M * N) = orderRepR ω M * orderRepR ω N := by
  rw [orderRepR, orderRep_mul, orderRepR, orderRepR]
  exact map_mul ((Int.castRingHom ℝ).mapMatrix) _ _

theorem orderRepR_isUnit (ω : Module.Basis (Fin d) ℤ R) {M : Matrix (Fin nb) (Fin nb) R}
    (hM : IsUnit M) : IsUnit (orderRepR ω M) := by
  refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
  have heq : orderRepR ω M = (orderRep ω M).map (fun z : ℤ => (z : ℝ)) := rfl
  have hdet : (orderRepR ω M).det = (((orderRep ω M).det : ℤ) : ℝ) := by
    rw [heq]
    exact (RingHom.map_det (Int.castRingHom ℝ) (orderRep ω M)).symm
  have hu : IsUnit ((orderRep ω M).det) :=
    (Matrix.isUnit_iff_isUnit_det _).1 (hM.map (orderRepHom ω))
  rw [hdet]
  rcases Int.isUnit_iff.1 hu with hz | hz <;> rw [hz] <;> norm_num

/-- Multiplication by a ring element, in the regular representation. -/
noncomputable def orderScalar (ω : Module.Basis (Fin d) ℤ R) (α : R) :
    Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ :=
  orderRepR ω (α • (1 : Matrix (Fin nb) (Fin nb) R))

theorem orderScalar_commute (ω : Module.Basis (Fin d) ℤ R) (α : R)
    (M : Matrix (Fin nb) (Fin nb) R) :
    orderScalar ω α * orderRepR ω M = orderRepR ω M * orderScalar ω α := by
  have hcen : (α • (1 : Matrix (Fin nb) (Fin nb) R)) * M = M * (α • 1) := by
    rw [smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one]
  rw [orderScalar, ← orderRepR_mul, hcen, orderRepR_mul]

/-- The balanced forms: multiplication by every ring element is self-adjoint. -/
def balancedSubspace (ω : Module.Basis (Fin d) ℤ R) :
    Submodule ℝ (Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ) where
  carrier := {A | ∀ α : R, (orderScalar ω α)ᵀ * A = A * orderScalar ω α}
  add_mem' := by
    intro A B hA hB α
    rw [Matrix.mul_add, Matrix.add_mul, hA α, hB α]
  zero_mem' := by
    intro α
    rw [Matrix.mul_zero, Matrix.zero_mul]
  smul_mem' := by
    intro c A hA α
    rw [Matrix.mul_smul, Matrix.smul_mul, hA α]

theorem mem_balancedSubspace {ω : Module.Basis (Fin d) ℤ R}
    {A : Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ} :
    A ∈ balancedSubspace ω ↔ ∀ α : R, (orderScalar ω α)ᵀ * A = A * orderScalar ω α := Iff.rfl

/-- **Balancedness is preserved by congruence with the regular representation.** -/
theorem balancedSubspace_congr {ω : Module.Basis (Fin d) ℤ R}
    {A : Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ} (hA : A ∈ balancedSubspace ω)
    (M : Matrix (Fin nb) (Fin nb) R) :
    (orderRepR ω M)ᵀ * A * orderRepR ω M ∈ balancedSubspace ω := by
  intro α
  have hcomm := orderScalar_commute ω α M
  have hT : (orderRepR ω M)ᵀ * (orderScalar ω α)ᵀ = (orderScalar ω α)ᵀ * (orderRepR ω M)ᵀ := by
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, hcomm]
  calc (orderScalar ω α)ᵀ * ((orderRepR ω M)ᵀ * A * orderRepR ω M)
      = ((orderScalar ω α)ᵀ * (orderRepR ω M)ᵀ) * A * orderRepR ω M := by
        simp only [Matrix.mul_assoc]
    _ = (orderRepR ω M)ᵀ * ((orderScalar ω α)ᵀ * A) * orderRepR ω M := by
        rw [← hT]; simp only [Matrix.mul_assoc]
    _ = (orderRepR ω M)ᵀ * (A * orderScalar ω α) * orderRepR ω M := by rw [hA α]
    _ = (orderRepR ω M)ᵀ * A * (orderScalar ω α * orderRepR ω M) := by
        simp only [Matrix.mul_assoc]
    _ = (orderRepR ω M)ᵀ * A * orderRepR ω M * orderScalar ω α := by
        rw [hcomm]; simp only [Matrix.mul_assoc]

end GaloisForLFunctions.HTGeometry
