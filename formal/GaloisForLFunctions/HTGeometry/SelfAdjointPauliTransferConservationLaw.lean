import GaloisForLFunctions.HTGeometry.PermanentLocalityHaarSeparationLaw
import Mathlib.Algebra.Star.Module
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Self-adjoint Pauli-transfer conservation

This module removes the abstract fixed-vector premise from the permanent
locality witness.  In any finite real basis of self-adjoint observables,
Heisenberg evolution is a real-linear map.  Its coordinate transfer matrix
fixes the Hamiltonian coordinate vector exactly because autonomous evolution
conserves the Hamiltonian.
-/

open scoped Matrix
open Module NormedSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- Real-linear Heisenberg conjugation on self-adjoint observables. -/
def selfAdjointConjugationLinearMap (U : A) :
    selfAdjoint A →ₗ[ℝ] selfAdjoint A where
  toFun X :=
    ⟨star U * (X : A) * U, X.prop.conjugate' U⟩
  map_add' X Y := by
    ext
    simp [mul_add, add_mul]
  map_smul' r X := by
    ext
    simp

/-- Autonomous Heisenberg conjugation fixes the Hamiltonian as an element of
the real self-adjoint observable space. -/
theorem selfAdjointConjugationLinearMap_fixes_energy
    (H : selfAdjoint A) (t : ℝ) :
    selfAdjointConjugationLinearMap
        (exp (t • ((-Complex.I) • (H : A)))) H = H := by
  apply Subtype.ext
  exact selfAdjoint_unitaryEvolution_conserves_energy
    (H : A) H.prop t

/-- Coordinate matrix of a linear map fixes the coordinate vector of every
fixed vector. -/
theorem linearMap_toMatrix_mulVec_repr_eq_of_fixed
    {R M ι : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [Fintype ι] [DecidableEq ι]
    (b : Basis ι R M) (T : M →ₗ[R] M) (x : M)
    (hfix : T x = x) :
    LinearMap.toMatrix b b T *ᵥ (b.repr x : ι → R) =
      (b.repr x : ι → R) := by
  rw [LinearMap.toMatrix_mulVec_repr, hfix]

/-- In every finite real self-adjoint basis, the Pauli-transfer matrix of an
autonomous Hamiltonian fixes that Hamiltonian's coefficient vector at every
real time. -/
theorem autonomousSelfAdjointTransferMatrix_fixes_energyCoordinates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ (selfAdjoint A))
    (H : selfAdjoint A) (t : ℝ) :
    LinearMap.toMatrix b b
        (selfAdjointConjugationLinearMap
          (exp (t • ((-Complex.I) • (H : A))))) *ᵥ
        (b.repr H : ι → ℝ) =
      (b.repr H : ι → ℝ) := by
  exact linearMap_toMatrix_mulVec_repr_eq_of_fixed b _ H
    (selfAdjointConjugationLinearMap_fixes_energy H t)

/-- A nonzero self-adjoint Hamiltonian has a nonzero coordinate vector in
every basis. -/
theorem selfAdjoint_basis_repr_coe_ne_zero
    {ι : Type*} [Fintype ι]
    (b : Basis ι ℝ (selfAdjoint A))
    (H : selfAdjoint A) (hH : H ≠ 0) :
    (b.repr H : ι → ℝ) ≠ 0 := by
  intro hzero
  apply hH
  apply b.repr.injective
  exact Finsupp.ext fun i => by
    simpa using congrFun hzero i

/-- **Concrete autonomous locality--Haar separator.**  Once a bounded-weight
self-adjoint basis is identified with the chosen Pauli dictionary, every
nonzero time-independent Hamiltonian has product-stabilizer signal strictly
above the exact Haar benchmark at every time in the dimension regime
`M 3^q < D+1`.  The fixed-coordinate premise is discharged internally. -/
theorem autonomousSelfAdjointTransferSignal_gt_haarBenchmark
    {σ ι : Type*} [Fintype σ] [Fintype ι]
    [DecidableEq ι] [Nonempty ι]
    (q D : ℕ) (label : ι → σ → Option (Fin 3))
    (hinj : Function.Injective label)
    (hweight : ∀ j, finitePauliWeight (label j) ≤ q)
    (b : Basis ι ℝ (selfAdjoint A))
    (H : selfAdjoint A) (hH : H ≠ 0) (t : ℝ)
    (hsep : Fintype.card ι * 3 ^ q < D + 1) :
    1 / ((D + 1 : ℕ) : ℝ) <
      productStabilizerTwoQueryProtocolSignal label
        (LinearMap.toMatrix b b
          (selfAdjointConjugationLinearMap
            (exp (t • ((-Complex.I) • (H : A)))))) := by
  exact productStabilizerTwoQueryProtocolSignal_gt_haarBenchmark
    q D label hinj hweight _ (b.repr H : ι → ℝ)
    (selfAdjoint_basis_repr_coe_ne_zero b H hH)
    (autonomousSelfAdjointTransferMatrix_fixes_energyCoordinates b H t)
    hsep

end

end GaloisForLFunctions.HTGeometry
