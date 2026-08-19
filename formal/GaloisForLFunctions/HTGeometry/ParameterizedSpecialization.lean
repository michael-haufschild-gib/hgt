import GaloisForLFunctions.HTGeometry.ParameterizedTensorTorsor
import GaloisForLFunctions.HTGeometry.DifferenceSpecialization

/-!
# Specialising the parameterized torsor

A specialisation of the tensor square which commutes with both operators has a right component that
commutes with both, hence is an element of the *parameterized* Galois group.  For the derivation the
verification is one line, because `δ 1 = 0` makes the derivation of `1 ⊗ y` equal to `1 ⊗ δ y`.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]
  [Differential K] [Differential R] [DifferentialAlgebra K R]

/-- **The right component commutes with the derivation.** -/
theorem rightComponent_commutes_deriv (ψ : (R ⊗[K] R) →ₐ[K] R)
    (hψ : ∀ v : R ⊗[K] R, ψ (tensorSquareDerivation (K := K) v) = Differential.deriv (ψ v))
    (y : R) :
    rightComponent ψ (Differential.deriv y) = Differential.deriv (rightComponent ψ y) := by
  have h1 : tensorSquareDerivation (K := K) ((1 : R) ⊗ₜ[K] y)
      = (1 : R) ⊗ₜ[K] Differential.deriv y := by
    rw [tensorSquareDerivation_tmul, Derivation.map_one_eq_zero]
    simp
  simp only [rightComponent_apply]
  rw [← h1, hψ]

/-- **A doubly equivariant specialisation gives a parameterized Galois element.** -/
theorem rightComponent_mem_parameterizedAut (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (ψ : (R ⊗[K] R) →ₐ[K] R)
    (hσψ : ∀ v : R ⊗[K] R,
      ψ (differenceTensorEquiv σK σR hcompat v) = σR (ψ v))
    (hδψ : ∀ v : R ⊗[K] R, ψ (tensorSquareDerivation (K := K) v) = Differential.deriv (ψ v))
    (hbij : Function.Bijective (rightComponent ψ)) :
    (AlgEquiv.ofBijective (rightComponent ψ) hbij) ∈ parameterizedAut (K := K) σR := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · exact rightComponent_commutes σK σR hcompat ψ hσψ x
  · exact rightComponent_commutes_deriv ψ hδψ x

end

end GaloisForLFunctions.HTGeometry
