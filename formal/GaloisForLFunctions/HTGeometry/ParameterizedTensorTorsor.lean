import GaloisForLFunctions.HTGeometry.TensorSquareDerivation

/-!
# The parameterized torsor comparison matrix

In the parameterized setting the comparison matrix of the torsor still has entries fixed by the
difference operator, and now their derivatives are fixed too, because the two operators commute on
the tensor square.  So the comparison matrix lives over a *differential* ring of constants: the
coordinates of the parameterized Galois group are differential coordinates, which is what makes that
group a differential algebraic group.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]
  [Differential K] [Differential R] [DifferentialAlgebra K R] {n : ℕ}

/-- **The parameterized torsor comparison matrix.**  Its entries are constants of the difference
operator on the tensor square, and so are their derivatives. -/
theorem exists_parameterized_tensor_comparison_matrix (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (hσ : ∀ x : R, σR (Differential.deriv x) = Differential.deriv (σR x))
    (B : Matrix (Fin n) (Fin n) K) (Y : Matrix (Fin n) (Fin n) R) [Invertible Y]
    (hY : Y.map (σR : R → R) = (B.map (algebraMap K R)) * Y) :
    ∃ Z : Matrix (Fin n) (Fin n) (R ⊗[K] R),
      leftFundamental K Y * Z = rightFundamental K Y ∧
      (∀ i j, differenceTensorEquiv σK σR hcompat (Z i j) = Z i j) ∧
      (∀ i j, differenceTensorEquiv σK σR hcompat
          (tensorSquareDerivation (K := K) (Z i j))
        = tensorSquareDerivation (K := K) (Z i j)) ∧
      IsUnit Z.det := by
  obtain ⟨Z, hZfact, hZconst, hZdet⟩ :=
    exists_tensor_comparison_matrix σK σR hcompat B Y hY
  have hentry : ∀ i j, differenceTensorEquiv σK σR hcompat (Z i j) = Z i j := by
    intro i j
    exact congrFun (congrFun hZconst i) j
  refine ⟨Z, hZfact, hentry, ?_, hZdet⟩
  intro i j
  rw [tensorSquareDerivation_commutes σK σR hcompat hσ, hentry i j]

end

end GaloisForLFunctions.HTGeometry
