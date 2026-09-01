import GaloisForLFunctions.HTGeometry.GaloisMonoidGroupStructure
import GaloisForLFunctions.HTGeometry.ComparisonJetAlgebraFlip

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct Differential

universe u

variable {K R C : Type u} [Field K] [CommRing R] [Nontrivial R] [Algebra K R]
  [Field C] [Algebra C K] [Algebra C R] [IsScalarTower C K R]
  [Differential K] [Differential R] [DifferentialAlgebra K R]
  [Differential C] [DifferentialAlgebra C R]

omit [Nontrivial R] in
/-- The comparison-jet algebra supplies inverse-adjoint stability directly from tensor flip, using
only a chosen inverse determinant. -/
theorem comparisonJetGaloisMonoid_detOne_inverse_adjoint_of_det_inverse
    (Y : Matrix (Fin 2) (Fin 2) R)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R))
    (w : R ⊗[K] R)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hw : Z.det * w = 1)
    (u : R) (hu : Y.det * u = 1)
    :
    ∀ g ∈ galoisMonoid (comparisonJetAlgebra (C := C) Z w) Z
        (fun i j => mem_comparisonJetAlgebra_entry Z w i j)
        (tensorDifferentialPoints (comparisonJetAlgebra (C := C) Z w)
          (fun _e he => comparisonJetAlgebra_deriv_stable Z hw he)),
      ∃ g' : Matrix (Fin 2) (Fin 2) C, g * g' = 1 ∧
        ∀ W ∈ matrixTangentM (matrixVanishingIdeal
            {h ∈ galoisMonoid (comparisonJetAlgebra (C := C) Z w) Z
                (fun i j => mem_comparisonJetAlgebra_entry Z w i j)
                (tensorDifferentialPoints (comparisonJetAlgebra (C := C) Z w)
                  (fun _e he => comparisonJetAlgebra_deriv_stable Z hw he)) |
              h.det = 1})
          (subset_matrixZeroSet_vanishingIdeal _
            ⟨Submonoid.one_mem _, Matrix.det_one⟩),
          g * W * g' ∈ matrixTangentM (matrixVanishingIdeal
            {h ∈ galoisMonoid (comparisonJetAlgebra (C := C) Z w) Z
                (fun i j => mem_comparisonJetAlgebra_entry Z w i j)
                (tensorDifferentialPoints (comparisonJetAlgebra (C := C) Z w)
                  (fun _e he => comparisonJetAlgebra_deriv_stable Z hw he)) |
              h.det = 1})
            (subset_matrixZeroSet_vanishingIdeal _
              ⟨Submonoid.one_mem _, Matrix.det_one⟩) := by
  let E := comparisonJetAlgebra (C := C) Z w
  let hZE : ∀ i j, Z i j ∈ E := fun i j => mem_comparisonJetAlgebra_entry Z w i j
  let hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E :=
    fun e he => comparisonJetAlgebra_deriv_stable Z hw he
  intro g hg
  obtain ⟨g', hg', hgg'⟩ := comparisonJetGaloisMonoid_exists_inverse_mem_of_det_inverse
    Y u hu Z w hZ hw hg
  refine ⟨g', hgg', ?_⟩
  apply conj_mem_matrixTangentM_vanishingIdeal
    (H := {h ∈ galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ) | h.det = 1})
    (hHone := ⟨Submonoid.one_mem _, Matrix.det_one⟩) hgg'
  intro h hh
  refine ⟨Submonoid.mul_mem _ (Submonoid.mul_mem _ hg hh.1) hg', ?_⟩
  have hdetgg' : g.det * g'.det = 1 := by
    rw [← Matrix.det_mul, hgg', Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, hh.2, mul_one, hdetgg']

omit [Nontrivial R] in
/-- The comparison-jet algebra supplies inverse-adjoint stability directly from tensor flip. -/
theorem comparisonJetGaloisMonoid_detOne_inverse_adjoint
    (Y : Matrix (Fin 2) (Fin 2) R)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R))
    (w : R ⊗[K] R)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hw : Z.det * w = 1)
    (_hdet : Z.det ^ 2 = 1)
    (u : R) (hu : Y.det * u = 1)
    :
    ∀ g ∈ galoisMonoid (comparisonJetAlgebra (C := C) Z w) Z
        (fun i j => mem_comparisonJetAlgebra_entry Z w i j)
        (tensorDifferentialPoints (comparisonJetAlgebra (C := C) Z w)
          (fun _e he => comparisonJetAlgebra_deriv_stable Z hw he)),
      ∃ g' : Matrix (Fin 2) (Fin 2) C, g * g' = 1 ∧
        ∀ W ∈ matrixTangentM (matrixVanishingIdeal
            {h ∈ galoisMonoid (comparisonJetAlgebra (C := C) Z w) Z
                (fun i j => mem_comparisonJetAlgebra_entry Z w i j)
                (tensorDifferentialPoints (comparisonJetAlgebra (C := C) Z w)
                  (fun _e he => comparisonJetAlgebra_deriv_stable Z hw he)) |
              h.det = 1})
          (subset_matrixZeroSet_vanishingIdeal _
            ⟨Submonoid.one_mem _, Matrix.det_one⟩),
          g * W * g' ∈ matrixTangentM (matrixVanishingIdeal
            {h ∈ galoisMonoid (comparisonJetAlgebra (C := C) Z w) Z
                (fun i j => mem_comparisonJetAlgebra_entry Z w i j)
                (tensorDifferentialPoints (comparisonJetAlgebra (C := C) Z w)
                  (fun _e he => comparisonJetAlgebra_deriv_stable Z hw he)) |
              h.det = 1})
            (subset_matrixZeroSet_vanishingIdeal _
              ⟨Submonoid.one_mem _, Matrix.det_one⟩) :=
  comparisonJetGaloisMonoid_detOne_inverse_adjoint_of_det_inverse Y Z w hZ hw u hu

end

end GaloisForLFunctions.HTGeometry
