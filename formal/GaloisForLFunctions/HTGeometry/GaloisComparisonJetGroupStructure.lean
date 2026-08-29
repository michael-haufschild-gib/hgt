import GaloisForLFunctions.HTGeometry.GaloisMonoidGroupStructure
import GaloisForLFunctions.HTGeometry.ComparisonJetAlgebraFixed
import GaloisForLFunctions.HTGeometry.TensorBasisIndependence

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct Differential

universe u

variable {K R C : Type u} [Field K] [CommRing R] [Nontrivial R] [Algebra K R]
  [Field C] [Algebra C K] [Algebra C R] [IsScalarTower C K R]
  [Differential K] [Differential R] [DifferentialAlgebra K R]
  [Differential C] [DifferentialAlgebra C R]

/-- The comparison-jet algebra supplies every structural premise of inverse-adjoint stability. -/
theorem comparisonJetGaloisMonoid_detOne_inverse_adjoint
    (Y : Matrix (Fin 2) (Fin 2) R)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R))
    (w : R ⊗[K] R)
    {ι : Type*}
    (b : Module.Basis ι C (comparisonJetAlgebra (C := C) Z w))
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hσδ : ∀ x : R, σR (Differential.deriv x) = Differential.deriv (σR x))
    (hsimple : IsSigmaSimple σR)
    (hnew : ∀ x : R, σR x = x → ∃ c : C, x = algebraMap C R c)
    (hZσ : ∀ i j, differenceTensorEquiv σK σR hcompat (Z i j) = Z i j)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hw : Z.det * w = 1)
    (hdet : Z.det ^ 2 = 1)
    (u : R) (hu : Y.det * u = 1)
    (htop : Algebra.adjoin K
      (Set.range (fun p : Fin 2 × Fin 2 => Y p.1 p.2) ∪ {u}) = ⊤) :
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
  classical
  let E := comparisonJetAlgebra (C := C) Z w
  let hZE : ∀ i j, Z i j ∈ E := fun i j => mem_comparisonJetAlgebra_entry Z w i j
  let hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E :=
    fun e he => comparisonJetAlgebra_deriv_stable Z hw he
  have hEσ : ∀ e ∈ E, differenceTensorEquiv σK σR hcompat e = e :=
    fun e he => comparisonJetAlgebra_fixed hcompat hconstC hσδ Z hZσ w hw he
  have hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤ :=
    adjoin_comparisonJetAlgebra_eq_top Y u hu htop Z w hZ hw
  let τ := differenceTensorEquiv σK σR hcompat
  have hτR : ∀ r : R, τ (algebraMap R (R ⊗[K] R) r) =
      algebraMap R (R ⊗[K] R) (σR r) := by
    intro r
    change τ (r ⊗ₜ[K] (1 : R)) = σR r ⊗ₜ[K] (1 : R)
    rw [differenceTensorEquiv_tmul, map_one]
  have hEconst : ∀ e : E, τ (e : R ⊗[K] R) = (e : R ⊗[K] R) :=
    fun e => hEσ e e.2
  have hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)) :=
    linearIndependent_constants_basis σR τ hτR hsimple E hEconst hnew b
  exact galoisMonoid_detOne_inverse_adjoint E b hgen hindep hcompat hconstC hEσ hEδ
    hsimple hnew Y Z hZE hZ hdet u hu htop

end

end GaloisForLFunctions.HTGeometry
