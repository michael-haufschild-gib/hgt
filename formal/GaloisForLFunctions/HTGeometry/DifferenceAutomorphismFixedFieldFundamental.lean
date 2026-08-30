import GaloisForLFunctions.HTGeometry.DifferenceComparisonAlgebra
import GaloisForLFunctions.HTGeometry.DifferenceAutomorphismFixedField

/-!
# Ordinary fixed-field descent from a fundamental solution

The finite comparison algebra and its basis are constructed internally.  The second theorem also
constructs the tensor comparison matrix and its inverse determinant from an invertible fundamental
solution of the difference system.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

universe u

variable {K R C : Type u} [Field K] [CharZero K] [CommRing R] [Nontrivial R]
  [Algebra K R] [Field C] [IsAlgClosed C]
  [Algebra C K] [Algebra C R] [IsScalarTower C K R]
  {n : ℕ}

/-- Fixed-field descent with the finite comparison algebra and its basis constructed internally. -/
theorem exists_eq_algebraMap_of_forall_differenceAut_of_comparison
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ y : K, σR (algebraMap K R y) = algebraMap K R (σK y))
    (hconstC : ∀ y : C, σR (algebraMap C R y) = algebraMap C R y)
    (hsimple : IsSigmaSimple σR)
    (hnonew : ∀ r : R, σR r = r → ∃ c : C, r = algebraMap C R c)
    (Y : Matrix (Fin 2) (Fin 2) R)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R))
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hZσ : ∀ i j, differenceTensorEquiv σK σR hcompat (Z i j) = Z i j)
    (w : R ⊗[K] R) (hw : Z.det * w = 1)
    (u : R) (hu : Y.det * u = 1)
    (htop : Algebra.adjoin K
      (Set.range (fun p : Fin 2 × Fin 2 => Y p.1 p.2) ∪ {u}) = ⊤)
    {x : R} (hx : ∀ g : differenceAut (K := K) σR, g.1 x = x) :
    ∃ k : K, x = algebraMap K R k := by
  let E := comparisonAlgebra (C := C) Z w
  let b := Module.Free.chooseBasis C E
  have hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤ :=
    adjoin_comparisonAlgebra_eq_top Y u hu htop Z w hZ hw
  have hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)) :=
    linearIndependent_comparisonAlgebra_chooseBasis hcompat hconstC hsimple hnonew Z hZσ w hw
  exact exists_eq_algebraMap_of_forall_differenceAut
    (K := K) (R := R) (C := C) E b hgen hindep hcompat hconstC
      (fun e he => comparisonAlgebra_fixed hcompat hconstC Z hZσ w hw he)
      hsimple Y Z (fun i j => mem_comparisonAlgebra_entry Z w i j) hZ
      w (mem_comparisonAlgebra_inverseDet Z w) hw u hu htop hx

/-- Fixed-field descent from an invertible fundamental solution.  Tensor comparison matrix,
inverse determinant, finite comparison algebra, and constants basis are all produced internally. -/
theorem exists_eq_algebraMap_of_forall_differenceAut_of_fundamental
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ y : K, σR (algebraMap K R y) = algebraMap K R (σK y))
    (hconstC : ∀ y : C, σR (algebraMap C R y) = algebraMap C R y)
    (hsimple : IsSigmaSimple σR)
    (hnonew : ∀ r : R, σR r = r → ∃ c : C, r = algebraMap C R c)
    (B : Matrix (Fin 2) (Fin 2) K) (Y : Matrix (Fin 2) (Fin 2) R) [Invertible Y]
    (hY : Y.map (σR : R → R) = (B.map (algebraMap K R)) * Y)
    (u : R) (hu : Y.det * u = 1)
    (htop : Algebra.adjoin K
      (Set.range (fun p : Fin 2 × Fin 2 => Y p.1 p.2) ∪ {u}) = ⊤)
    {x : R} (hx : ∀ g : differenceAut (K := K) σR, g.1 x = x) :
    ∃ k : K, x = algebraMap K R k := by
  obtain ⟨Z, hZ, hZmap, hunit⟩ :=
    exists_tensor_comparison_matrix σK σR hcompat B Y hY
  obtain ⟨d, hd⟩ := hunit
  let w : R ⊗[K] R := ↑(d⁻¹)
  have hw : Z.det * w = 1 := by
    rw [← hd]
    simp [w]
  have hZσ : ∀ i j, differenceTensorEquiv σK σR hcompat (Z i j) = Z i j := by
    intro i j
    exact congrFun (congrFun hZmap i) j
  exact exists_eq_algebraMap_of_forall_differenceAut_of_comparison
    hcompat hconstC hsimple hnonew Y Z hZ hZσ w hw u hu htop hx

end

end GaloisForLFunctions.HTGeometry
