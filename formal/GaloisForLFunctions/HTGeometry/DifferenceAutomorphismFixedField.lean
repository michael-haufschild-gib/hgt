import GaloisForLFunctions.HTGeometry.GaloisDifferentialPointGroup
import GaloisForLFunctions.HTGeometry.DifferenceGaloisEndgame
import GaloisForLFunctions.HTGeometry.SigmaConstantsReduced

/-!
# Fixed-field descent for an ordinary difference Picard--Vessiot torsor

Rational points of the comparison algebra give difference endomorphisms.  Sigma-simplicity makes
them injective, Picard--Vessiot generation makes them surjective, and point separation then turns
invariance under the full difference automorphism group into membership in the base field.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

variable {K R C : Type*} [Field K] [CharZero K] [CommRing R] [Nontrivial R]
  [Algebra K R] [Field C] [IsAlgClosed C]
  [Algebra C K] [Algebra C R] [IsScalarTower C K R]

/-- The fixed field of the ordinary difference automorphism group of a finite-type
Picard--Vessiot torsor is the base field.  Point separation, injectivity, and surjectivity are all
derived from the displayed structural data. -/
theorem exists_eq_algebraMap_of_forall_differenceAut
    (E : Subalgebra C (R ⊗[K] R)) [Algebra.FiniteType C E]
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hEσ : ∀ e ∈ E, differenceTensorEquiv σK σR hcompat e = e)
    (hsimple : IsSigmaSimple σR)
    (Y : Matrix (Fin 2) (Fin 2) R)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hGdet : ∀ χ : E →ₐ[C] C, IsUnit (galoisMatrixAt E Z hZE χ).det)
    (u : R) (hu : Y.det * u = 1)
    (htop : Algebra.adjoin K
      (Set.range (fun p : Fin 2 × Fin 2 => Y p.1 p.2) ∪ {u}) = ⊤)
    {x : R} (hx : ∀ g : differenceAut (K := K) σR, g.1 x = x) :
    ∃ k : K, x = algebraMap K R k := by
  have hsep : ∀ e : E, (∀ χ ∈ (Set.univ : Set (E →ₐ[C] C)), χ e = 0) → e = 0 := by
    intro e he
    exact eq_zero_of_forall_algHom_eq_zero_tensorSquare hsimple E
      (fun χ => he χ Set.mem_univ)
  apply exists_eq_algebraMap_of_forall_galoisAutAt E b hgen hindep Set.univ hsep
  intro χ _
  let f := galoisAutAtK E b hgen hindep χ
  have hfinj : Function.Injective f :=
    galoisAutAtK_injective E b hgen hindep hcompat hconstC hEσ hsimple χ
  have hfsurj : Function.Surjective f :=
    galoisAutAtK_surjective_of_pvGeneration E b hgen hindep χ Y Z hZE hZ
      (hGdet χ) u hu htop
  let φ : R ≃ₐ[K] R := AlgEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  have hφσ : ∀ y : R, φ (σR y) = σR (φ y) := by
    intro y
    exact galoisAutAtK_sigma E b hgen hindep hcompat hconstC hEσ χ y
  let g : differenceAut (K := K) σR := ⟨φ, hφσ⟩
  change f x = x
  exact hx g

end

end GaloisForLFunctions.HTGeometry
