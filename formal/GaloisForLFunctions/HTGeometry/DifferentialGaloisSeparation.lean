import GaloisForLFunctions.HTGeometry.DifferentialGaloisPoint
import GaloisForLFunctions.HTGeometry.KolchinNullstellensatz
import GaloisForLFunctions.HTGeometry.DifferenceIsomonodromyEndgame

/-!
# Isomonodromy with the separating set supplied

A derivation-stable subalgebra of the tensor square inherits the derivation, so its differential
points are exactly the algebra maps to the constants commuting with it.  Kolchin's Nullstellensatz
makes those points separate as soon as the constants are differentially closed and the subalgebra is
a reduced algebra of finite type, and the specialisation bridge makes their Galois automorphisms
differential.

Both hypotheses of the isomonodromy endgame are therefore discharged, leaving a statement whose
inputs are the difference equation, the absence of a base Riccati solution, and the differential
constraint on the scalar stabiliser of the Galois monoid.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct Differential

/-- The derivation restricted to a stable subalgebra. -/
@[reducible] def subalgebraDifferential {C A : Type*} [CommRing C] [CommRing A]
    [Algebra C A] [Differential A] (E : Subalgebra C A)
    (hE : ∀ e ∈ E, Differential.deriv e ∈ E) : Differential E where
  deriv :=
    { toLinearMap :=
        { toFun := fun x => ⟨Differential.deriv x.1, hE x.1 x.2⟩
          map_add' := fun x y => Subtype.ext (Differential.deriv.map_add x.1 y.1)
          map_smul' := fun n x => Subtype.ext (Differential.deriv.map_smul n x.1) }
      map_one_eq_zero' := Subtype.ext Differential.deriv.map_one_eq_zero
      leibniz' := fun x y => Subtype.ext (Differential.deriv.leibniz x.1 y.1) }

@[simp] theorem subalgebraDifferential_coe {C A : Type*} [CommRing C] [CommRing A]
    [Algebra C A] [Differential A] (E : Subalgebra C A)
    (hE : ∀ e ∈ E, Differential.deriv e ∈ E) (x : E) :
    letI := subalgebraDifferential E hE
    ((Differential.deriv x : E) : A) = Differential.deriv (x : A) := rfl

universe u

variable {K R C : Type u} [Field K] [CommRing R] [Nontrivial R] [Algebra K R]
  [Field C] [Algebra C K] [Algebra C R] [IsScalarTower C K R]
  [Differential K] [Differential R] [DifferentialAlgebra K R]
  [Differential C] [DifferentialAlgebra C R]

omit [Nontrivial R] in
/-- The derivation of the tensor square extends the derivation of the constants. -/
theorem tensorSquareDerivation_algebraMap (c : C) :
    tensorSquareDerivation (K := K) (algebraMap C (R ⊗[K] R) c)
      = algebraMap C (R ⊗[K] R) (Differential.deriv c) := by
  have halgC : ∀ d : C, (algebraMap C (R ⊗[K] R)) d = (algebraMap C R d) ⊗ₜ[K] (1 : R) := by
    intro d
    rw [IsScalarTower.algebraMap_apply C R (R ⊗[K] R)]
    rfl
  rw [halgC, halgC, tensorSquareDerivation_tmul, Derivation.map_one_eq_zero,
    TensorProduct.tmul_zero, add_zero, DifferentialAlgebra.deriv_algebraMap]

/-- The differential points of a derivation-stable subalgebra of the tensor square. -/
def tensorDifferentialPoints (E : Subalgebra C (R ⊗[K] R))
    (hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E) : Set (E →ₐ[C] C) :=
  {χ | ∀ (e : R ⊗[K] R) (he : e ∈ E),
      χ ⟨tensorSquareDerivation (K := K) e, hEδ e he⟩ = Differential.deriv (χ ⟨e, he⟩)}

omit [Nontrivial R] in
/-- **The differential points of the constants subalgebra separate**, over a differentially closed
field of constants. -/
theorem eq_zero_of_forall_mem_tensorDifferentialPoints [Algebra ℚ C] [IsDifferentiallyClosed C]
    (E : Subalgebra C (R ⊗[K] R)) (hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E)
    [IsReduced E] [Algebra.FiniteType C E]
    (e : E) (h : ∀ χ ∈ tensorDifferentialPoints E hEδ, χ e = 0) : e = 0 := by
  letI : Differential (R ⊗[K] R) := ⟨tensorSquareDerivation (K := K)⟩
  letI : Differential E := subalgebraDifferential E hEδ
  letI : Algebra ℚ E := ((algebraMap C E).comp (algebraMap ℚ C)).toAlgebra
  haveI : DifferentialAlgebra C E := by
    refine ⟨fun c => ?_⟩
    apply Subtype.ext
    show tensorSquareDerivation (K := K) ((algebraMap C E c : E) : R ⊗[K] R)
      = ((algebraMap C E (Differential.deriv c) : E) : R ⊗[K] R)
    show tensorSquareDerivation (K := K) (algebraMap C (R ⊗[K] R) c)
      = algebraMap C (R ⊗[K] R) (Differential.deriv c)
    exact tensorSquareDerivation_algebraMap c
  refine eq_zero_of_forall_mem_differentialPoints (C := C) (E := ↥E) ?_
  intro χ hχ
  refine h χ ?_
  intro y hy
  exact hχ ⟨y, hy⟩

/-- **Isomonodromy over a differentially closed field of constants.**  A second-order difference
equation without a base Riccati solution, whose Galois monoid at the differential points has a
differentially constrained scalar stabiliser, carries a connection over the base — with the
separating set of points supplied by Kolchin's Nullstellensatz and their Galois automorphisms
differential by the specialisation bridge. -/
theorem isomonodromy_of_no_riccati_of_differentiallyClosed
    [IsAlgClosed C] [CharZero C] [IsAlgClosed (differentialConstants C)]
    [Algebra ℚ C] [IsDifferentiallyClosed C]
    (E : Subalgebra C (R ⊗[K] R)) (hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E)
    [IsReduced E] [Algebra.FiniteType C E]
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hσδ : ∀ x : R, σR (Differential.deriv x) = Differential.deriv (σR x))
    (hsimple : IsSigmaSimple σR)
    {a₁ a₀ : K} (hric : ∀ r : K, σK r * r ≠ a₁ * r + a₀)
    (A : Matrix (Fin 2) (Fin 2) K)
    (Y : Matrix (Fin 2) (Fin 2) R) [Invertible Y]
    (hsys : Y.map ((σR : R ≃+* R) : R →+* R) = (A.map (algebraMap K R)) * Y)
    (hY1 : ∀ j, Y 1 j = σR (Y 0 j))
    (hYrec : ∀ j, σR (Y 1 j) = algebraMap K R a₁ * Y 1 j + algebraMap K R a₀ * Y 0 j)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    {m : ℕ} (aa : Fin m → C)
    (hsol : ∀ x : C, x • (1 : Matrix (Fin 2) (Fin 2) C) ∈
        Submodule.span (differentialConstants C)
          (galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ)) →
      differentialJet m x = ∑ i, aa i * differentialJet (i : ℕ) x) :
    ∃ B : Matrix (Fin 2) (Fin 2) K,
      B.map ((σK : K ≃+* K) : K →+* K) * A = matrixDeriv A + A * B :=
  isomonodromy_of_no_riccati_of_differentialSolution E b hgen hindep
    (tensorDifferentialPoints E hEδ)
    (fun e he => eq_zero_of_forall_mem_tensorDifferentialPoints E hEδ e he)
    hcompat hconstC hσδ hsimple hric A Y hsys hY1 hYrec Z hZE hZ
    (fun χ hχ x => galoisAutAt_deriv E b hgen hindep hEδ χ hχ x) aa hsol

end

end GaloisForLFunctions.HTGeometry
