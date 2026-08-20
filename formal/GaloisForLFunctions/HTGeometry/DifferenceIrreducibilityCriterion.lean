import GaloisForLFunctions.HTGeometry.TorsorSpecializationSeparation
import GaloisForLFunctions.HTGeometry.DifferenceSemiInvariantSolution

/-!
# Irreducibility from the absence of a Riccati solution

A solution of a second-order difference equation that every specialisation of the torsor merely
scales is hyperexponential over the base: separation of specialisations turns the proportionality
into the tensor identity `y ⊗ σ y = σ y ⊗ y`, a linear functional turns that into `σ y = r y` with
`r` in the base, and `σ`-simplicity makes `y` a unit, so `r` solves the Riccati equation of the
recurrence.

An equation whose Riccati equation has no solution in the base therefore has no such solution — the
Galois action leaves no line of the solution space stable, which is the irreducibility hypothesis
the classification of the Galois group needs.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

variable {K R k : Type*} [Field K] [CommRing R] [Nontrivial R] [Algebra K R]
  [Field k] [IsAlgClosed k] [Algebra k K] [Algebra k R] [IsScalarTower k K R]

/-- The right embedding of the Picard--Vessiot ring in its tensor square, over the constants. -/
def rightEmbedding (K : Type*) [Field K] {R : Type*} [CommRing R] [Algebra K R]
    (k : Type*) [Field k] [Algebra k K] [Algebra k R] [IsScalarTower k K R] :
    R →ₐ[k] R ⊗[K] R :=
  (Algebra.TensorProduct.includeRight : R →ₐ[K] R ⊗[K] R).restrictScalars k

omit [Nontrivial R] [IsAlgClosed k] in
@[simp] theorem rightEmbedding_apply (r : R) :
    rightEmbedding K k r = (1 : R) ⊗ₜ[K] r := rfl

omit [IsAlgClosed k] in
/-- **A second-order recurrence without a base Riccati solution has no semi-invariant solution.**
If a separating set of specialisations of the torsor all scale the solution, the solution is
hyperexponential over the base, and its ratio solves the Riccati equation. -/
theorem not_forall_specialization_semiInvariant_of_no_riccati_subset
    (E : Subalgebra k (R ⊗[K] R))
    {ι : Type*} (b : Module.Basis ι k E)
    (hgen : Algebra.adjoin k
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    (S : Set (E →ₐ[k] k)) (hsep : ∀ e : E, (∀ χ ∈ S, χ e = 0) → e = 0)
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (hsimple : IsSigmaSimple σR)
    {a₁ a₀ : K} (hric : ∀ r : K, σK r * r ≠ a₁ * r + a₀)
    {y : R} (hy : y ≠ 0)
    (hrec : σR (σR y) = algebraMap K R a₁ * σR y + algebraMap K R a₀ * y) :
    ¬ ∀ χ ∈ S,
        y * (torsorSpecialization E b hgen hindep χ) (rightEmbedding K k (σR y))
          = σR y * (torsorSpecialization E b hgen hindep χ) (rightEmbedding K k y) := by
  intro h
  have hmul := mul_comm_embeddings_of_forall_specialization_subset E b hgen hindep S hsep
    (rightEmbedding K k) h
  have hleft : ∀ r : R, algebraMap R (R ⊗[K] R) r = r ⊗ₜ[K] (1 : R) := fun r => rfl
  have hprod : ∀ r s : R, (r ⊗ₜ[K] (1 : R)) * ((1 : R) ⊗ₜ[K] s) = r ⊗ₜ[K] s := by
    intro r s
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hleft, hleft, rightEmbedding_apply, rightEmbedding_apply, hprod, hprod] at hmul
  obtain ⟨r, hr⟩ := exists_riccati_of_tmul_comm hcompat hsimple hy hrec hmul
  exact hric r hr

/-- The same statement for the full set of specialisations. -/
theorem not_forall_specialization_semiInvariant_of_no_riccati
    (E : Subalgebra k (R ⊗[K] R)) [IsReduced E] [Algebra.FiniteType k E]
    {ι : Type*} (b : Module.Basis ι k E)
    (hgen : Algebra.adjoin k
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (hsimple : IsSigmaSimple σR)
    {a₁ a₀ : K} (hric : ∀ r : K, σK r * r ≠ a₁ * r + a₀)
    {y : R} (hy : y ≠ 0)
    (hrec : σR (σR y) = algebraMap K R a₁ * σR y + algebraMap K R a₀ * y) :
    ¬ ∀ χ : E →ₐ[k] k,
        y * (torsorSpecialization E b hgen hindep χ) (rightEmbedding K k (σR y))
          = σR y * (torsorSpecialization E b hgen hindep χ) (rightEmbedding K k y) := by
  intro h
  exact not_forall_specialization_semiInvariant_of_no_riccati_subset E b hgen hindep Set.univ
    (fun _ he => eq_zero_of_forall_algHom_eq_zero (fun χ => he χ (Set.mem_univ χ)))
    hcompat hsimple hric hy hrec (fun χ _ => h χ)

end

end GaloisForLFunctions.HTGeometry
