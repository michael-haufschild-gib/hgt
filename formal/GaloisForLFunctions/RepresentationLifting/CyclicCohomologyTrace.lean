import GaloisForLFunctions.RepresentationLifting.CyclicProductRepresentation
import GaloisForLFunctions.RepresentationLifting.CohomologicalTrace

/-!
# Cohomological trace vanishing for cyclic norm representations

In characteristic two, the norm-difference representation has no endomorphism
whose scalar line is detected by the cohomological trace. This holds in every
degree: equivariance forces commutation with the acyclic differential, and the
resulting ordinary trace is zero.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RepresentationLifting

universe u

variable (k G : Type u) [Field k] [CharP k 2]
  [CommGroup G] [Fintype G] [IsCyclic G]

/-- Every scalar line defined by an endomorphism has zero cohomological trace. -/
theorem cyclicProductRepresentation_cohomologyTrace_zero
    (T : Rep.of (cyclicProductRepresentation k G) ⟶
      Rep.of (cyclicProductRepresentation k G)) (n : ℕ) :
    (groupCohomology.functor k (G × Multiplicative k) n).map (scalarHom T) ≫
        (groupCohomology.functor k (G × Multiplicative k) n).map
          (endomorphismTrace (Rep.of (cyclicProductRepresentation k G))) = 0 := by
  rw [scalarHom_trace_cohomology, cyclicProductRepresentation_endomorphism_trace, zero_smul]
  rfl

/-- Element form: every scalar class has zero trace after multiplication by an endomorphism. -/
theorem cyclicProductRepresentation_cohomologyTrace_apply
    (T : Rep.of (cyclicProductRepresentation k G) ⟶
      Rep.of (cyclicProductRepresentation k G)) (n : ℕ)
    (b : groupCohomology (Rep.trivial k (G × Multiplicative k) k) n) :
    ((groupCohomology.functor k (G × Multiplicative k) n).map
      (endomorphismTrace (Rep.of (cyclicProductRepresentation k G)))).hom
        (((groupCohomology.functor k (G × Multiplicative k) n).map (scalarHom T)).hom b) = 0 := by
  exact congrArg (fun m : groupCohomology (Rep.trivial k (G × Multiplicative k) k) n ⟶
    groupCohomology (Rep.trivial k (G × Multiplicative k) k) n => m.hom b)
      (cyclicProductRepresentation_cohomologyTrace_zero k G T n)

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.cyclicProductRepresentation_cohomologyTrace_zero
