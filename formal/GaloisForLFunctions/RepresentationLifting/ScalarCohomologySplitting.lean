import GaloisForLFunctions.RepresentationLifting.CohomologicalTrace

/-!
# Scalar cohomology splits off in odd dimension

In characteristic two, the trace of the identity of an odd-dimensional
representation is one. Consequently trace is a left inverse, in every degree,
to the coefficient map `a ↦ a * id`. Scalar cohomology therefore embeds into
endomorphism-valued cohomology. This is a positive application of the trace
mechanism in Scavia's Lemma 6.1.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RepresentationLifting

universe u

variable {k G : Type u} [Field k] [CharP k 2] [Group G]

/-- Trace retracts the scalar inclusion on cohomology in odd dimension and characteristic two. -/
theorem oddDimensionalRepresentation_cohomology_trace (m : ℕ)
    (ρ : Representation k G (Fin (2 * m + 1) → k)) (n : ℕ) :
    (groupCohomology.functor k G n).map (scalarHom (𝟙 (Rep.of ρ))) ≫
        (groupCohomology.functor k G n).map (endomorphismTrace (Rep.of ρ)) =
      𝟙 (groupCohomology (Rep.trivial k G k) n) := by
  have htrace : LinearMap.trace k (Rep.of ρ)
      (𝟙 (Rep.of ρ) : Rep.of ρ ⟶ Rep.of ρ).hom.toLinearMap = 1 := by
    change LinearMap.trace k (Fin (2 * m + 1) → k) LinearMap.id = 1
    rw [LinearMap.trace_id, Module.finrank_fin_fun]
    have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      htwo, zero_mul, zero_add]
  rw [scalarHom_trace_cohomology, htrace, one_smul]

/-- A scalar cohomology class cannot vanish after multiplication by the identity. -/
theorem oddDimensionalRepresentation_scalar_injective (m : ℕ)
    (ρ : Representation k G (Fin (2 * m + 1) → k)) (n : ℕ) :
    Function.Injective
      ((groupCohomology.functor k G n).map (scalarHom (𝟙 (Rep.of ρ)))).hom := by
  intro a b hab
  have ha := congrArg (fun f : groupCohomology (Rep.trivial k G k) n ⟶
    groupCohomology (Rep.trivial k G k) n => f.hom a)
    (oddDimensionalRepresentation_cohomology_trace m ρ n)
  have hb := congrArg (fun f : groupCohomology (Rep.trivial k G k) n ⟶
    groupCohomology (Rep.trivial k G k) n => f.hom b)
    (oddDimensionalRepresentation_cohomology_trace m ρ n)
  exact ha.symm.trans ((congrArg
    ((groupCohomology.functor k G n).map (endomorphismTrace (Rep.of ρ))).hom hab).trans hb)

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.oddDimensionalRepresentation_scalar_injective
