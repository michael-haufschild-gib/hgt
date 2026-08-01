import GaloisForLFunctions.HTGeometry.NaturalIrrationalities
import GaloisForLFunctions.HTGeometry.RootFieldTransport

/-!
# Base change along a field in which the base is relatively algebraically closed

The splitting field of a separable polynomial and a second field meet in the base as soon as the
second field carries no algebraic element beyond the base: every element of the splitting field is
algebraic.

So when the two together generate the ambient field, restriction is an isomorphism from the
automorphisms over the second field to the Galois group of the polynomial over the base — base
change does not shrink the group.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- **Every element of the root field is algebraic over the base.** -/
theorem isAlgebraic_of_mem_rootField {p : Polynomial F}
    (hsplit : (p.map (algebraMap F L)).Splits) {x : L}
    (hx : x ∈ rootField F (L := L) p) : IsAlgebraic F x := by
  haveI := isSplittingField_rootField (F := F) (p := p) (L := L) hsplit
  haveI : FiniteDimensional F (rootField F (L := L) p) :=
    Polynomial.IsSplittingField.finiteDimensional _ p
  have halg : IsAlgebraic F (⟨x, hx⟩ : rootField F (L := L) p) :=
    (IsIntegral.of_finite F (⟨x, hx⟩ : rootField F (L := L) p)).isAlgebraic
  have hinj : Function.Injective (algebraMap (rootField F (L := L) p) L) :=
    (algebraMap (rootField F (L := L) p) L).injective
  exact (isAlgebraic_algebraMap_iff (A := L) hinj).2 halg

/-- **The root field and a relatively closed field meet in the base.** -/
theorem rootField_inf_eq_bot {p : Polynomial F}
    (hsplit : (p.map (algebraMap F L)).Splits) {M : IntermediateField F L}
    (hM : ∀ x : L, x ∈ M → IsAlgebraic F x → x ∈ (⊥ : IntermediateField F L)) :
    rootField F (L := L) p ⊓ M = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  exact hM x hx.2 (isAlgebraic_of_mem_rootField hsplit hx.1)

/-- **Base change along a relatively closed field preserves the Galois group.** -/
noncomputable def baseChangeRelativelyClosed {p : Polynomial F} (hsep : p.Separable)
    (hsplit : (p.map (algebraMap F L)).Splits) {M : IntermediateField F L}
    [FiniteDimensional M L] [IsGalois M L]
    (hM : ∀ x : L, x ∈ M → IsAlgebraic F x → x ∈ (⊥ : IntermediateField F L))
    (htop : rootField F (L := L) p ⊔ M = ⊤) :
    (L ≃ₐ[M] L) ≃* (rootField F (L := L) p ≃ₐ[F] rootField F (L := L) p) := by
  haveI := isSplittingField_rootField (F := F) (p := p) (L := L) hsplit
  haveI : FiniteDimensional F (rootField F (L := L) p) :=
    Polynomial.IsSplittingField.finiteDimensional _ p
  haveI : IsGalois F (rootField F (L := L) p) := IsGalois.of_separable_splitting_field hsep
  haveI : Normal F (rootField F (L := L) p) := IsGalois.to_normal
  exact compositumRestrictEquiv htop (rootField_inf_eq_bot hsplit hM)

end GaloisForLFunctions.HTGeometry
