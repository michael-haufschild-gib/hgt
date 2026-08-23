import GaloisForLFunctions.HTGeometry.HasseExactSequence
import GaloisForLFunctions.RHTower.DeningerTreeShortExact

/-!
# Hasse classification on the Bass--Serre tree

The augmentation is the sole obstruction to expressing a finite vertex distribution as a tree
boundary.  Thus vertex distributions modulo edge transport are classified by their total mass.
This is a local--global principle on the combinatorial tree underlying the Deninger pushout route.
-/

namespace RHTower

open Monoid Monoid.PushoutI
open GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {ι : Type u} {G : ι → Type u} {H : Type u} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} (k : Type u) [Field k]

/-- Tree boundary followed by total mass is exact.  No injectivity condition on the pushout maps is
needed for this middle-term statement. -/
theorem deningerTree_functionExact :
    Function.Exact (deningerTreeBoundary (φ := φ) k) (deningerTreeAug k) := by
  intro x
  constructor
  · exact deningerTree_connected k x
  · rintro ⟨y, rfl⟩
    have h := DFunLike.congr_fun (deningerTreeAug_comp_boundary (φ := φ) k) y
    simpa using h

/-- Finite vertex distributions modulo edge transport are classified by total mass. -/
noncomputable def deningerTreeHasseQuotientEquiv :
    (MonoidAlgebra k (DeningerTreeVertex φ) ⧸
      LinearMap.range (deningerTreeBoundary (φ := φ) k)) ≃ₗ[k] k :=
  linearHasseQuotientEquiv
    (deningerTreeBoundary (φ := φ) k) (deningerTreeAug k)
    (deningerTree_functionExact k) (deningerTreeAug_surjective k)

/-- The tree Hasse equivalence is induced by total mass. -/
@[simp] theorem deningerTreeHasseQuotientEquiv_mk
    (x : MonoidAlgebra k (DeningerTreeVertex φ)) :
    deningerTreeHasseQuotientEquiv k (Submodule.Quotient.mk x) = deningerTreeAug k x := by
  simp [deningerTreeHasseQuotientEquiv]

/-- Two vertex distributions differ by edge transport exactly when they have equal total mass. -/
theorem deningerTree_congr_hasse_iff
    (x y : MonoidAlgebra k (DeningerTreeVertex φ)) :
    x - y ∈ LinearMap.range (deningerTreeBoundary (φ := φ) k) ↔
      deningerTreeAug k x = deningerTreeAug k y :=
  linearHasse_congr_iff
    (deningerTreeBoundary (φ := φ) k) (deningerTreeAug k)
    (deningerTree_functionExact k) x y

/-- Every total mass has a vertex distribution representative, unique modulo edge transport. -/
theorem deningerTree_exists_unique_mod_boundary (c : k) :
    ∃ x : MonoidAlgebra k (DeningerTreeVertex φ), deningerTreeAug k x = c ∧
      ∀ y, deningerTreeAug k y = c ↔
        y - x ∈ LinearMap.range (deningerTreeBoundary (φ := φ) k) :=
  linearHasse_exists_unique_mod_global
    (deningerTreeBoundary (φ := φ) k) (deningerTreeAug k)
    (deningerTree_functionExact k) (deningerTreeAug_surjective k) c

/-- Canonical root normal form: every distribution is congruent to its total mass at the root. -/
theorem deningerTree_sub_rootMass_mem_boundary
    (x : MonoidAlgebra k (DeningerTreeVertex φ)) :
    x - MonoidAlgebra.single
        (DeningerTreeVertex.ofBase (QuotientGroup.mk 1 : PushoutI φ ⧸ _))
        (deningerTreeAug k x) ∈
      LinearMap.range (deningerTreeBoundary (φ := φ) k) := by
  apply (deningerTree_congr_hasse_iff k _ _).2
  rw [deningerTreeAug_single]

end

end RHTower
