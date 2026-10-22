import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticCauchyCohomologyDescent

/-!
# Simultaneous-local Hasse classification for Cauchy descent

All descended local restrictions assemble into one linear map.  Whenever simultaneous local
boundary membership is already known to classify global boundaries, this map embeds the global
cohomology quotient into its realized family of local profiles.  No approximation or surjectivity
onto arbitrary local families is asserted.
-/

namespace RHTower

noncomputable section

variable {R V W ι : Type*}
variable [CommRing R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- Simultaneous restriction from global Cauchy cohomology to all local boundary quotients. -/
def deningerCauchySimultaneousRestriction
    (globalBoundaries : Submodule R V)
    (localBoundaries : Submodule R W)
    (restriction : ι → V →ₗ[R] W)
    (hboundary : ∀ (i : ι) (x : V), x ∈ globalBoundaries →
      restriction i x ∈ localBoundaries) :
    (V ⧸ globalBoundaries) →ₗ[R] (ι → (W ⧸ localBoundaries)) where
  toFun q i := deningerCauchyQuotientRestriction
    globalBoundaries localBoundaries restriction hboundary i q
  map_add' x y := by
    funext i
    exact map_add _ _ _
  map_smul' c x := by
    funext i
    exact map_smul _ _ _

@[simp] theorem deningerCauchySimultaneousRestriction_apply
    (globalBoundaries : Submodule R V)
    (localBoundaries : Submodule R W)
    (restriction : ι → V →ₗ[R] W)
    (hboundary : ∀ (i : ι) (x : V), x ∈ globalBoundaries →
      restriction i x ∈ localBoundaries)
    (q : V ⧸ globalBoundaries) (i : ι) :
    deningerCauchySimultaneousRestriction
        globalBoundaries localBoundaries restriction hboundary q i =
      deningerCauchyQuotientRestriction
        globalBoundaries localBoundaries restriction hboundary i q :=
  rfl

/-- Joint local boundary classification makes simultaneous descended restriction injective. -/
theorem deningerCauchySimultaneousRestriction_injective
    (globalBoundaries : Submodule R V)
    (localBoundaries : Submodule R W)
    (restriction : ι → V →ₗ[R] W)
    (hboundary : ∀ (i : ι) (x : V), x ∈ globalBoundaries →
      restriction i x ∈ localBoundaries)
    (hclass : ∀ x : V, (∀ i : ι, restriction i x ∈ localBoundaries) →
      x ∈ globalBoundaries) :
    Function.Injective
      (deningerCauchySimultaneousRestriction
        globalBoundaries localBoundaries restriction hboundary) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply (deningerCauchyQuotientRestrictions_eq_zero_iff
    globalBoundaries localBoundaries restriction hboundary hclass (x - y)).1
  intro i
  rw [map_sub]
  have hi := congrFun hxy i
  change deningerCauchyQuotientRestriction globalBoundaries localBoundaries
    restriction hboundary i x =
      deningerCauchyQuotientRestriction globalBoundaries localBoundaries
        restriction hboundary i y at hi
  rw [hi, sub_self]

/-- Equality at every local restriction is equivalent to equality of global quotient classes. -/
theorem deningerCauchy_congr_hasse_iff
    (globalBoundaries : Submodule R V)
    (localBoundaries : Submodule R W)
    (restriction : ι → V →ₗ[R] W)
    (hboundary : ∀ (i : ι) (x : V), x ∈ globalBoundaries →
      restriction i x ∈ localBoundaries)
    (hclass : ∀ x : V, (∀ i : ι, restriction i x ∈ localBoundaries) →
      x ∈ globalBoundaries)
    (x y : V ⧸ globalBoundaries) :
    (∀ i : ι,
      deningerCauchyQuotientRestriction
          globalBoundaries localBoundaries restriction hboundary i x =
        deningerCauchyQuotientRestriction
          globalBoundaries localBoundaries restriction hboundary i y) ↔
      (x = y) := by
  constructor
  · intro hlocal
    apply deningerCauchySimultaneousRestriction_injective
      globalBoundaries localBoundaries restriction hboundary hclass
    funext i
    exact hlocal i
  · rintro rfl i
    rfl

/-- The global cohomology quotient is linearly equivalent to the subspace of simultaneous local
profiles that it actually realizes. -/
noncomputable def deningerCauchyHasseEquivRealizedProfiles
    (globalBoundaries : Submodule R V)
    (localBoundaries : Submodule R W)
    (restriction : ι → V →ₗ[R] W)
    (hboundary : ∀ (i : ι) (x : V), x ∈ globalBoundaries →
      restriction i x ∈ localBoundaries)
    (hclass : ∀ x : V, (∀ i : ι, restriction i x ∈ localBoundaries) →
      x ∈ globalBoundaries) :
    (V ⧸ globalBoundaries) ≃ₗ[R]
      LinearMap.range (deningerCauchySimultaneousRestriction
        globalBoundaries localBoundaries restriction hboundary) :=
  LinearEquiv.ofInjective _
    (deningerCauchySimultaneousRestriction_injective
      globalBoundaries localBoundaries restriction hboundary hclass)

end

end RHTower
