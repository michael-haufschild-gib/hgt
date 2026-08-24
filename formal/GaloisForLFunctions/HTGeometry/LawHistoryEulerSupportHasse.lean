import GaloisForLFunctions.HTGeometry.ABHN.FinsuppReciprocitySupportCardinality
import GaloisForLFunctions.HTGeometry.LawHistoryTransgressionPages

/-!
# Hasse support rigidity for the law-history Euler profile

The six finite-dimensional terms in the law-history transgression sequence have vanishing
alternating sum.  Packaging their signed dimensions as a finite profile shows that a nonzero
homological term cannot be the only active term in the sequence.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.HTGeometry.ABHN

/-- Signed dimension profile of the six-term law-history sequence. -/
noncomputable def lawHistoryEulerProfile
    {k X Y Z : Type*} [Field k]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [AddCommGroup Z] [Module k Z]
    [FiniteDimensional k X] [FiniteDimensional k Y] [FiniteDimensional k Z]
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) : Fin 6 →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm ![
    (Module.finrank k (LinearMap.ker f) : ℤ),
    -(Module.finrank k (LinearMap.ker (g.comp f)) : ℤ),
    (Module.finrank k (LinearMap.ker g) : ℤ),
    -(Module.finrank k (Y ⧸ LinearMap.range f) : ℤ),
    (Module.finrank k (Z ⧸ LinearMap.range (g.comp f)) : ℤ),
    -(Module.finrank k (Z ⧸ LinearMap.range g) : ℤ)]

@[simp]
theorem lawHistoryEulerProfile_zero
    {k X Y Z : Type*} [Field k]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [AddCommGroup Z] [Module k Z]
    [FiniteDimensional k X] [FiniteDimensional k Y] [FiniteDimensional k Z]
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    lawHistoryEulerProfile f g 0 = Module.finrank k (LinearMap.ker f) := rfl

@[simp]
theorem lawHistoryEulerProfile_one
    {k X Y Z : Type*} [Field k]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [AddCommGroup Z] [Module k Z]
    [FiniteDimensional k X] [FiniteDimensional k Y] [FiniteDimensional k Z]
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    lawHistoryEulerProfile f g 1 =
      -(Module.finrank k (LinearMap.ker (g.comp f)) : ℤ) := rfl

@[simp]
theorem lawHistoryEulerProfile_two
    {k X Y Z : Type*} [Field k]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [AddCommGroup Z] [Module k Z]
    [FiniteDimensional k X] [FiniteDimensional k Y] [FiniteDimensional k Z]
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    lawHistoryEulerProfile f g 2 = Module.finrank k (LinearMap.ker g) := rfl

@[simp]
theorem lawHistoryEulerProfile_three
    {k X Y Z : Type*} [Field k]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [AddCommGroup Z] [Module k Z]
    [FiniteDimensional k X] [FiniteDimensional k Y] [FiniteDimensional k Z]
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    lawHistoryEulerProfile f g 3 =
      -(Module.finrank k (Y ⧸ LinearMap.range f) : ℤ) := rfl

@[simp]
theorem lawHistoryEulerProfile_four
    {k X Y Z : Type*} [Field k]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [AddCommGroup Z] [Module k Z]
    [FiniteDimensional k X] [FiniteDimensional k Y] [FiniteDimensional k Z]
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    lawHistoryEulerProfile f g 4 =
      Module.finrank k (Z ⧸ LinearMap.range (g.comp f)) := rfl

@[simp]
theorem lawHistoryEulerProfile_five
    {k X Y Z : Type*} [Field k]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [AddCommGroup Z] [Module k Z]
    [FiniteDimensional k X] [FiniteDimensional k Y] [FiniteDimensional k Z]
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    lawHistoryEulerProfile f g 5 =
      -(Module.finrank k (Z ⧸ LinearMap.range g) : ℤ) := rfl

/-- The law-history Euler profile has total signed dimension zero. -/
theorem lawHistoryEulerProfile_sum_eq_zero
    {k X Y Z : Type*} [Field k]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [AddCommGroup Z] [Module k Z]
    [FiniteDimensional k X] [FiniteDimensional k Y] [FiniteDimensional k Z]
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    (lawHistoryEulerProfile f g).sum (fun _ z => z) = 0 := by
  rw [Finsupp.sum_fintype _ _ (by intro; rfl)]
  change ∑ i : Fin 6, (![
    (Module.finrank k (LinearMap.ker f) : ℤ),
    -(Module.finrank k (LinearMap.ker (g.comp f)) : ℤ),
    (Module.finrank k (LinearMap.ker g) : ℤ),
    -(Module.finrank k (Y ⧸ LinearMap.range f) : ℤ),
    (Module.finrank k (Z ⧸ LinearMap.range (g.comp f)) : ℤ),
    -(Module.finrank k (Z ⧸ LinearMap.range g) : ℤ)] : Fin 6 → ℤ) i = 0
  simp [Fin.sum_univ_succ]
  have h := lawHistory_alternating_sum_eq_zero f g
  omega

/-- Every nonzero law-history homological coordinate has a distinct nonzero companion. -/
theorem lawHistoryEulerProfile_exists_other_nonzero_coordinate
    {k X Y Z : Type*} [Field k]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [AddCommGroup Z] [Module k Z]
    [FiniteDimensional k X] [FiniteDimensional k Y] [FiniteDimensional k Z]
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) {i : Fin 6}
    (hi : lawHistoryEulerProfile f g i ≠ 0) :
    ∃ j : Fin 6, j ≠ i ∧ lawHistoryEulerProfile f g j ≠ 0 :=
  finsupp_exists_other_nonzero_place_of_sum_eq_zero
    (lawHistoryEulerProfile f g) (lawHistoryEulerProfile_sum_eq_zero f g) hi

/-- A nonzero law-history Euler profile occupies at least two homological coordinates. -/
theorem lawHistoryEulerProfile_two_le_support_card
    {k X Y Z : Type*} [Field k]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [AddCommGroup Z] [Module k Z]
    [FiniteDimensional k X] [FiniteDimensional k Y] [FiniteDimensional k Z]
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z)
    (hne : lawHistoryEulerProfile f g ≠ 0) :
    2 ≤ (lawHistoryEulerProfile f g).support.card :=
  finsupp_two_le_support_card_of_sum_eq_zero
    (lawHistoryEulerProfile f g) (lawHistoryEulerProfile_sum_eq_zero f g) hne

end GaloisForLFunctions.HTGeometry
