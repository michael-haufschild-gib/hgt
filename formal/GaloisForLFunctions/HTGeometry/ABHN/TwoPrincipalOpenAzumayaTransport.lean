/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.PrincipalOpenFinitePlaces
import GaloisForLFunctions.HTGeometry.ABHN.AzumayaScalarExtension

/-!
# Transporting Azumaya algebras through two principal opens

If the second localization witness has numerator relation `s * r^n = a`, then it is invertible
after localizing the original ring at `r * a`.  The resulting map transports any Azumaya algebra
over the second localization to an Azumaya algebra over this single principal localization.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v

/-- An Azumaya algebra over a two-stage principal localization remains Azumaya after scalar
extension to the one-stage localization at the product of the two base-ring numerators. -/
theorem isAzumaya_twoPrincipalOpen_scalarExtension
    (R : Type u) [CommRing R] (r a : R) (n : ℕ)
    (s : Localization (Submonoid.powers r))
    (B : Type v) [Ring B]
    [Algebra (Localization (Submonoid.powers s)) B]
    [IsAzumaya (Localization (Submonoid.powers s)) B]
    (hsa : s * (algebraMap R (Localization (Submonoid.powers r)) r) ^ n =
      algebraMap R (Localization (Submonoid.powers r)) a) :
    let S := Localization (Submonoid.powers r)
    let T := Localization (Submonoid.powers (r * a))
    let U := Localization (Submonoid.powers s)
    let f : S →+* T := IsLocalization.Away.awayToAwayRight r a
    letI : Algebra S T := f.toAlgebra
    letI : Algebra U T :=
      (IsLocalization.Away.lift s
        (principalLocalization_numeratorRelation_map_isUnit R r a n s hsa)).toAlgebra
    IsAzumaya T (T ⊗[U] B) := by
  let S := Localization (Submonoid.powers r)
  let T := Localization (Submonoid.powers (r * a))
  let U := Localization (Submonoid.powers s)
  let f : S →+* T := IsLocalization.Away.awayToAwayRight r a
  letI : Algebra S T := f.toAlgebra
  have hunit : IsUnit (f s) := by
    dsimp [f]
    exact principalLocalization_numeratorRelation_map_isUnit R r a n s hsa
  letI : Algebra U T := (IsLocalization.Away.lift s hunit).toAlgebra
  exact AzumayaScalarExtension.isAzumaya_scalarExtension
    (R := U) (S := T) (A := B)

end GaloisForLFunctions.HTGeometry.ABHN
