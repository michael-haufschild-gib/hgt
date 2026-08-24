import GaloisForLFunctions.HTGeometry.ABHN.RestrictedBrauerDFinsuppHasse

/-!
# Failure witnesses for restricted local Brauer families

Restricted local Brauer families are dependent finitely supported coordinate families. Hence
inequality has a witness place, and nonzero families have a place carrying a nonsplit class.
Unlike rigid scalar-extension failures, these are existential local witnesses.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-- Distinct restricted number-field local Brauer families differ at some place. -/
theorem numberFieldRestrictedLocalBrauer_ne_iff_exists_place_ne
    (K : Type u) [Field K] [NumberField K]
    (x y : RestrictedLocalBrauerClasses K) :
    x ≠ y ↔ ∃ v, x.toLocalBrauerClasses v ≠ y.toLocalBrauerClasses v := by
  classical
  have h := not_congr (numberFieldRestrictedLocalBrauer_congr_hasse_iff K x y)
  simpa only [not_forall] using h

/-- A nonzero restricted number-field local Brauer family is nonsplit at some place. -/
theorem numberFieldRestrictedLocalBrauer_ne_zero_iff_exists_place_nonSplit
    (K : Type u) [Field K] [NumberField K]
    (x : RestrictedLocalBrauerClasses K) :
    x ≠ 0 ↔ ∃ v,
      x.toLocalBrauerClasses v ≠ brauerSplitClass (completion K v) := by
  classical
  have h := not_congr (numberFieldRestrictedLocalBrauer_eq_zero_hasse_iff K x)
  simpa only [not_forall] using h

/-- Distinct restricted `F(t)` local Brauer families differ at some place. -/
theorem rationalFunctionRestrictedLocalBrauer_ne_iff_exists_place_ne
    (F : Type u) [Field F] [Finite F]
    (x y : RationalFunctionRestrictedLocalBrauerClasses F) :
    x ≠ y ↔ ∃ v, x.toLocalBrauerClasses v ≠ y.toLocalBrauerClasses v := by
  classical
  have h := not_congr (rationalFunctionRestrictedLocalBrauer_congr_hasse_iff F x y)
  simpa only [not_forall] using h

/-- A nonzero restricted `F(t)` local Brauer family is nonsplit at some place. -/
theorem rationalFunctionRestrictedLocalBrauer_ne_zero_iff_exists_place_nonSplit
    (F : Type u) [Field F] [Finite F]
    (x : RationalFunctionRestrictedLocalBrauerClasses F) :
    x ≠ 0 ↔ ∃ v,
      x.toLocalBrauerClasses v ≠ brauerSplitClass (rationalFunctionCompletion F v) := by
  classical
  have h := not_congr (rationalFunctionRestrictedLocalBrauer_eq_zero_hasse_iff F x)
  simpa only [not_forall] using h

end GaloisForLFunctions.HTGeometry.ABHN
