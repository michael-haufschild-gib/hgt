import GaloisForLFunctions.SelbergClass.MeromorphicTensorAgreement

/-!
# Entire shifts of meromorphic tensor presentations

An entire additive ambiguity should not alter a presented tensor's displayed
denominator.  This module records that operation at both pointwise regular
values and in the fraction field of entire functions.  It makes no claim about
actual poles after cancellation, nor about meromorphic continuation.
-/

open Complex Filter Set Topology

namespace GaloisForLFunctions.SelbergClass

open GaloisForLFunctions.HTGeometry

namespace MeromorphicTensorPresentation

variable {N : ℕ}

/-- Add an entire tensor to a quotient presentation while retaining its
displayed denominator. -/
noncomputable def addEntire (T : MeromorphicTensorPresentation N)
    (E : entireSubring (Fin N → ℂ)) : MeromorphicTensorPresentation N where
  numerator := T.numerator + E * T.denominator
  denominator := T.denominator
  denominator_ne_zero := T.denominator_ne_zero

/-- On the original regular locus, adding an entire presentation has its usual
pointwise meaning. -/
theorem value_addEntire (T : MeromorphicTensorPresentation N)
    (E : entireSubring (Fin N → ℂ)) {s : Fin N → ℂ}
    (hs : s ∈ T.regularSet) :
    (T.addEntire E).value s = T.value s + (E : (Fin N → ℂ) → ℂ) s := by
  change
    ((T.numerator : (Fin N → ℂ) → ℂ) s +
      (E : (Fin N → ℂ) → ℂ) s * (T.denominator : (Fin N → ℂ) → ℂ) s) /
        (T.denominator : (Fin N → ℂ) → ℂ) s =
      (T.numerator : (Fin N → ℂ) → ℂ) s / (T.denominator : (Fin N → ℂ) → ℂ) s +
        (E : (Fin N → ℂ) → ℂ) s
  change (T.denominator : (Fin N → ℂ) → ℂ) s ≠ 0 at hs
  field_simp [hs]

/-- An entire additive ambiguity preserves the displayed regular locus. -/
theorem regularSet_addEntire (T : MeromorphicTensorPresentation N)
    (E : entireSubring (Fin N → ℂ)) :
    (T.addEntire E).regularSet = T.regularSet := rfl

/-- An entire additive ambiguity preserves the candidate polar set of the
chosen quotient presentation.  It does not assert equality of actual polar
sets after possible numerator-denominator cancellation. -/
theorem candidatePolarSet_addEntire (T : MeromorphicTensorPresentation N)
    (E : entireSubring (Fin N → ℂ)) :
    (T.addEntire E).candidatePolarSet = T.candidatePolarSet := rfl

/-- In the fraction field of entire functions, `addEntire` is ordinary
addition by the entire tensor. -/
theorem toEntireField_addEntire (T : MeromorphicTensorPresentation N)
    (E : entireSubring (Fin N → ℂ)) :
    (T.addEntire E).toEntireField =
      T.toEntireField + algebraMap (entireSubring (Fin N → ℂ))
        (EntireField (Fin N → ℂ)) E := by
  change
    (algebraMap (entireSubring (Fin N → ℂ)) (EntireField (Fin N → ℂ))
        (T.numerator + E * T.denominator) /
      algebraMap (entireSubring (Fin N → ℂ)) (EntireField (Fin N → ℂ)) T.denominator) =
      (algebraMap (entireSubring (Fin N → ℂ)) (EntireField (Fin N → ℂ)) T.numerator /
        algebraMap (entireSubring (Fin N → ℂ)) (EntireField (Fin N → ℂ)) T.denominator) +
      algebraMap (entireSubring (Fin N → ℂ)) (EntireField (Fin N → ℂ)) E
  rw [map_add, map_mul]
  have hden := T.denominator_toEntireField_ne_zero
  field_simp [hden]

end MeromorphicTensorPresentation

end GaloisForLFunctions.SelbergClass
