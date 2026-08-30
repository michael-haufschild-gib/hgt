import GaloisForLFunctions.HTGeometry.NumberFieldMixedRealCoordinates
import GaloisForLFunctions.HTGeometry.NumberFieldMixedVectorCoordinates

/-!
# Split archimedean coordinates for number-field vectors

Applying the real/complex Minkowski splitting coordinatewise gives a canonical placewise
coordinate system for vectors over a number field.  Composing with the integral-basis coordinate
system supplies the exact change of coordinates needed to define the real/Hermitian
archimedean symmetric space without retaining a chosen coordinate equivalence.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Apply the canonical split real Minkowski coordinates independently to each vector entry. -/
def numberFieldMixedVectorPlaceCoordinates (n : ℕ) :
    (Fin n → mixedEmbedding.mixedSpace K) ≃ₗ[ℝ]
      (Fin n × numberFieldMixedRealCoordinateIndex K → ℝ) where
  toFun z p := numberFieldMixedRealCoordinates (z p.1) p.2
  invFun x i := numberFieldMixedRealCoordinates.symm (fun k => x (i, k))
  left_inv z := by
    funext i
    exact numberFieldMixedRealCoordinates.symm_apply_apply (z i)
  right_inv x := by
    funext p
    exact congrFun
      (numberFieldMixedRealCoordinates.apply_symm_apply (fun k => x (p.1, k))) p.2
  map_add' z z' := by
    funext p
    exact congrFun (numberFieldMixedRealCoordinates.map_add (z p.1) (z' p.1)) p.2
  map_smul' c z := by
    funext p
    exact congrFun (numberFieldMixedRealCoordinates.map_smul c (z p.1)) p.2

/-- Change from canonical integral-basis coordinates to split archimedean coordinates. -/
def numberFieldCanonicalToPlaceCoordinates (n : ℕ) :
    (Fin (n * Module.finrank ℚ K) → ℝ) ≃ₗ[ℝ]
      (Fin n × numberFieldMixedRealCoordinateIndex K → ℝ) :=
  (numberFieldMixedVectorContinuousLinearEquiv K n).toLinearEquiv.symm.trans
    (numberFieldMixedVectorPlaceCoordinates n)

@[simp]
theorem numberFieldCanonicalToPlaceCoordinates_apply
    (n : ℕ) (z : Fin n → mixedEmbedding.mixedSpace K) :
    numberFieldCanonicalToPlaceCoordinates (K := K) n
        (numberFieldMixedVectorContinuousLinearEquiv K n z) =
      numberFieldMixedVectorPlaceCoordinates n z := by
  simp [numberFieldCanonicalToPlaceCoordinates]

end

end GaloisForLFunctions.HTGeometry
