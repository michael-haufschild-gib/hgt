import GaloisForLFunctions.RHTower.DeningerMeyerCompleteSpace

/-!
# The two Deninger spaces are Fréchet

Both `DeningerCircle P` (the smooth functions on the circle `ℝ/Pℤ`) and `DeningerMeyerSource`
(Meyer's source `H_-`) carry a countable separating family of seminorms and are complete.  This file
records the two structural consequences: their uniformities are countably generated, hence they are
pseudometrizable, hence — being complete — completely pseudometrizable.  That last instance is the
hypothesis of the Fréchet open mapping theorem `GaloisForLFunctions.isOpenMap_of_surjective` and of
its closed-range corollary.

* `DeningerCircle.instIsCompletelyPseudoMetrizableSpace`
* `DeningerMeyerSource.instIsCompletelyPseudoMetrizableSpace`
-/

namespace RHTower

open Filter Topology Uniformity TopologicalSpace

/-- The uniformity of the circle space is countably generated. -/
instance DeningerCircle.instIsCountablyGeneratedUniformity (P : {x : ℝ // 0 < x}) :
    (𝓤 (DeningerCircle P)).IsCountablyGenerated := by
  rw [uniformity_eq_comap_nhds_zero]
  infer_instance

/-- The circle space is pseudometrizable. -/
instance DeningerCircle.instPseudoMetrizableSpace (P : {x : ℝ // 0 < x}) :
    PseudoMetrizableSpace (DeningerCircle P) :=
  UniformSpace.pseudoMetrizableSpace

/-- **The circle space is a Fréchet space**: completely pseudometrizable. -/
instance DeningerCircle.instIsCompletelyPseudoMetrizableSpace (P : {x : ℝ // 0 < x}) :
    IsCompletelyPseudoMetrizableSpace (DeningerCircle P) := by
  infer_instance

/-- The uniformity of Meyer's source is countably generated. -/
instance DeningerMeyerSource.instIsCountablyGeneratedUniformity :
    (𝓤 DeningerMeyerSource).IsCountablyGenerated := by
  rw [uniformity_eq_comap_nhds_zero]
  infer_instance

/-- Meyer's source is pseudometrizable. -/
instance DeningerMeyerSource.instPseudoMetrizableSpace :
    PseudoMetrizableSpace DeningerMeyerSource :=
  UniformSpace.pseudoMetrizableSpace

/-- **Meyer's source is a Fréchet space**: completely pseudometrizable. -/
instance DeningerMeyerSource.instIsCompletelyPseudoMetrizableSpace :
    IsCompletelyPseudoMetrizableSpace DeningerMeyerSource := by
  infer_instance

end RHTower
