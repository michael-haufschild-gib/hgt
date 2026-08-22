import GaloisForLFunctions.HTGeometry.FiniteUnitaryHaarMeasureLaw

/-!
# Topological Haar interface for finite unitary groups

This is the `U(d)` counterpart of the special-unitary Haar topology layer.
It exposes normalized finite-unitary Haar as a Haar measure and records its
right invariance, which allows a local exponential-coordinate measure to be
averaged into Haar measure.
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Finite unitary matrix groups inherit second countability from their
finite-dimensional complex matrix ambient space. -/
noncomputable instance finiteUnitarySecondCountableTopology
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    SecondCountableTopology (Matrix.unitaryGroup ι ℂ) := by
  letI : Finite ι := Fintype.finite inferInstance
  letI : Countable ι := Finite.to_countable
  letI : SecondCountableTopology (Matrix ι ι ℂ) := by
    change SecondCountableTopology (ι → ι → ℂ)
    infer_instance
  exact Topology.IsInducing.subtypeVal.secondCountableTopology

/-- The normalized finite-unitary Haar law has Mathlib's complete Haar
interface. -/
noncomputable instance finiteUnitaryHaarIsHaarMeasure
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    IsHaarMeasure (finiteUnitaryHaar ι) := by
  let K : PositiveCompacts (Matrix.unitaryGroup ι ℂ) :=
    ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  change IsHaarMeasure (haarMeasure K)
  exact isHaarMeasure_haarMeasure K

/-- Normalized finite-unitary Haar is right invariant. -/
noncomputable instance finiteUnitaryHaarIsMulRightInvariant
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    IsMulRightInvariant (finiteUnitaryHaar ι) where
  map_mul_right_eq_self := map_finiteUnitaryHaar_mul_right

/-- Every nonempty open subset of a finite unitary group has positive
normalized Haar mass. -/
theorem finiteUnitaryHaar_pos_of_isOpen_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : Set (Matrix.unitaryGroup ι ℂ)}
    (hs : IsOpen s) (hne : s.Nonempty) :
    0 < finiteUnitaryHaar ι s :=
  hs.measure_pos (finiteUnitaryHaar ι) hne

end

end GaloisForLFunctions.HTGeometry
