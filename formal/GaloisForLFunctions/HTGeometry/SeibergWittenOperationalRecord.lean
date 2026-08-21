import GaloisForLFunctions.HTGeometry.NoOutsideOperationalSquareCausality
import GaloisForLFunctions.HTGeometry.SeibergWittenAbelianSpinor

/-!
# Finite Seiberg--Witten invariants as positive operational records

The finite Seiberg--Witten outer square is positive semidefinite, so it can be placed directly in
the corpus's two-channel operational-record order. Adjoining any existing color-event Gram square
produces a positive successor and hence increases every pure two-channel witness weight. The base
record itself remains unchanged by the common Seiberg--Witten gauge phase.

This is a finite matrix-order bridge. It does not impose a causal order on continuum
Seiberg--Witten configurations.
-/

noncomputable section

open scoped ComplexOrder MatrixOrder

namespace GaloisForLFunctions.HTGeometry

/-- A finite Seiberg--Witten invariant bundled as a positive two-channel operational record. -/
def seibergWittenPositiveRecord (psi : SeibergWittenSpinor) : TwoChannelPositiveRecord :=
  ⟨seibergWittenInvariant psi, higgsSpinorEventMatrix_posSemidef psi⟩

/-- Record obtained by adjoining a positive color-event Gram increment. -/
def seibergWittenPositiveRecordAfter
    (psi : SeibergWittenSpinor) (Y : ColorEventMatrix) : TwoChannelPositiveRecord :=
  ⟨seibergWittenInvariant psi + colorGramMatrix Y,
    (higgsSpinorEventMatrix_posSemidef psi).add (colorGramMatrix_posSemidef Y)⟩

/-- The positive operational record is invariant under the common Seiberg--Witten gauge phase. -/
theorem seibergWittenPositiveRecord_gaugeInvariant (u : Circle) (psi : SeibergWittenSpinor) :
    seibergWittenPositiveRecord (u • psi) = seibergWittenPositiveRecord psi := by
  apply Subtype.ext
  exact seibergWittenInvariant_gaugeInvariant u psi

/-- Adjoining any color-event Gram square gives a positive-record successor. -/
theorem seibergWittenPositiveRecord_precedes_after
    (psi : SeibergWittenSpinor) (Y : ColorEventMatrix) :
    twoRecordPrecedes (seibergWittenPositiveRecord psi)
      (seibergWittenPositiveRecordAfter psi Y) := by
  change (seibergWittenInvariant psi + colorGramMatrix Y - seibergWittenInvariant psi).PosSemidef
  simpa only [add_sub_cancel_left] using colorGramMatrix_posSemidef Y

/-- Every pure witness weight is nondecreasing after a color-event increment. -/
theorem seibergWittenPositiveRecord_witness_monotone
    (psi : SeibergWittenSpinor) (Y : ColorEventMatrix) (chi : SeibergWittenSpinor) :
    twoRecordWitnessWeight (seibergWittenPositiveRecord psi).1 chi ≤
      twoRecordWitnessWeight (seibergWittenPositiveRecordAfter psi Y).1 chi :=
  (twoRecordPrecedes_iff_forall_witnessWeight_le
    (seibergWittenPositiveRecord psi)
    (seibergWittenPositiveRecordAfter psi Y)).mp
      (seibergWittenPositiveRecord_precedes_after psi Y) chi

/-- The added operational increment is exactly an existing color-event Gram square. -/
theorem seibergWittenPositiveRecord_increment_is_eventSquare
    (psi : SeibergWittenSpinor) (Y : ColorEventMatrix) :
    ∃ Z : ColorEventMatrix,
      (seibergWittenPositiveRecordAfter psi Y).1 =
        (seibergWittenPositiveRecord psi).1 + colorGramMatrix Z :=
  ⟨Y, rfl⟩

end GaloisForLFunctions.HTGeometry
