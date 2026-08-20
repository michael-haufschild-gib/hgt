import GaloisForLFunctions.QECLean.Stabilizer.Codes.RotatedSurface.StabilizerCode

/-!
# Loop-gauge applications for the rotated surface code

Premise-free order/disorder-line consequences.  Open boundaries turn the toric Wilson and
't Hooft loops into boundary-to-boundary strings; one crossing still gives exact anticommutation.
-/

noncomputable section

namespace Quantum.StabilizerGroup.RotatedSurfaceCodeN.LoopGaugeApplications

/-- Admissible rotated-surface sizes, internalizing oddness and the lower size bound so exported
line-operator laws have no proposition-valued premises. -/
def RotatedGaugeSize := { L : ℕ // Odd L ∧ 3 ≤ L }

instance (L : RotatedGaugeSize) : Fact (Odd L.1) := ⟨L.2.1⟩
instance (L : RotatedGaugeSize) : Fact (3 ≤ L.1) := ⟨L.2.2⟩

/-- Horizontal logical Z string, interpreted as the open-boundary Wilson line. -/
noncomputable def wilsonLine (L : RotatedGaugeSize) :
    NQubitPauliGroupElement (numQubits L.1) :=
  logicalZ L.1

/-- Vertical logical X string, interpreted as the open-boundary 't Hooft line. -/
noncomputable def tHooftLine (L : RotatedGaugeSize) :
    NQubitPauliGroupElement (numQubits L.1) :=
  logicalX L.1

/-- A single transverse intersection gives the order/disorder anticommutation law for every
admissible rotated-surface size. -/
theorem crossing_lines_anticommute (L : RotatedGaugeSize) :
    NQubitPauliGroupElement.Anticommute (tHooftLine L) (wilsonLine L) :=
  logicalX_anticommute_logicalZ L.1

/-- Both lines commute with every local stabilizer, yet they anticommute with each other. -/
theorem line_operator_package (L : RotatedGaugeSize) :
    tHooftLine L ∈ StabilizerGroup.centralizer (stabilizerGroup L.1) ∧
      wilsonLine L ∈ StabilizerGroup.centralizer (stabilizerGroup L.1) ∧
      NQubitPauliGroupElement.Anticommute (tHooftLine L) (wilsonLine L) :=
  ⟨logicalX_mem_centralizer L.1,
    logicalZ_mem_centralizer L.1,
    crossing_lines_anticommute L⟩

end Quantum.StabilizerGroup.RotatedSurfaceCodeN.LoopGaugeApplications
