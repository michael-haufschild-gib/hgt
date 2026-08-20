import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra
import GaloisForLFunctions.HTGeometry.PauliCharacterFirstDefectSelector

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Every nonzero finite Pauli character selects a unit-momentum local supercharge pair. -/
def firstDefectPauliD1N2
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (P : NonzeroPauliCharacter σ) :
    SuperPoincare.D1N2 (Matrix Bool Bool ℂ) where
  supercharge0 := finiteQubitPauli (pauliAxisPrev (firstActivePauliAxis P))
  supercharge1 := finiteQubitPauli (firstActivePauliAxis P)
  momentum := 1
  supercharge0_sq := finiteQubitPauli_mul_self _
  supercharge1_sq := finiteQubitPauli_mul_self _
  mixed_anticommutator := by
    rw [finiteQubitPauli_firstDefect_anticommutes_source P]
    exact neg_add_cancel _

end GaloisForLFunctions.HTGeometry
