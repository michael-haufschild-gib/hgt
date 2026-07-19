import GaloisForLFunctions.HTGeometry.CauchyTransformIteratedDeriv
import GaloisForLFunctions.HTGeometry.BoundaryCarrierTranslationFreeness

/-!
# The packet value is a factorial multiple of a kernel moment

The carrier freeness predicate evaluates iterated derivatives of the Cauchy transform at the
row-plus-shift nodes, while the controllability and genericity development works with kernel
moments.  The two differ by the factorial of the jet order.

Recording that identity in the corpus's own packet vocabulary is what lets a pattern relation be
read as a condition on the kernel-moment coordinates, which is the form the genericity theorems
refute.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- The node at which one packet coordinate is evaluated. -/
def packetNode {row ι : Type} [Fintype row] [Fintype ι]
    (orders : ι → ℕ) (packet : InjectiveProjectiveRowPacket row)
    (shift : InjectiveShiftConfiguration ι)
    (p : row × Fin (Fintype.card (Σ i, Fin (orders i)))) : ℂ :=
  packet.1 p.1 + shift.1 ((Fintype.equivFin (Σ i, Fin (orders i))).symm p.2).1

/-- The jet order of one packet coordinate. -/
def packetOrder {row ι : Type} [Fintype row] [Fintype ι]
    (orders : ι → ℕ)
    (p : row × Fin (Fintype.card (Σ i, Fin (orders i)))) : ℕ :=
  ((Fintype.equivFin (Σ i, Fin (orders i))).symm p.2).2

/-- **Factorial dictionary in packet coordinates.**  Off the real axis, the carrier packet value is
the factorial of its jet order times the corresponding kernel moment. -/
theorem probabilityCarrierExpandedPacketValue_eq_factorial_moment
    {row ι : Type} [Fintype row] [Fintype ι]
    (nu : ProbabilityMeasure ℝ) (orders : ι → ℕ)
    (packet : InjectiveProjectiveRowPacket row)
    (shift : InjectiveShiftConfiguration ι)
    (p : row × Fin (Fintype.card (Σ i, Fin (orders i))))
    (hz : (packetNode orders packet shift p).im ≠ 0) :
    probabilityCarrierExpandedPacketValue nu orders packet shift p =
      ((Nat.factorial (packetOrder orders p) : ℕ) : ℂ) *
        cauchyKernelMoment (nu : Measure ℝ) (packetOrder orders p)
          (packetNode orders packet shift p) := by
  rw [probabilityCarrierExpandedPacketValue]
  exact iteratedDeriv_cauchyTransform (nu : Measure ℝ) (packetOrder orders p) hz

end

end GaloisForLFunctions.HTGeometry
