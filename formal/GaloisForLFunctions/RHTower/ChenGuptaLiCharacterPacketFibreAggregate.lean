/-
# Chen--Gupta--Li fibrewise whole-packet kernel budget

This module sums the source-correct fibrewise CGL Lemma 9.1 row estimate over
the complete finite packet.  Different characters need no ordinate separation:
their cancellation was already isolated by character orthogonality, while each
equal-character fibre supplies its own harmonic off-diagonal row budget.

No RH, GRH, smoothness, large-value, or zero-density premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketFibreSeparation

noncomputable section

namespace RHTower

/-- Total same-character off-diagonal interval-kernel mass for a source-correct
fibrewise separated CGL packet. -/
def cglFibreSeparatedPacketSameCharacterKernelTotal {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (A B : ℝ) : ℝ :=
  ∑ r : Fin R, cglFibreSeparatedPacketSameCharacterKernelRow P A B r

/-- The whole source-correct packet has the finite harmonic off-diagonal
budget obtained by summing its fibrewise rows. -/
theorem cglFibreSeparatedPacket_sameCharacterKernelTotal_le {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (A B : ℝ) :
    cglFibreSeparatedPacketSameCharacterKernelTotal P A B ≤
      (R : ℝ) * ((4 / P.spacing) * ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1)) := by
  let C : ℝ := (4 / P.spacing) * ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1)
  calc
    cglFibreSeparatedPacketSameCharacterKernelTotal P A B ≤ ∑ _ : Fin R, C := by
      unfold cglFibreSeparatedPacketSameCharacterKernelTotal
      apply Finset.sum_le_sum
      intro r hr
      exact cglFibreSeparatedPacket_sameCharacterKernelRow_le P A B r
    _ = (R : ℝ) * C := by simp [C]
    _ = _ := rfl

end RHTower
