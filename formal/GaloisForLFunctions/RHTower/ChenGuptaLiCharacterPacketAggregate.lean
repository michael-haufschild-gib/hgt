/-
# Chen--Gupta--Li whole-packet off-diagonal kernel budget

Chen--Gupta--Li Lemma 9.1 bounds a finite character packet by summing its
same-character off-diagonal rows.  This module carries out that finite
summation exactly for the globally separated packet model.  Together with the
interval identity, it is the complete finite off-diagonal bookkeeping layer;
only the source's weaker fibrewise separation remains to be installed.

No RH, GRH, smoothness, large-value, or zero-density premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketOffDiagonal

noncomputable section

namespace RHTower

/-- Total same-character off-diagonal interval-kernel mass of a finite CGL
packet. -/
def cglGloballySeparatedPacketSameCharacterKernelTotal {q R : ℕ}
    (P : CGLGloballySeparatedPacket q R) (A B : ℝ) : ℝ :=
  ∑ r : Fin R, cglGloballySeparatedPacketSameCharacterKernelRow P A B r

/-- Summing the certified row estimate gives the whole-packet CGL
off-diagonal budget.  The `R` factor is the literal number of packet rows;
the harmonic sum is the exact logarithmic loss supplied by separation. -/
theorem cglGloballySeparatedPacket_sameCharacterKernelTotal_le {q R : ℕ}
    (P : CGLGloballySeparatedPacket q R) (A B : ℝ) :
    cglGloballySeparatedPacketSameCharacterKernelTotal P A B ≤
      (R : ℝ) * ((4 / P.spacing) * ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1)) := by
  let C : ℝ := (4 / P.spacing) * ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1)
  calc
    cglGloballySeparatedPacketSameCharacterKernelTotal P A B ≤ ∑ _ : Fin R, C := by
      unfold cglGloballySeparatedPacketSameCharacterKernelTotal
      apply Finset.sum_le_sum
      intro r hr
      exact le_trans (cglGloballySeparatedPacket_sameCharacterKernelRow_le P A B r)
        (cglGloballySeparatedPacket_reciprocalRow_le P r)
    _ = (R : ℝ) * C := by simp [C]
    _ = _ := rfl

end RHTower
