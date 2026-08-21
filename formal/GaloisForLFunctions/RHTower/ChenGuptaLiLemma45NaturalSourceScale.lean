/-
# Chen--Gupta--Li Lemma 4.5 natural source-scale constructor

Builds the source-power certificate from literal natural scale bounds.  Only
the bounded-height fibre-packing capacity remains to be supplied by the source
packet constructor.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45SourcePower

noncomputable section

namespace RHTower

/-- Natural CGL Lemma 4.5 source data.  `rowCount_le` is the finite packing
certificate to be constructed from the source's height and fibre-spacing data. -/
structure CGLLemma45NaturalSourcePacket {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (N : CGLPositiveLength) where
  scale : ℕ
  modulus_le : q + 1 ≤ scale
  length_le : N.value ≤ scale
  numerator : ℕ
  numerator_pos : 0 < numerator
  denominator : ℕ
  denominator_pos : 0 < denominator
  spacing_power : (scale : ℝ) ^ numerator ≤ P.spacing ^ denominator
  rowCountExponent : ℕ
  rowCount_le : R ≤ scale ^ rowCountExponent

/-- Every natural source packet yields the complete analytic source-power
certificate used by the CGL Lemma 4.5 zero-mode estimate. -/
def CGLLemma45NaturalSourcePacket.toSourceScale
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45NaturalSourcePacket P N) : CGLLemma45SourceScale P N where
  separation :=
    { base := S.scale
      base_one := by
        have h : 1 ≤ S.scale := le_trans (Nat.succ_le_succ (Nat.zero_le q)) S.modulus_le
        exact_mod_cast h
      numerator := S.numerator
      numerator_pos := S.numerator_pos
      denominator := S.denominator
      denominator_pos := S.denominator_pos
      spacing_power := S.spacing_power }
  fourierScale_le := by
    unfold cglAffineFourierScale cglLemma45FibreModulus
    calc
      (N.value : ℝ) / ↑(q + 1) ≤ N.value :=
        div_le_self (by positivity) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le q))
      _ ≤ S.scale := by exact_mod_cast S.length_le
  totient_le := by
    change ((q + 1).totient : ℝ) ≤ S.scale
    exact_mod_cast (le_trans (Nat.totient_le (q + 1)) S.modulus_le)
  rowCountExponent := S.rowCountExponent
  rowCount_le := by
    change (R : ℝ) ≤ (S.scale : ℝ) ^ S.rowCountExponent
    exact_mod_cast S.rowCount_le

/-- Explicit arbitrary-power CGL Lemma 4.5 error bound at a natural source
scale. -/
theorem norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_naturalSourcePower
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45NaturalSourcePacket P N) (w : CGLRealSmoothBump)
    (targetExponent : ℕ) :
    ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) 0‖ ≤
      (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
        (S.denominator * (3 * S.rowCountExponent + 6 + targetExponent)) *
        cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
        cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0) /
          (S.scale : ℝ) ^ targetExponent := by
  exact norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_any_sourcePower S.toSourceScale w
    targetExponent

end RHTower
