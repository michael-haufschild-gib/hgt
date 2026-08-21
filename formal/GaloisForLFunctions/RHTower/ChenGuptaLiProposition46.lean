/-
# Chen--Gupta--Li Proposition 4.6: certified matrix packet

This module combines the closed source interfaces for Lemmas 4.1 and 4.2 on
the one literal CGL packet.  The remaining source step is to replace the
centered cubic trace by the Lemma 4.5 frequency expansion and then absorb the
certified zero-frequency remainder.  All source conditions are fields of the
packet, so exported theorems have no caller-supplied mathematical premise.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45
import GaloisForLFunctions.RHTower.ChenGuptaLiUnitRealSmoothBump
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma42

noncomputable section

namespace RHTower

open Matrix
open scoped Matrix.Norms.L2Operator

/-- Certified finite data from CGL Proposition 4.6 before applying the
off-diagonal-frequency estimate.  The literal source large-value condition is
internal to the packet. -/
structure CGLProposition46Packet {q R : ℕ}
    (P : CGLFibreSeparatedPacket q (R + 1)) (N : CGLPositiveLength) where
  source : CGLLemma45LiteralEpsilonSourcePacket P N
  cutoff : CGLUnitRealSmoothBump
  sigma : ℝ
  coefficients : CGLCharacterDyadicBoundedCoefficients N.value
  large : ∀ r,
    ((N.value : ℝ) ^ sigma / 6) ≤
      ‖cglCharacterDyadicWeightedPolynomial N.value (q + 1)
        (cglSmoothBumpDyadicWeight cutoff.toCGLRealSmoothBump.toCGLSmoothBump N)
        (cglLemma45FibreRows P r) coefficients.value‖

/-- The Proposition 4.6 packet viewed as the exact source packet of Lemma 4.1. -/
def CGLProposition46Packet.toLemma41
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) : CGLLemma41Packet where
  length := N
  modulus := cglLemma45FibreModulus q
  cutoff := S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump
  sigma := S.sigma
  rowCount := R + 1
  rows := cglLemma45FibreRows P
  coefficients := S.coefficients
  large := by
    intro r
    change (N.value : ℝ) ^ S.sigma / 6 ≤
      ‖cglCharacterDyadicWeightedPolynomial N.value (q + 1)
        (cglSmoothBumpDyadicWeight S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump N)
        (cglLemma45FibreRows P r) S.coefficients.value‖
    exact S.large r

/-- The Proposition 4.6 packet viewed as the exact nonempty matrix packet of
Lemma 4.2. -/
def CGLProposition46Packet.toLemma42
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) : CGLLemma42Packet where
  length := N
  modulus := cglLemma45FibreModulus q
  cutoff := S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump
  rowTail := R
  rows := cglLemma45FibreRows P

/-- CGL Lemma 4.1 on the literal Proposition 4.6 matrix. -/
theorem cglProposition46_lemma41_matrix_bound
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) :
    ((R + 1 : ℕ) : ℝ) ≤ 36 * (N.value : ℝ) ^ (1 - 2 * S.sigma) *
      ‖cglLemma42Matrix S.toLemma42‖ ^ 2 := by
  have hmatrix : cglLemma42Matrix S.toLemma42 =
      cglCharacterDyadicWeightedEvaluationMatrix N.value (cglLemma45FibreModulus q).value (R + 1)
        (cglLemma41Weight S.toLemma41) (cglLemma45FibreRows P) := by
    ext r j
    rfl
  rw [hmatrix]
  change (S.toLemma41.rowCount : ℝ) ≤ 36 * (S.toLemma41.length.value : ℝ) ^
      (1 - 2 * S.toLemma41.sigma) *
      ‖cglCharacterDyadicWeightedEvaluationMatrix S.toLemma41.length.value
        S.toLemma41.modulus.value S.toLemma41.rowCount (cglLemma41Weight S.toLemma41)
        S.toLemma41.rows‖ ^ 2
  exact cglLemma41_source_matrix_bound S.toLemma41

/-- CGL Lemma 4.2 on the literal Proposition 4.6 matrix. -/
theorem cglProposition46_lemma42_spectral_bound
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) :
    ‖cglLemma42Matrix S.toLemma42‖ ≤
      2 * (((cglLemma42Matrix S.toLemma42 * (cglLemma42Matrix S.toLemma42)ᴴ) ^ 3).trace.re -
        ((cglLemma42Matrix S.toLemma42 * (cglLemma42Matrix S.toLemma42)ᴴ).trace.re ^ 3) /
          (R + 1 : ℝ) ^ 2) ^ (1 / 6 : ℝ) +
      2 * √((cglLemma42Matrix S.toLemma42 * (cglLemma42Matrix S.toLemma42)ᴴ).trace.re /
        (R + 1 : ℝ)) :=
  cglLemma42_source_bound S.toLemma42

end RHTower
