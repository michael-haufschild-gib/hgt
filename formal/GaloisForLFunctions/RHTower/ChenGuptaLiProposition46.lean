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

/-- CGL Lemma 4.5 after subtracting the exact all-equal diagonal from the
centered cubic trace in Lemma 4.2.  The zero-frequency remainder stays explicit
at this stage. -/
theorem cglProposition46_centeredCubicTrace_eq_zero_add_nonzero
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) :
    ((cglCharacterDyadicWeightedGram N.value (cglLemma45FibreModulus q).value (R + 1)
      (cglSmoothBumpDyadicWeight S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump N)
      (cglLemma45FibreRows P)) ^ 3).trace.re -
      (cglCharacterDyadicWeightedGram N.value (cglLemma45FibreModulus q).value (R + 1)
        (cglSmoothBumpDyadicWeight S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump N)
        (cglLemma45FibreRows P)).trace.re ^ 3 / (R + 1 : ℝ) ^ 2 =
      (cglLemma45OffDiagonalFrequencyTerm S.cutoff.toCGLRealSmoothBump N
        (cglLemma45FibreModulus q) (R + 1) (cglLemma45FibreRows P) 0 +
        ∑' m : {m : (ℤ × ℤ) × ℤ // m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))},
          cglLemma45OffDiagonalNonzeroFrequencyTerm S.cutoff.toCGLRealSmoothBump N
            (cglLemma45FibreModulus q) (R + 1) (cglLemma45FibreRows P) m).re := by
  have hsource :=
    (cglLemma45_literalEpsilon_expansion_and_zeroBound S.source
      S.cutoff.toCGLRealSmoothBump).1
  have hsourceQ :
      cglCharacterDyadicWeightedGramCubicTrace N.value (cglLemma45FibreModulus q).value (R + 1)
        (cglSmoothBumpDyadicWeight S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump N)
        (cglLemma45FibreRows P) =
        ((R + 1 : ℕ) : ℂ) * cglLemma45DiagonalPoissonMass
          S.cutoff.toCGLRealSmoothBump N (cglLemma45FibreModulus q) ^ 3 +
          cglLemma45OffDiagonalFrequencyTerm S.cutoff.toCGLRealSmoothBump N
            (cglLemma45FibreModulus q) (R + 1) (cglLemma45FibreRows P) 0 +
          ∑' m : {m : (ℤ × ℤ) × ℤ // m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))},
            cglLemma45OffDiagonalNonzeroFrequencyTerm S.cutoff.toCGLRealSmoothBump N
              (cglLemma45FibreModulus q) (R + 1) (cglLemma45FibreRows P) m := by
    simpa only [cglLemma45FibreModulus] using hsource
  have hsplit := cglLemma45_cubicTrace_eq_diagonalPoisson_add_offDiagonal
    S.cutoff.toCGLRealSmoothBump N (cglLemma45FibreModulus q) (R + 1)
    (cglLemma45FibreRows P)
  have hoff :
      cglCharacterDyadicWeightedGramCubicOffDiagonal N.value (cglLemma45FibreModulus q).value (R + 1)
        (cglSmoothBumpDyadicWeight S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump N)
        (cglLemma45FibreRows P) =
        cglLemma45OffDiagonalFrequencyTerm S.cutoff.toCGLRealSmoothBump N
          (cglLemma45FibreModulus q) (R + 1) (cglLemma45FibreRows P) 0 +
          ∑' m : {m : (ℤ × ℤ) × ℤ // m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))},
            cglLemma45OffDiagonalNonzeroFrequencyTerm S.cutoff.toCGLRealSmoothBump N
              (cglLemma45FibreModulus q) (R + 1) (cglLemma45FibreRows P) m := by
    calc
      cglCharacterDyadicWeightedGramCubicOffDiagonal N.value (cglLemma45FibreModulus q).value (R + 1)
          (cglSmoothBumpDyadicWeight S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump N)
          (cglLemma45FibreRows P) =
          cglCharacterDyadicWeightedGramCubicTrace N.value (cglLemma45FibreModulus q).value (R + 1)
            (cglSmoothBumpDyadicWeight S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump N)
            (cglLemma45FibreRows P) -
              ((R + 1 : ℕ) : ℂ) * cglLemma45DiagonalPoissonMass
                S.cutoff.toCGLRealSmoothBump N (cglLemma45FibreModulus q) ^ 3 := by
          rw [hsplit]
          ring
      _ = _ := by
          rw [hsourceQ]
          ring
  calc
    ((cglCharacterDyadicWeightedGram N.value (cglLemma45FibreModulus q).value (R + 1)
      (cglSmoothBumpDyadicWeight S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump N)
      (cglLemma45FibreRows P)) ^ 3).trace.re -
        (cglCharacterDyadicWeightedGram N.value (cglLemma45FibreModulus q).value (R + 1)
          (cglSmoothBumpDyadicWeight S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump N)
          (cglLemma45FibreRows P)).trace.re ^ 3 / (R + 1 : ℝ) ^ 2 =
        (cglCharacterDyadicWeightedGramCubicOffDiagonal N.value (cglLemma45FibreModulus q).value (R + 1)
          (cglSmoothBumpDyadicWeight S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump N)
          (cglLemma45FibreRows P)).re :=
      cglCharacterDyadicWeighted_centeredCubicTrace_re_eq_offDiagonal_re
        N.value (cglLemma45FibreModulus q).value R
          (cglSmoothBumpDyadicWeight S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump N)
          (cglLemma45FibreRows P)
    _ = _ := congrArg Complex.re hoff

/-- Matrix form of the exact centered-cubic identity needed in Proposition 4.6. -/
theorem cglProposition46_matrix_centeredCubicTrace_eq_zero_add_nonzero
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) :
    (((cglLemma42Matrix S.toLemma42 * (cglLemma42Matrix S.toLemma42)ᴴ) ^ 3).trace.re -
      ((cglLemma42Matrix S.toLemma42 * (cglLemma42Matrix S.toLemma42)ᴴ).trace.re ^ 3) /
        (R + 1 : ℝ) ^ 2) =
      (cglLemma45OffDiagonalFrequencyTerm S.cutoff.toCGLRealSmoothBump N
        (cglLemma45FibreModulus q) (R + 1) (cglLemma45FibreRows P) 0 +
        ∑' m : {m : (ℤ × ℤ) × ℤ // m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))},
          cglLemma45OffDiagonalNonzeroFrequencyTerm S.cutoff.toCGLRealSmoothBump N
            (cglLemma45FibreModulus q) (R + 1) (cglLemma45FibreRows P) m).re := by
  change
    (((cglCharacterDyadicWeightedEvaluationMatrix N.value (cglLemma45FibreModulus q).value
      (R + 1) (cglSmoothBumpDyadicWeight S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump N)
      (cglLemma45FibreRows P) *
      (cglCharacterDyadicWeightedEvaluationMatrix N.value (cglLemma45FibreModulus q).value
        (R + 1) (cglSmoothBumpDyadicWeight S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump N)
        (cglLemma45FibreRows P))ᴴ) ^ 3).trace.re -
      ((cglCharacterDyadicWeightedEvaluationMatrix N.value (cglLemma45FibreModulus q).value
        (R + 1) (cglSmoothBumpDyadicWeight S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump N)
        (cglLemma45FibreRows P) *
        (cglCharacterDyadicWeightedEvaluationMatrix N.value (cglLemma45FibreModulus q).value
          (R + 1) (cglSmoothBumpDyadicWeight S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump N)
          (cglLemma45FibreRows P))ᴴ).trace.re ^ 3) /
        (R + 1 : ℝ) ^ 2) = _
  rw [cglCharacterDyadicWeightedEvaluationMatrix_self_mul_conjTranspose_eq_gram]
  exact cglProposition46_centeredCubicTrace_eq_zero_add_nonzero S

/-- The nonnegative spectral cubic deviation occurring in CGL Lemma 4.2. -/
noncomputable def cglProposition46CenteredCubic
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) : ℝ :=
  ((cglLemma42Matrix S.toLemma42 * (cglLemma42Matrix S.toLemma42)ᴴ) ^ 3).trace.re -
    ((cglLemma42Matrix S.toLemma42 * (cglLemma42Matrix S.toLemma42)ᴴ).trace.re ^ 3) /
      (R + 1 : ℝ) ^ 2

/-- The real Hilbert--Schmidt trace in CGL Lemma 4.2. -/
noncomputable def cglProposition46TraceMass
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) : ℝ :=
  (cglLemma42Matrix S.toLemma42 * (cglLemma42Matrix S.toLemma42)ᴴ).trace.re

/-- The literal nonzero-frequency total `Σ_{m≠0} I_m` from CGL Lemma 4.5. -/
noncomputable def cglProposition46NonzeroFrequencySum
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) : ℂ :=
  ∑' m : {m : (ℤ × ℤ) × ℤ // m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))},
    cglLemma45OffDiagonalNonzeroFrequencyTerm S.cutoff.toCGLRealSmoothBump N
      (cglLemma45FibreModulus q) (R + 1) (cglLemma45FibreRows P) m

/-- The literal off-diagonal zero-frequency term `Z′` from CGL Lemma 4.5. -/
noncomputable def cglProposition46ZeroFrequencyTerm
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) : ℂ :=
  cglLemma45OffDiagonalFrequencyTerm S.cutoff.toCGLRealSmoothBump N
    (cglLemma45FibreModulus q) (R + 1) (cglLemma45FibreRows P) 0

/-- The explicit `X^-100` bound for `Z′` supplied by CGL Lemma 4.5. -/
noncomputable def cglProposition46ZeroFrequencyBudget
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) : ℝ :=
  (cglLogFourierAmplitudeAllOrderBudget S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump
    (S.source.epsilonDenominator * 115) *
    cglLogFourierAmplitudeAllOrderBudget S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump 0 *
    cglLogFourierAmplitudeAllOrderBudget S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump 0) /
      S.source.base ^ 100

/-- The centered cubic deviation is nonnegative by the finite positive
spectrum of `M M*`. -/
theorem cglProposition46_centeredCubic_nonneg
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) :
    0 ≤ cglProposition46CenteredCubic S := by
  unfold cglProposition46CenteredCubic
  have h := cglCenteredCubicDeviation_nonneg R
    (CGLGramSpectrum R N.value (cglLemma42Matrix S.toLemma42))
  rw [cglGramCenteredCubicDeviation_eq_trace] at h
  exact h

/-- The Hilbert--Schmidt trace is nonnegative. -/
theorem cglProposition46_traceMass_nonneg
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) :
    0 ≤ cglProposition46TraceMass S := by
  unfold cglProposition46TraceMass
  rw [← sum_cglGramSpectrum_eq_trace]
  exact Finset.sum_nonneg fun _ _ => NNReal.zero_le_coe

/-- The source's unit cutoff gives `Re tr(MM*) ≤ |W|N`. -/
theorem cglProposition46_traceMass_le_card_mul_length
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) :
    cglProposition46TraceMass S ≤ ((R + 1 : ℕ) : ℝ) * N.value := by
  unfold cglProposition46TraceMass
  change
    ((cglCharacterDyadicWeightedEvaluationMatrix N.value (cglLemma45FibreModulus q).value
      (R + 1) (cglSmoothBumpDyadicWeight S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump N)
      (cglLemma45FibreRows P) *
      (cglCharacterDyadicWeightedEvaluationMatrix N.value (cglLemma45FibreModulus q).value
        (R + 1) (cglSmoothBumpDyadicWeight S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump N)
        (cglLemma45FibreRows P))ᴴ).trace).re ≤ _
  exact cglUnitRealSmoothBump_trace_self_mul_conjTranspose_re_le_card_mul_length
    S.cutoff N (cglLemma45FibreModulus q) (R + 1) (cglLemma45FibreRows P)

/-- Exact centered-trace form of Lemma 4.5 on the Proposition 4.6 matrix. -/
theorem cglProposition46_centeredCubic_eq_zero_add_nonzero
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) :
    cglProposition46CenteredCubic S =
      (cglProposition46ZeroFrequencyTerm S +
        cglProposition46NonzeroFrequencySum S).re := by
  exact cglProposition46_matrix_centeredCubicTrace_eq_zero_add_nonzero S

/-- The literal zero-frequency term obeys the closed Lemma 4.5 budget. -/
theorem cglProposition46_zeroFrequency_norm_le_budget
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) :
    ‖cglProposition46ZeroFrequencyTerm S‖ ≤ cglProposition46ZeroFrequencyBudget S := by
  exact (cglLemma45_literalEpsilon_expansion_and_zeroBound S.source
    S.cutoff.toCGLRealSmoothBump).2

/-- The centered cubic deviation is at most the explicit zero-frequency
budget plus the real part of the nonzero-frequency total. -/
theorem cglProposition46_centeredCubic_le_budget_add_nonzeroRe
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) :
    cglProposition46CenteredCubic S ≤
      cglProposition46ZeroFrequencyBudget S +
        (cglProposition46NonzeroFrequencySum S).re := by
  rw [cglProposition46_centeredCubic_eq_zero_add_nonzero]
  have hzero := cglProposition46_zeroFrequency_norm_le_budget S
  calc
    (cglProposition46ZeroFrequencyTerm S +
      cglProposition46NonzeroFrequencySum S).re =
        (cglProposition46ZeroFrequencyTerm S).re +
          (cglProposition46NonzeroFrequencySum S).re := by rw [Complex.add_re]
    _ ≤ cglProposition46ZeroFrequencyBudget S +
          (cglProposition46NonzeroFrequencySum S).re := by
      gcongr
      exact (Complex.re_le_norm _).trans hzero

/-- Closed combination of CGL Lemmas 4.1 and 4.2 with the normalized
Hilbert--Schmidt trace bound, before substituting the Lemma 4.5 error. -/
theorem cglProposition46_preAbsorption_bound
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) :
    (R + 1 : ℝ) ≤
      288 * (N.value : ℝ) ^ (1 - 2 * S.sigma) *
        cglProposition46CenteredCubic S ^ (1 / 3 : ℝ) +
      288 * (N.value : ℝ) ^ (2 - 2 * S.sigma) := by
  let M := cglLemma42Matrix S.toLemma42
  let C := cglProposition46CenteredCubic S
  let H := cglProposition46TraceMass S
  let A : ℝ := (N.value : ℝ) ^ (1 - 2 * S.sigma)
  have hN : 0 < (N.value : ℝ) := by exact_mod_cast N.positive
  have hr : 0 < (R + 1 : ℝ) := by positivity
  have hA : 0 ≤ A := Real.rpow_nonneg hN.le _
  have hC : 0 ≤ C := cglProposition46_centeredCubic_nonneg S
  have hH : 0 ≤ H := cglProposition46_traceMass_nonneg S
  have hHle : H ≤ ((R + 1 : ℕ) : ℝ) * N.value :=
    cglProposition46_traceMass_le_card_mul_length S
  have h41 : (R + 1 : ℝ) ≤ 36 * A * ‖M‖ ^ 2 := by
    simpa only [M, A, Nat.cast_add, Nat.cast_one] using
      cglProposition46_lemma41_matrix_bound S
  have h42 : ‖M‖ ≤
      2 * C ^ (1 / 6 : ℝ) + 2 * √(H / (R + 1 : ℝ)) := by
    simpa [M, C, H, cglProposition46CenteredCubic, cglProposition46TraceMass] using
      cglProposition46_lemma42_spectral_bound S
  have hHr : 0 ≤ H / (R + 1 : ℝ) := div_nonneg hH hr.le
  have hC16sq : (C ^ (1 / 6 : ℝ)) ^ 2 = C ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hC]
    norm_num
  have hHsq : (√(H / (R + 1 : ℝ))) ^ 2 = H / (R + 1 : ℝ) :=
    Real.sq_sqrt hHr
  have hMsq : ‖M‖ ^ 2 ≤
      8 * C ^ (1 / 3 : ℝ) + 8 * (H / (R + 1 : ℝ)) := by
    have hsq := pow_le_pow_left₀ (norm_nonneg M) h42 2
    calc
      ‖M‖ ^ 2 ≤ (2 * C ^ (1 / 6 : ℝ) + 2 * √(H / (R + 1 : ℝ))) ^ 2 := hsq
      _ ≤ 2 * (2 * C ^ (1 / 6 : ℝ)) ^ 2 +
          2 * (2 * √(H / (R + 1 : ℝ))) ^ 2 := by
        nlinarith [sq_nonneg (2 * C ^ (1 / 6 : ℝ) - 2 * √(H / (R + 1 : ℝ)))]
      _ = 8 * (C ^ (1 / 6 : ℝ)) ^ 2 +
          8 * (√(H / (R + 1 : ℝ))) ^ 2 := by ring
      _ = 8 * C ^ (1 / 3 : ℝ) + 8 * (H / (R + 1 : ℝ)) := by
        rw [hC16sq, hHsq]
  have hdiv : H / (R + 1 : ℝ) ≤ N.value := by
    apply (div_le_iff₀ hr).mpr
    calc
      H ≤ ((R + 1 : ℕ) : ℝ) * N.value := hHle
      _ = N.value * (R + 1 : ℝ) := by
        push_cast
        ring
  have hpower : A * N.value = (N.value : ℝ) ^ (2 - 2 * S.sigma) := by
    calc
      A * N.value = (N.value : ℝ) ^ (1 - 2 * S.sigma) * (N.value : ℝ) ^ 1 := by
        dsimp [A]
        rw [Real.rpow_one]
      _ = (N.value : ℝ) ^ ((1 - 2 * S.sigma) + 1) :=
        (Real.rpow_add hN _ _).symm
      _ = (N.value : ℝ) ^ (2 - 2 * S.sigma) := by
        congr 1
        ring
  calc
    (R + 1 : ℝ) ≤ 36 * A *
        (8 * C ^ (1 / 3 : ℝ) + 8 * (H / (R + 1 : ℝ))) :=
      h41.trans (mul_le_mul_of_nonneg_left hMsq (by positivity))
    _ = 288 * A * C ^ (1 / 3 : ℝ) + 288 * A * (H / (R + 1 : ℝ)) := by ring
    _ ≤ 288 * A * C ^ (1 / 3 : ℝ) + 288 * A * N.value := by
      gcongr
    _ = 288 * A * C ^ (1 / 3 : ℝ) +
        288 * (A * N.value) := by ring
    _ = 288 * A * C ^ (1 / 3 : ℝ) +
        288 * (N.value : ℝ) ^ (2 - 2 * S.sigma) := by rw [hpower]
    _ = _ := by rfl

/-- Explicit CGL Proposition 4.6 estimate.  The paper's `O_ε((qT)^-100)`
term is retained as the fully constructed Lemma 4.5 budget. -/
theorem cglProposition46_explicitZeroMode_bound
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) :
    (R + 1 : ℝ) ≤
      288 * (N.value : ℝ) ^ (1 - 2 * S.sigma) *
        (cglProposition46ZeroFrequencyBudget S +
          (cglProposition46NonzeroFrequencySum S).re) ^ (1 / 3 : ℝ) +
      288 * (N.value : ℝ) ^ (2 - 2 * S.sigma) := by
  have hC := cglProposition46_centeredCubic_nonneg S
  have hCbound := cglProposition46_centeredCubic_le_budget_add_nonzeroRe S
  have hroot := Real.rpow_le_rpow hC hCbound (by norm_num : (0 : ℝ) ≤ 1 / 3)
  calc
    (R + 1 : ℝ) ≤
        288 * (N.value : ℝ) ^ (1 - 2 * S.sigma) *
          cglProposition46CenteredCubic S ^ (1 / 3 : ℝ) +
        288 * (N.value : ℝ) ^ (2 - 2 * S.sigma) :=
      cglProposition46_preAbsorption_bound S
    _ ≤ 288 * (N.value : ℝ) ^ (1 - 2 * S.sigma) *
          (cglProposition46ZeroFrequencyBudget S +
            (cglProposition46NonzeroFrequencySum S).re) ^ (1 / 3 : ℝ) +
        288 * (N.value : ℝ) ^ (2 - 2 * S.sigma) := by
      gcongr

/-- The cutoff- and `ε`-dependent numerator of the explicit `Z′` budget. -/
noncomputable def cglProposition46ZeroFrequencyNumerator
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) : ℝ :=
  cglLogFourierAmplitudeAllOrderBudget S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump
    (S.source.epsilonDenominator * 115) *
    cglLogFourierAmplitudeAllOrderBudget S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump 0 *
    cglLogFourierAmplitudeAllOrderBudget S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump 0

theorem cglProposition46_zeroFrequencyNumerator_nonneg
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) :
    0 ≤ cglProposition46ZeroFrequencyNumerator S := by
  unfold cglProposition46ZeroFrequencyNumerator
  exact mul_nonneg
    (mul_nonneg
      (cglLogFourierAmplitudeAllOrderBudget_nonneg
        S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump _)
      (cglLogFourierAmplitudeAllOrderBudget_nonneg
        S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump 0))
    (cglLogFourierAmplitudeAllOrderBudget_nonneg
      S.cutoff.toCGLRealSmoothBump.toCGLSmoothBump 0)

/-- The explicit Lemma 4.5 budget is bounded by its fixed-cutoff/`ε`
numerator because the certified source scale satisfies `X≥5`. -/
theorem cglProposition46_zeroFrequencyBudget_le_numerator
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) :
    cglProposition46ZeroFrequencyBudget S ≤ cglProposition46ZeroFrequencyNumerator S := by
  unfold cglProposition46ZeroFrequencyBudget cglProposition46ZeroFrequencyNumerator
  apply div_le_self
  · exact cglProposition46_zeroFrequencyNumerator_nonneg S
  · exact one_le_pow₀ (by linarith [S.source.base_five])

/-- **Chen--Gupta--Li Proposition 4.6, closed real form.** The source's
untyped `Σ_{m≠0} I_m` is represented by the positivity-safe real quantity
`max(0, Re Σ I_m)`.  The displayed coefficient makes the paper's
cutoff- and `ε`-dependent implicit constant explicit. -/
theorem cglProposition46_realAsymptotic_bound
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) :
    (R + 1 : ℝ) ≤
      288 * (cglProposition46ZeroFrequencyNumerator S ^ (1 / 3 : ℝ) + 1) *
        (N.value : ℝ) ^ (2 - 2 * S.sigma) +
      288 * (N.value : ℝ) ^ (1 - 2 * S.sigma) *
        (max 0 (cglProposition46NonzeroFrequencySum S).re) ^ (1 / 3 : ℝ) := by
  let A : ℝ := (N.value : ℝ) ^ (1 - 2 * S.sigma)
  let B : ℝ := cglProposition46ZeroFrequencyBudget S
  let K : ℝ := cglProposition46ZeroFrequencyNumerator S
  let V : ℝ := max 0 (cglProposition46NonzeroFrequencySum S).re
  have hN : 0 < (N.value : ℝ) := by exact_mod_cast N.positive
  have hN1 : (1 : ℝ) ≤ N.value := by
    exact_mod_cast Nat.succ_le_iff.mpr N.positive
  have hA : 0 ≤ A := Real.rpow_nonneg hN.le _
  have hK : 0 ≤ K := cglProposition46_zeroFrequencyNumerator_nonneg S
  have hB : 0 ≤ B := by
    unfold B cglProposition46ZeroFrequencyBudget
    exact div_nonneg hK (pow_nonneg (by linarith [S.source.base_five]) _)
  have hV : 0 ≤ V := by
    dsimp [V]
    exact le_max_left (0 : ℝ) _
  have hBLeK : B ≤ K := by
    simpa only [B, K] using cglProposition46_zeroFrequencyBudget_le_numerator S
  have hC : 0 ≤ cglProposition46CenteredCubic S := cglProposition46_centeredCubic_nonneg S
  have hCLe : cglProposition46CenteredCubic S ≤ B + V := by
    calc
      cglProposition46CenteredCubic S ≤
          B + (cglProposition46NonzeroFrequencySum S).re := by
        simpa only [B] using cglProposition46_centeredCubic_le_budget_add_nonzeroRe S
      _ ≤ B + V := by
        dsimp [V]
        gcongr
        exact le_max_right (0 : ℝ) _
  have hCroot : cglProposition46CenteredCubic S ^ (1 / 3 : ℝ) ≤
      B ^ (1 / 3 : ℝ) + V ^ (1 / 3 : ℝ) := by
    exact (Real.rpow_le_rpow hC hCLe (by norm_num : (0 : ℝ) ≤ 1 / 3)).trans
      (Real.rpow_add_le_add_rpow hB hV (by norm_num : (0 : ℝ) ≤ 1 / 3)
        (by norm_num : (1 / 3 : ℝ) ≤ 1))
  have hBroot : B ^ (1 / 3 : ℝ) ≤ K ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow hB hBLeK (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hKroot : 0 ≤ K ^ (1 / 3 : ℝ) := Real.rpow_nonneg hK _
  have hpower : A * N.value = (N.value : ℝ) ^ (2 - 2 * S.sigma) := by
    calc
      A * N.value = (N.value : ℝ) ^ (1 - 2 * S.sigma) * (N.value : ℝ) ^ 1 := by
        dsimp [A]
        rw [Real.rpow_one]
      _ = (N.value : ℝ) ^ ((1 - 2 * S.sigma) + 1) :=
        (Real.rpow_add hN _ _).symm
      _ = (N.value : ℝ) ^ (2 - 2 * S.sigma) := by
        congr 1
        ring
  have herror : 288 * A * B ^ (1 / 3 : ℝ) ≤
      288 * K ^ (1 / 3 : ℝ) * (N.value : ℝ) ^ (2 - 2 * S.sigma) := by
    have hAK : A * B ^ (1 / 3 : ℝ) ≤ A * K ^ (1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hBroot hA
    have hAK0 : 0 ≤ A * K ^ (1 / 3 : ℝ) := mul_nonneg hA hKroot
    have hAKN : A * K ^ (1 / 3 : ℝ) ≤ A * K ^ (1 / 3 : ℝ) * N.value := by
      calc
        A * K ^ (1 / 3 : ℝ) = A * K ^ (1 / 3 : ℝ) * 1 := by ring
        _ ≤ A * K ^ (1 / 3 : ℝ) * N.value :=
          mul_le_mul_of_nonneg_left hN1 hAK0
    calc
      288 * A * B ^ (1 / 3 : ℝ) = 288 * (A * B ^ (1 / 3 : ℝ)) := by ring
      _ ≤ 288 * (A * K ^ (1 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hAK (by norm_num)
      _ ≤ 288 * (A * K ^ (1 / 3 : ℝ) * N.value) :=
        mul_le_mul_of_nonneg_left hAKN (by norm_num)
      _ = 288 * K ^ (1 / 3 : ℝ) * (N.value : ℝ) ^ (2 - 2 * S.sigma) := by
        calc
          288 * (A * K ^ (1 / 3 : ℝ) * N.value) =
              288 * K ^ (1 / 3 : ℝ) * (A * N.value) := by ring
          _ = _ := by rw [hpower]
  calc
    (R + 1 : ℝ) ≤
        288 * A * cglProposition46CenteredCubic S ^ (1 / 3 : ℝ) +
        288 * (N.value : ℝ) ^ (2 - 2 * S.sigma) := by
      simpa only [A] using cglProposition46_preAbsorption_bound S
    _ ≤ 288 * A * (B ^ (1 / 3 : ℝ) + V ^ (1 / 3 : ℝ)) +
        288 * (N.value : ℝ) ^ (2 - 2 * S.sigma) := by
      gcongr
    _ = 288 * A * B ^ (1 / 3 : ℝ) +
        288 * A * V ^ (1 / 3 : ℝ) +
        288 * (N.value : ℝ) ^ (2 - 2 * S.sigma) := by ring
    _ ≤ 288 * K ^ (1 / 3 : ℝ) * (N.value : ℝ) ^ (2 - 2 * S.sigma) +
        288 * A * V ^ (1 / 3 : ℝ) +
        288 * (N.value : ℝ) ^ (2 - 2 * S.sigma) := by
      gcongr
    _ = 288 * (K ^ (1 / 3 : ℝ) + 1) *
          (N.value : ℝ) ^ (2 - 2 * S.sigma) +
        288 * A * V ^ (1 / 3 : ℝ) := by ring
    _ = _ := by rfl

end RHTower
