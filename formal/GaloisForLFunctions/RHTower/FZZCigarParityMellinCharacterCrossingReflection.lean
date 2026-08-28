import GaloisForLFunctions.RHTower.FZZCigarParityAllScaleKreinCrossing
import GaloisForLFunctions.RHTower.RiemannComplexModularCharacterLaw

/-!
# Mellin-character reflection detected by the FZZ parity crossing

The all-scale FZZ parity source has a canonical Hermitian grade crossing.  This file lands the
corpus's centered Mellin dilation character in its two-coordinate source block.  Dividing the
crossing by character norm removes projective gauge.

Critical-line reflection sends the character to its conjugate inverse.  Consequently the
normalized unit phase is unchanged, while the radial character norm is inverted.  The difference
of reflected FZZ crossings is therefore purely real and has exact sign
`sign(rho.re-1/2)` at every positive physical scale.  Equality is equivalent to the critical line.

This is a source-first transverse detector, valid before divisor specialization.  Applied to all
zeros of the parity FZZ Mellin transform, reflected-crossing matching is exactly RH-strength; the
remaining producer is to derive that matching from interacting FZZ/GFZZ dynamics.
-/

open Complex

namespace RHTower

noncomputable section

/-- Centered Mellin character at the first dyadic dilation step. -/
def fzzCigarParityDyadicMellinCharacter (rho : ℂ) : ℂ :=
  centeredComplexModularCharacter rho (Real.log 2 : ℂ)

theorem fzzCigarParityDyadicMellinCharacter_ne_zero (rho : ℂ) :
    fzzCigarParityDyadicMellinCharacter rho ≠ 0 := by
  rw [fzzCigarParityDyadicMellinCharacter, centeredComplexModularCharacter]
  exact Complex.exp_ne_zero _

theorem norm_fzzCigarParityDyadicMellinCharacter_pos (rho : ℂ) :
    0 < ‖fzzCigarParityDyadicMellinCharacter rho‖ :=
  norm_pos_iff.mpr (fzzCigarParityDyadicMellinCharacter_ne_zero rho)

/-- Two-coordinate multiplicative carrier with dyadic ratio equal to the centered character. -/
def fzzCigarParityMellinCharacterCarrier (rho : ℂ) : ℂ × ℂ :=
  (1, fzzCigarParityDyadicMellinCharacter rho)

/-- Projectively normalized grade crossing of the Mellin-character carrier. -/
def fzzCigarParityMellinCharacterNormalizedCrossing
    (beta : ℝ) (rho : ℂ) : ℂ :=
  fzzCigarParityDilatedTwoScaleGradeCrossing beta
      (fzzCigarParityMellinCharacterCarrier rho) /
    (‖fzzCigarParityDyadicMellinCharacter rho‖ : ℂ)

/-- The normalized crossing splits into unit phase plus positive radial source term. -/
theorem fzzCigarParityMellinCharacterNormalizedCrossing_eq
    (beta : ℝ) (rho : ℂ) :
    fzzCigarParityMellinCharacterNormalizedCrossing beta rho =
      (fzzKreinQAt beta : ℂ) *
          (fzzCigarParityDyadicMellinCharacter rho /
            (‖fzzCigarParityDyadicMellinCharacter rho‖ : ℂ)) +
        (fzzKreinRAt beta : ℂ) *
          (‖fzzCigarParityDyadicMellinCharacter rho‖ : ℂ) := by
  rw [fzzCigarParityMellinCharacterNormalizedCrossing,
    fzzCigarParityDilatedTwoScaleGradeCrossing,
    fzzCigarParityDilatedTwoScaleGrade,
    fzzCigarParityDilatedTwoScaleKreinPairing,
    fzzCigarParityMellinCharacterCarrier]
  simp only [star_one, mul_zero, add_zero, mul_one, zero_add]
  have hn : (‖fzzCigarParityDyadicMellinCharacter rho‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_fzzCigarParityDyadicMellinCharacter_pos rho).ne'
  have hstar :
      star (fzzCigarParityDyadicMellinCharacter rho) *
          fzzCigarParityDyadicMellinCharacter rho =
        ((‖fzzCigarParityDyadicMellinCharacter rho‖ ^ 2 : ℝ) : ℂ) := by
    simpa using Complex.conj_mul' (fzzCigarParityDyadicMellinCharacter rho)
  rw [mul_assoc (fzzKreinRAt beta : ℂ), hstar]
  push_cast
  field_simp

theorem fzzCigarParityDyadicMellinCharacter_reflection (rho : ℂ) :
    fzzCigarParityDyadicMellinCharacter (criticalLineReflectionPoint rho) =
      ((starRingEnd ℂ) (fzzCigarParityDyadicMellinCharacter rho))⁻¹ := by
  rw [fzzCigarParityDyadicMellinCharacter,
    fzzCigarParityDyadicMellinCharacter,
    centeredComplexModularCharacter, centeredComplexModularCharacter]
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  have hlog :
      (starRingEnd ℂ) ((Real.log 2 : ℝ) : ℂ) =
        ((Real.log 2 : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [criticalLineReflectionPoint]
  simp only [map_mul, map_sub, map_one, map_div₀, map_ofNat, hlog]
  ring

theorem norm_fzzCigarParityDyadicMellinCharacter_reflection_mul (rho : ℂ) :
    ‖fzzCigarParityDyadicMellinCharacter (criticalLineReflectionPoint rho)‖ *
      ‖fzzCigarParityDyadicMellinCharacter rho‖ = 1 := by
  exact norm_centeredComplexModularCharacter_reflection_mul rho (Real.log 2)

/-- Functional-equation reflection preserves the normalized dyadic character phase exactly. -/
theorem fzzCigarParityDyadicMellinCharacter_normalizedPhase_reflection
    (rho : ℂ) :
    fzzCigarParityDyadicMellinCharacter (criticalLineReflectionPoint rho) /
        (‖fzzCigarParityDyadicMellinCharacter
          (criticalLineReflectionPoint rho)‖ : ℂ) =
      fzzCigarParityDyadicMellinCharacter rho /
        (‖fzzCigarParityDyadicMellinCharacter rho‖ : ℂ) := by
  let z := fzzCigarParityDyadicMellinCharacter rho
  let zr := fzzCigarParityDyadicMellinCharacter (criticalLineReflectionPoint rho)
  let n := ‖z‖
  have hz : z ≠ 0 := fzzCigarParityDyadicMellinCharacter_ne_zero rho
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hz).ne'
  have href : zr = (star z)⁻¹ := by
    exact fzzCigarParityDyadicMellinCharacter_reflection rho
  have hstar : star z * z = ((n ^ 2 : ℝ) : ℂ) := by
    simpa [n] using Complex.conj_mul' z
  dsimp only [z, zr, n] at *
  rw [href]
  have hstarz : star (fzzCigarParityDyadicMellinCharacter rho) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hz
  rw [norm_inv, norm_star]
  field_simp [hstarz]
  simpa [pow_two] using hstar.symm

theorem norm_fzzCigarParityDyadicMellinCharacter (rho : ℂ) :
    ‖fzzCigarParityDyadicMellinCharacter rho‖ =
      Real.exp (Real.log 2 * (rho.re - 1 / 2)) := by
  exact norm_centeredComplexModularCharacter_ofReal rho (Real.log 2)

/-- Exact reflected crossing defect: unit phase cancels, leaving only reciprocal radial weight. -/
theorem fzzCigarParityMellinCharacterNormalizedCrossing_sub_reflection
    (beta : ℝ) (rho : ℂ) :
    fzzCigarParityMellinCharacterNormalizedCrossing beta rho -
        fzzCigarParityMellinCharacterNormalizedCrossing beta
          (criticalLineReflectionPoint rho) =
      (fzzKreinRAt beta : ℂ) *
        ((‖fzzCigarParityDyadicMellinCharacter rho‖ : ℂ) -
          (‖fzzCigarParityDyadicMellinCharacter
            (criticalLineReflectionPoint rho)‖ : ℂ)) := by
  rw [fzzCigarParityMellinCharacterNormalizedCrossing_eq,
    fzzCigarParityMellinCharacterNormalizedCrossing_eq,
    fzzCigarParityDyadicMellinCharacter_normalizedPhase_reflection]
  ring

/-- Closed exponential formula for the transverse reflected-crossing defect. -/
theorem fzzCigarParityMellinCharacterNormalizedCrossing_sub_reflection_re
    (beta : ℝ) (rho : ℂ) :
    (fzzCigarParityMellinCharacterNormalizedCrossing beta rho -
        fzzCigarParityMellinCharacterNormalizedCrossing beta
          (criticalLineReflectionPoint rho)).re =
      fzzKreinRAt beta *
        (Real.exp (Real.log 2 * (rho.re - 1 / 2)) -
          Real.exp (-(Real.log 2 * (rho.re - 1 / 2)))) := by
  rw [fzzCigarParityMellinCharacterNormalizedCrossing_sub_reflection]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.sub_re,
    Complex.ofReal_im, sub_zero, zero_mul]
  rw [norm_fzzCigarParityDyadicMellinCharacter,
    norm_fzzCigarParityDyadicMellinCharacter,
    criticalLineReflectionPoint_weight]
  congr 2
  ring_nf

theorem fzzCigarParityMellinCharacterNormalizedCrossing_sub_reflection_im
    (beta : ℝ) (rho : ℂ) :
    (fzzCigarParityMellinCharacterNormalizedCrossing beta rho -
        fzzCigarParityMellinCharacterNormalizedCrossing beta
          (criticalLineReflectionPoint rho)).im = 0 := by
  rw [fzzCigarParityMellinCharacterNormalizedCrossing_sub_reflection]
  simp

theorem fzzCigarParityMellinCharacterNormalizedCrossing_sub_reflection_re_pos_iff
    {beta : ℝ} (hbeta : 0 < beta) (rho : ℂ) :
    0 < (fzzCigarParityMellinCharacterNormalizedCrossing beta rho -
        fzzCigarParityMellinCharacterNormalizedCrossing beta
          (criticalLineReflectionPoint rho)).re ↔
      1 / 2 < rho.re := by
  rw [fzzCigarParityMellinCharacterNormalizedCrossing_sub_reflection_re]
  have hR := fzzKreinRAt_pos hbeta
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · intro h
    have hexp :
        Real.exp (-(Real.log 2 * (rho.re - 1 / 2))) <
          Real.exp (Real.log 2 * (rho.re - 1 / 2)) := by
      nlinarith
    have harg := (Real.exp_lt_exp).mp hexp
    nlinarith
  · intro hre
    have harg :
        -(Real.log 2 * (rho.re - 1 / 2)) <
          Real.log 2 * (rho.re - 1 / 2) := by
      nlinarith
    have hexp := (Real.exp_lt_exp).mpr harg
    nlinarith

theorem fzzCigarParityMellinCharacterNormalizedCrossing_sub_reflection_re_neg_iff
    {beta : ℝ} (hbeta : 0 < beta) (rho : ℂ) :
    (fzzCigarParityMellinCharacterNormalizedCrossing beta rho -
        fzzCigarParityMellinCharacterNormalizedCrossing beta
          (criticalLineReflectionPoint rho)).re < 0 ↔
      rho.re < 1 / 2 := by
  rw [fzzCigarParityMellinCharacterNormalizedCrossing_sub_reflection_re]
  have hR := fzzKreinRAt_pos hbeta
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · intro h
    have hexp :
        Real.exp (Real.log 2 * (rho.re - 1 / 2)) <
          Real.exp (-(Real.log 2 * (rho.re - 1 / 2))) := by
      nlinarith
    have harg := (Real.exp_lt_exp).mp hexp
    nlinarith
  · intro hre
    have harg :
        Real.log 2 * (rho.re - 1 / 2) <
          -(Real.log 2 * (rho.re - 1 / 2)) := by
      nlinarith
    have hexp := (Real.exp_lt_exp).mpr harg
    nlinarith

/-- **FZZ crossing reflection law.** At every positive physical scale, matched reflected
crossings are equivalent to critical-line placement. -/
theorem fzzCigarParityMellinCharacterNormalizedCrossing_eq_reflection_iff
    {beta : ℝ} (hbeta : 0 < beta) (rho : ℂ) :
    fzzCigarParityMellinCharacterNormalizedCrossing beta rho =
        fzzCigarParityMellinCharacterNormalizedCrossing beta
          (criticalLineReflectionPoint rho) ↔
      rho.re = 1 / 2 := by
  rw [← sub_eq_zero]
  constructor
  · intro hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.zero_re,
      fzzCigarParityMellinCharacterNormalizedCrossing_sub_reflection_re] at hre
    have hR := fzzKreinRAt_pos hbeta
    have hexpeq :
        Real.exp (Real.log 2 * (rho.re - 1 / 2)) =
          Real.exp (-(Real.log 2 * (rho.re - 1 / 2))) := by
      nlinarith
    have harg := Real.exp_injective hexpeq
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  · intro hre
    rw [fzzCigarParityMellinCharacterNormalizedCrossing_sub_reflection]
    have hnorm : ‖fzzCigarParityDyadicMellinCharacter rho‖ = 1 := by
      rw [norm_fzzCigarParityDyadicMellinCharacter, hre]
      norm_num
    have hrefre : (criticalLineReflectionPoint rho).re = 1 / 2 := by
      have hw := criticalLineReflectionPoint_weight rho
      rw [hre] at hw
      norm_num at hw
      linarith
    have hnormref :
        ‖fzzCigarParityDyadicMellinCharacter
          (criticalLineReflectionPoint rho)‖ = 1 := by
      rw [norm_fzzCigarParityDyadicMellinCharacter, hrefre]
      norm_num
    rw [hnorm, hnormref, sub_self, mul_zero]

/-- Every open-strip parity-Mellin mode has matched reflected crossing at one physical scale. -/
def FZZCigarParityMellinReflectionCrossingMatchedAt (beta : ℝ) : Prop :=
  ∀ rho : ℂ, 0 < rho.re → rho.re < 1 → FZZCigarParityMellinMode rho →
    fzzCigarParityMellinCharacterNormalizedCrossing beta rho =
      fzzCigarParityMellinCharacterNormalizedCrossing beta
        (criticalLineReflectionPoint rho)

/-- One arbitrary positive FZZ source scale already gives an exact source-native RH endpoint. -/
theorem fzzCigarParityMellinReflectionCrossingMatchedAt_iff_riemannHypothesis
    {beta : ℝ} (hbeta : 0 < beta) :
    FZZCigarParityMellinReflectionCrossingMatchedAt beta ↔
      RiemannHypothesis := by
  constructor
  · intro hmatch
    apply fzzCigarParityMellinComplete_iff_riemannHypothesis.mp
    intro rho h0 h1 hmode
    have hre :=
      (fzzCigarParityMellinCharacterNormalizedCrossing_eq_reflection_iff
        hbeta rho).mp (hmatch rho h0 h1 hmode)
    refine ⟨rho.im, ?_⟩
    apply Complex.ext
    · rw [fzzPunctureHorizonDilationSpectralParameter_re, hre]
    · rw [fzzPunctureHorizonDilationSpectralParameter_im]
  · intro hRH rho h0 h1 hmode
    apply (fzzCigarParityMellinCharacterNormalizedCrossing_eq_reflection_iff
      hbeta rho).mpr
    have hxi : xi rho = 0 :=
      (fzzCigarParityMellin_eq_zero_iff_xi_eq_zero h0 h1).mp hmode
    exact xi_zero_re_eq_half_of_RH hRH hxi

/-- Reflected-crossing matching over the complete positive physical scale ray. -/
def FZZCigarParityMellinUniversalReflectionCrossingMatched : Prop :=
  ∀ beta : ℝ, 0 < beta →
    FZZCigarParityMellinReflectionCrossingMatchedAt beta

/-- Universal reflected-crossing matching is exactly RH-strength. -/
theorem fzzCigarParityMellinUniversalReflectionCrossingMatched_iff_riemannHypothesis :
    FZZCigarParityMellinUniversalReflectionCrossingMatched ↔
      RiemannHypothesis := by
  constructor
  · intro hall
    exact (fzzCigarParityMellinReflectionCrossingMatchedAt_iff_riemannHypothesis
      (beta := 1) zero_lt_one).mp (hall 1 zero_lt_one)
  · intro hRH beta hbeta
    exact (fzzCigarParityMellinReflectionCrossingMatchedAt_iff_riemannHypothesis
      hbeta).mpr hRH

end

end RHTower
