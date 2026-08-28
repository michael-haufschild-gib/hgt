import GaloisForLFunctions.RHTower.FZZCigarParityFixedReporterUniformConeEscape

/-!
# Covariant FZZ reporter conservation and matching rigidity

The unique Hermitian reporter contragredient to the stabilized source flow conserves unit diagonal
energy exactly.  Its reflected Mellin defect is therefore time-invariant: covariant transport
retains an all-time critical-line detector but cannot create the missing divisor matching.
-/

open Complex

namespace RHTower

noncomputable section

/-- Source-covariant off-diagonal compensation ratio `k/e`. -/
def fzzCigarParityDilatedCovariantReporterRatio
    (beta t : ℝ) : ℝ :=
  fzzCigarParityDilatedSecondDiagonalFlowShear beta t /
    Real.exp (fzzKreinPAt beta * t)

theorem fzzCigarParityDilatedCovariantReporterRatio_eq
    (beta t : ℝ) :
    fzzCigarParityDilatedCovariantReporterRatio beta t =
      fzzCigarParityDilatedStabilizedFlowSlope beta *
        (1 - Real.exp (-(fzzKreinPAt beta * t))) := by
  rw [fzzCigarParityDilatedCovariantReporterRatio,
    fzzCigarParityDilatedSecondDiagonalFlowShear,
    fzzCigarParityDilatedStabilizedFlowSlope]
  rw [Real.exp_neg]
  have he : Real.exp (fzzKreinPAt beta * t) ≠ 0 := Real.exp_ne_zero _
  field_simp [he]

theorem fzzCigarParityDilatedCovariantReporter_pullbackA_eq_zero
    (beta t : ℝ) :
    fzzCigarParityDilatedStabilizedFlowHermitianA beta t
        (fzzCigarParityDilatedCovariantReporterRatio beta t ^ 2)
        (fzzCigarParityDilatedCovariantReporterRatio beta t) 1 = 0 := by
  rw [fzzCigarParityDilatedStabilizedFlowHermitianA,
    fzzCigarParityDilatedCovariantReporterRatio]
  have he : Real.exp (fzzKreinPAt beta * t) ≠ 0 := Real.exp_ne_zero _
  field_simp [he]
  ring

theorem fzzCigarParityDilatedCovariantReporter_pullbackB_eq_zero
    (beta t : ℝ) :
    fzzCigarParityDilatedStabilizedFlowHermitianB beta t
        (fzzCigarParityDilatedCovariantReporterRatio beta t) 1 = 0 := by
  rw [fzzCigarParityDilatedStabilizedFlowHermitianB,
    fzzCigarParityDilatedCovariantReporterRatio]
  have he : Real.exp (fzzKreinPAt beta * t) ≠ 0 := Real.exp_ne_zero _
  field_simp [he]
  ring

/-- Exact all-time conservation of unit diagonal energy by the moving reporter. -/
theorem fzzCigarParityDilatedCovariantReporter_conservation
    (beta t : ℝ) (u : ℂ × ℂ) :
    fzzCigarParityHermitianQuadraticObservable
        (fzzCigarParityDilatedCovariantReporterRatio beta t ^ 2)
        (fzzCigarParityDilatedCovariantReporterRatio beta t) 0 1
        (fzzCigarParityDilatedSecondDiagonalStabilizedFlow beta t u) =
      fzzCigarParityHermitianQuadraticObservable 0 0 0 1 u := by
  rw [fzzCigarParityDilatedSecondDiagonalStabilizedFlow_hermitian_pullback,
    fzzCigarParityDilatedCovariantReporter_pullbackA_eq_zero,
    fzzCigarParityDilatedCovariantReporter_pullbackB_eq_zero]
  simp [fzzCigarParityDilatedStabilizedFlowHermitianC]

/-- Coefficient-level uniqueness of the moving reporter conserving unit diagonal energy. -/
theorem fzzCigarParityDilatedReporter_pullback_eq_unitSecondDiagonal_iff
    (beta t a b c d : ℝ) :
    (fzzCigarParityDilatedStabilizedFlowHermitianA beta t a b d = 0 ∧
      fzzCigarParityDilatedStabilizedFlowHermitianB beta t b d = 0 ∧
      fzzCigarParityDilatedStabilizedFlowHermitianC beta t c = 0 ∧
      d = 1) ↔
    (a = fzzCigarParityDilatedCovariantReporterRatio beta t ^ 2 ∧
      b = fzzCigarParityDilatedCovariantReporterRatio beta t ∧
      c = 0 ∧ d = 1) := by
  let e := Real.exp (fzzKreinPAt beta * t)
  let k := fzzCigarParityDilatedSecondDiagonalFlowShear beta t
  have he : e ≠ 0 := Real.exp_ne_zero _
  constructor
  · rintro ⟨hA, hB, hC, hd⟩
    have hc : c = 0 := by
      rw [fzzCigarParityDilatedStabilizedFlowHermitianC] at hC
      exact (mul_eq_zero.mp hC).resolve_left he
    have hb : b = fzzCigarParityDilatedCovariantReporterRatio beta t := by
      rw [fzzCigarParityDilatedStabilizedFlowHermitianB, hd] at hB
      rw [fzzCigarParityDilatedCovariantReporterRatio]
      field_simp [he] at hB ⊢
      linarith
    have ha : a = fzzCigarParityDilatedCovariantReporterRatio beta t ^ 2 := by
      rw [fzzCigarParityDilatedStabilizedFlowHermitianA, hd, hb] at hA
      rw [fzzCigarParityDilatedCovariantReporterRatio] at hA ⊢
      field_simp [he] at hA ⊢
      nlinarith
    exact ⟨ha, hb, hc, hd⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨
      fzzCigarParityDilatedCovariantReporter_pullbackA_eq_zero beta t,
      fzzCigarParityDilatedCovariantReporter_pullbackB_eq_zero beta t,
      by simp [fzzCigarParityDilatedStabilizedFlowHermitianC], rfl⟩

/-- Moving covariant readings remain an exact pointwise critical-line detector at every time. -/
theorem fzzCigarParityDilatedCovariantReporter_mellinReading_eq_reflection_iff
    (beta t : ℝ) (rho : ℂ) :
    fzzCigarParityHermitianQuadraticObservable
        (fzzCigarParityDilatedCovariantReporterRatio beta t ^ 2)
        (fzzCigarParityDilatedCovariantReporterRatio beta t) 0 1
        (fzzCigarParityDilatedSecondDiagonalStabilizedFlow beta t
          (fzzCigarParityMellinCharacterCarrier rho)) =
      fzzCigarParityHermitianQuadraticObservable
        (fzzCigarParityDilatedCovariantReporterRatio beta t ^ 2)
        (fzzCigarParityDilatedCovariantReporterRatio beta t) 0 1
        (fzzCigarParityDilatedSecondDiagonalStabilizedFlow beta t
          (fzzCigarParityMellinCharacterCarrier
            (criticalLineReflectionPoint rho))) ↔
      rho.re = 1 / 2 := by
  rw [fzzCigarParityDilatedCovariantReporter_conservation,
    fzzCigarParityDilatedCovariantReporter_conservation]
  exact fzzCigarParityMellinCharacterUnitSecondDiagonalReading_eq_reflection_iff rho

/-- The whole reflected reading defect is conserved, not merely its zero locus. -/
theorem fzzCigarParityDilatedCovariantReporter_reflectionDefect_conserved
    (beta t : ℝ) (rho : ℂ) :
    fzzCigarParityHermitianQuadraticObservable
          (fzzCigarParityDilatedCovariantReporterRatio beta t ^ 2)
          (fzzCigarParityDilatedCovariantReporterRatio beta t) 0 1
          (fzzCigarParityDilatedSecondDiagonalStabilizedFlow beta t
            (fzzCigarParityMellinCharacterCarrier rho)) -
        fzzCigarParityHermitianQuadraticObservable
          (fzzCigarParityDilatedCovariantReporterRatio beta t ^ 2)
          (fzzCigarParityDilatedCovariantReporterRatio beta t) 0 1
          (fzzCigarParityDilatedSecondDiagonalStabilizedFlow beta t
            (fzzCigarParityMellinCharacterCarrier
              (criticalLineReflectionPoint rho))) =
      fzzCigarParityMellinCharacterHermitianReading 0 0 0 1 rho -
        fzzCigarParityMellinCharacterHermitianReading 0 0 0 1
          (criticalLineReflectionPoint rho) := by
  rw [fzzCigarParityDilatedCovariantReporter_conservation,
    fzzCigarParityDilatedCovariantReporter_conservation]
  rfl

theorem fzzCigarParityDilatedCovariantReporter_mellinReading_ne_reflection_of_re_ne_half
    (beta t : ℝ) (rho : ℂ) (hre : rho.re ≠ 1 / 2) :
    fzzCigarParityHermitianQuadraticObservable
        (fzzCigarParityDilatedCovariantReporterRatio beta t ^ 2)
        (fzzCigarParityDilatedCovariantReporterRatio beta t) 0 1
        (fzzCigarParityDilatedSecondDiagonalStabilizedFlow beta t
          (fzzCigarParityMellinCharacterCarrier rho)) ≠
      fzzCigarParityHermitianQuadraticObservable
        (fzzCigarParityDilatedCovariantReporterRatio beta t ^ 2)
        (fzzCigarParityDilatedCovariantReporterRatio beta t) 0 1
        (fzzCigarParityDilatedSecondDiagonalStabilizedFlow beta t
          (fzzCigarParityMellinCharacterCarrier
            (criticalLineReflectionPoint rho))) := by
  intro heq
  exact hre
    ((fzzCigarParityDilatedCovariantReporter_mellinReading_eq_reflection_iff
      beta t rho).mp heq)

/-- Universal divisor matching by the covariant moving reporter at one time. -/
def FZZCigarParityDilatedCovariantReporterReflectionMatchedAt
    (beta t : ℝ) : Prop :=
  ∀ rho : ℂ, 0 < rho.re → rho.re < 1 → FZZCigarParityMellinMode rho →
    fzzCigarParityHermitianQuadraticObservable
        (fzzCigarParityDilatedCovariantReporterRatio beta t ^ 2)
        (fzzCigarParityDilatedCovariantReporterRatio beta t) 0 1
        (fzzCigarParityDilatedSecondDiagonalStabilizedFlow beta t
          (fzzCigarParityMellinCharacterCarrier rho)) =
      fzzCigarParityHermitianQuadraticObservable
        (fzzCigarParityDilatedCovariantReporterRatio beta t ^ 2)
        (fzzCigarParityDilatedCovariantReporterRatio beta t) 0 1
        (fzzCigarParityDilatedSecondDiagonalStabilizedFlow beta t
          (fzzCigarParityMellinCharacterCarrier
            (criticalLineReflectionPoint rho)))

/-- Covariant transport does not lower the global proof burden: its divisor matching is exactly
the original fixed unit-diagonal matching. -/
theorem fzzCigarParityDilatedCovariantReporterReflectionMatchedAt_iff_unitSecondDiagonal
    (beta t : ℝ) :
    FZZCigarParityDilatedCovariantReporterReflectionMatchedAt beta t ↔
      FZZCigarParityMellinHermitianReflectionMatched 0 0 0 1 := by
  constructor <;> intro h rho h0 h1 hmode
  · have hm := h rho h0 h1 hmode
    rw [fzzCigarParityDilatedCovariantReporter_conservation,
      fzzCigarParityDilatedCovariantReporter_conservation] at hm
    exact hm
  · have hm := h rho h0 h1 hmode
    rw [fzzCigarParityDilatedCovariantReporter_conservation,
      fzzCigarParityDilatedCovariantReporter_conservation]
    exact hm

/-- **Covariant-reporter rigidity.** Matching at any source scale and time is exactly RH-strength. -/
theorem fzzCigarParityDilatedCovariantReporterReflectionMatchedAt_iff_riemannHypothesis
    (beta t : ℝ) :
    FZZCigarParityDilatedCovariantReporterReflectionMatchedAt beta t ↔
      RiemannHypothesis := by
  rw [fzzCigarParityDilatedCovariantReporterReflectionMatchedAt_iff_unitSecondDiagonal]
  exact fzzCigarParityMellinHermitianReflectionMatched_iff_riemannHypothesis
    0 0 0 1 (by norm_num) (by norm_num)

end

end RHTower

