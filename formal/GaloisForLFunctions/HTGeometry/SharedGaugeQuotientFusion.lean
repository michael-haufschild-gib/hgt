import GaloisForLFunctions.HTGeometry.PrimeBooleanMassHankelQuantumFusion

/-!
# Shared-gauge quotient--fusion genesis

This module formalizes the unconditional polynomial core of quotient--fusion genesis.

For a weighted packet, `quotientFusionGenesisNumerator` is the Gram determinant
`C * Q - B^(2 : ℕ)`.  It is simultaneously:

* half the pairwise gauge-slope mismatch energy;
* the centered common-gauge residual after multiplication by total gauge weight.

For two already-fused blocks, `binaryQuotientFusionGenesis` proves the exact cross-multiplied
conservation law.  Its defect is one square, so it is nonnegative and vanishes exactly when the
two block gauges are compatible.  `binaryPartitionTransverseInformationConservation` transports
the same identity to the parity--clock/QFI normalization.

All main identities are polynomial.  They require no positivity, nonvanishing denominator,
choice of minimizer, or additional axiom.
-/

namespace HTGeometry

noncomputable section

open ConstraintFrameRelativity

variable {ι : Type*} [Fintype ι]

/-- Determinant of a scalar interest--gauge Gram block, with gauge energy `c`, cross moment `b`,
and interest energy `q`. -/
def quotientFusionGramDet (c b q : ℝ) : ℝ := c * q - b ^ (2 : ℕ)

/-- Cross-multiplied shared-gauge residual of a finite weighted slope packet. -/
def quotientFusionGenesisNumerator (c t : ι → ℝ) : ℝ :=
  capA c * capC c t - capB c t ^ (2 : ℕ)

/-- The quotient--fusion genesis numerator is exactly half the ordered pairwise slope-mismatch
energy.  This identity is unconditional; positive weights are needed only for its metric
interpretation. -/
theorem quotientFusionGenesisNumerator_eq_pairwise (c t : ι → ℝ) :
    quotientFusionGenesisNumerator c t =
      (∑ i, ∑ j, c i * c j * (t i - t j) ^ (2 : ℕ)) / 2 := by
  simpa [quotientFusionGenesisNumerator] using capA_mul_capC_sub_capB_sq c t

/-- Exact centered form without division by total gauge weight. -/
theorem capA_mul_quotientFusionGenesisNumerator_eq_centered (c t : ι → ℝ) :
    capA c * quotientFusionGenesisNumerator c t =
      ∑ i, c i * (capA c * t i - capB c t) ^ (2 : ℕ) := by
  have hs :
      (∑ i, c i * (capA c * t i - capB c t) ^ (2 : ℕ)) =
        ∑ i, c i * (capB c t - capA c * t i) ^ (2 : ℕ) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hs, quadratic_expand]
  unfold quotientFusionGenesisNumerator
  ring

/-- **Binary quotient--fusion genesis law.**

The cross-multiplied difference between quotient-after-fusion and the two separately quotiented
blocks is exactly the square of their gauge-slope incompatibility. -/
theorem binaryQuotientFusionGenesis
    (c₁ b₁ q₁ c₂ b₂ q₂ : ℝ) :
    c₁ * c₂ * quotientFusionGramDet (c₁ + c₂) (b₁ + b₂) (q₁ + q₂)
      - c₂ * (c₁ + c₂) * quotientFusionGramDet c₁ b₁ q₁
      - c₁ * (c₁ + c₂) * quotientFusionGramDet c₂ b₂ q₂
      = (c₂ * b₁ - c₁ * b₂) ^ (2 : ℕ) := by
  unfold quotientFusionGramDet
  ring

/-- Quotient--fusion genesis is nonnegative in its denominator-free form. -/
theorem binaryQuotientFusionGenesis_nonneg
    (c₁ b₁ q₁ c₂ b₂ q₂ : ℝ) :
    0 ≤ c₁ * c₂ * quotientFusionGramDet (c₁ + c₂) (b₁ + b₂) (q₁ + q₂)
      - c₂ * (c₁ + c₂) * quotientFusionGramDet c₁ b₁ q₁
      - c₁ * (c₁ + c₂) * quotientFusionGramDet c₂ b₂ q₂ := by
  rw [binaryQuotientFusionGenesis]
  positivity

/-- Exact zero classification: no genesis occurs precisely when the two block gauge slopes are
compatible after cross multiplication. -/
theorem binaryQuotientFusionGenesis_eq_zero_iff
    (c₁ b₁ q₁ c₂ b₂ q₂ : ℝ) :
    c₁ * c₂ * quotientFusionGramDet (c₁ + c₂) (b₁ + b₂) (q₁ + q₂)
      - c₂ * (c₁ + c₂) * quotientFusionGramDet c₁ b₁ q₁
      - c₁ * (c₁ + c₂) * quotientFusionGramDet c₂ b₂ q₂ = 0
      ↔ c₂ * b₁ = c₁ * b₂ := by
  rw [binaryQuotientFusionGenesis]
  constructor
  · intro h
    nlinarith [sq_nonneg (c₂ * b₁ - c₁ * b₂)]
  · intro h
    rw [h]
    simp

/-- Parity--clock Gram determinant for a block with Boolean variance `a`, mixed clock moment `b`,
and clock variance `c`. -/
def booleanClockGramDet (a b c : ℝ) : ℝ :=
  quotientFusionGramDet c (Real.pi * b) (Real.pi ^ (2 : ℕ) * a)

/-- The parity--clock block is `pi^(2 : ℕ)` times the ordinary two-moment determinant. -/
theorem booleanClockGramDet_eq (a b c : ℝ) :
    booleanClockGramDet a b c = Real.pi ^ (2 : ℕ) * (a * c - b ^ (2 : ℕ)) := by
  unfold booleanClockGramDet quotientFusionGramDet
  ring

/-- **Partition-QFI conservation, denominator-free form.**

The information gained by forcing two recurrent Boolean blocks to share one clock nuisance is
the squared incompatibility of their normalized block clocks, with the conventional factor
`4 * pi^(2 : ℕ)`. -/
theorem binaryPartitionTransverseInformationConservation
    (a₁ b₁ c₁ a₂ b₂ c₂ : ℝ) :
    4 * (c₁ * c₂ * booleanClockGramDet (a₁ + a₂) (b₁ + b₂) (c₁ + c₂)
      - c₂ * (c₁ + c₂) * booleanClockGramDet a₁ b₁ c₁
      - c₁ * (c₁ + c₂) * booleanClockGramDet a₂ b₂ c₂)
      = 4 * Real.pi ^ (2 : ℕ) * (c₂ * b₁ - c₁ * b₂) ^ (2 : ℕ) := by
  simp only [booleanClockGramDet_eq]
  ring

/-- Closed capstone: pairwise reconstruction, binary conservation, nonnegativity, exact zero
classification, and the fourth-organ QFI normalization are one algebraic mechanism. -/
theorem sharedGaugeQuotientFusion_capstone
    (c t : ι → ℝ) (c₁ b₁ q₁ c₂ b₂ q₂ a₁ a₂ : ℝ) :
    quotientFusionGenesisNumerator c t =
        (∑ i, ∑ j, c i * c j * (t i - t j) ^ (2 : ℕ)) / 2
      ∧ 0 ≤ c₁ * c₂ * quotientFusionGramDet (c₁ + c₂) (b₁ + b₂) (q₁ + q₂)
          - c₂ * (c₁ + c₂) * quotientFusionGramDet c₁ b₁ q₁
          - c₁ * (c₁ + c₂) * quotientFusionGramDet c₂ b₂ q₂
      ∧ (c₁ * c₂ * quotientFusionGramDet (c₁ + c₂) (b₁ + b₂) (q₁ + q₂)
          - c₂ * (c₁ + c₂) * quotientFusionGramDet c₁ b₁ q₁
          - c₁ * (c₁ + c₂) * quotientFusionGramDet c₂ b₂ q₂ = 0
        ↔ c₂ * b₁ = c₁ * b₂)
      ∧ 4 * (c₁ * c₂ * booleanClockGramDet (a₁ + a₂) (b₁ + b₂) (c₁ + c₂)
          - c₂ * (c₁ + c₂) * booleanClockGramDet a₁ b₁ c₁
          - c₁ * (c₁ + c₂) * booleanClockGramDet a₂ b₂ c₂)
        = 4 * Real.pi ^ (2 : ℕ) * (c₂ * b₁ - c₁ * b₂) ^ (2 : ℕ) := by
  exact ⟨quotientFusionGenesisNumerator_eq_pairwise c t,
    binaryQuotientFusionGenesis_nonneg c₁ b₁ q₁ c₂ b₂ q₂,
    binaryQuotientFusionGenesis_eq_zero_iff c₁ b₁ q₁ c₂ b₂ q₂,
    binaryPartitionTransverseInformationConservation a₁ b₁ c₁ a₂ b₂ c₂⟩

end

end HTGeometry
