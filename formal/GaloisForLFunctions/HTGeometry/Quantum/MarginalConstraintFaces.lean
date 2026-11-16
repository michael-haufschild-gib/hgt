import GaloisForLFunctions.HTGeometry.Quantum.PositiveConstraintSupport
import GaloisForLFunctions.HTGeometry.Arxiv2510ReducedDensityMatrixApplications

/-!
# Marginals detect global support constraints

A squared local constraint has the same expectation before and after partial
trace. Positivity upgrades this scalar equality to an equivalence of exact
annihilation conditions. The constrained marginal states form exposed faces.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.Quantum

open Matrix _root_.HTGeometry.ConstraintRelativity
open scoped Kronecker ComplexOrder

variable {m n σ : Type*} [Fintype m] [DecidableEq m]
  [Fintype n] [DecidableEq n] [Fintype σ]

/-- Partial trace preserves the energy of a constraint on the retained subsystem. -/
theorem constraintEnergy_partialTraceRight (C : Matrix m m ℂ)
    (ρ : Matrix (m × n) (m × n) ℂ) :
    constraintEnergy C (partialTraceRight ρ) =
      constraintEnergy (C ⊗ₖ (1 : Matrix n n ℂ)) ρ := by
  cases isEmpty_or_nonempty m
  · simp [constraintEnergy, Matrix.trace]
  cases isEmpty_or_nonempty n
  · simp [constraintEnergy, partialTraceRight, Matrix.trace]
  unfold constraintEnergy
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← trace_partialTraceRight,
    partialTraceRight_mul_leftLocal, partialTraceRight_leftLocal_mul]

/-- The marginal and the global state satisfy exactly the same local kernel constraint. -/
theorem partialTraceRight_annihilation_iff (C : Matrix m m ℂ)
    (ρ : DensityMatrix (m × n)) :
    C * partialTraceRight ρ.1 = 0 ↔ (C ⊗ₖ (1 : Matrix n n ℂ)) * ρ.1 = 0 := by
  rw [← constraintEnergy_eq_zero_iff C (posSemidef_partialTraceRight ρ.2.1),
    constraintEnergy_partialTraceRight, constraintEnergy_eq_zero_iff _ ρ.2.1]

/-- A marginal selected by finitely many squared constraints certifies global support. -/
theorem partialTraceRight_constraintHamiltonian_eq_zero_iff
    (C : σ → Matrix m m ℂ) (ρ : DensityMatrix (m × n)) :
    (constraintHamiltonian C * partialTraceRight ρ.1).trace.re = 0 ↔
      ∀ s, (C s ⊗ₖ (1 : Matrix n n ℂ)) * ρ.1 = 0 := by
  rw [trace_constraintHamiltonian_eq_zero_iff C (posSemidef_partialTraceRight ρ.2.1)]
  exact forall_congr' fun s => partialTraceRight_annihilation_iff (C s) ρ

/-- The symmetric local-to-global support law for the other subsystem. -/
theorem constraintEnergy_partialTraceLeft (C : Matrix n n ℂ)
    (ρ : Matrix (m × n) (m × n) ℂ) :
    constraintEnergy C (partialTraceLeft ρ) =
      constraintEnergy ((1 : Matrix m m ℂ) ⊗ₖ C) ρ := by
  cases isEmpty_or_nonempty n
  · simp [constraintEnergy, Matrix.trace]
  cases isEmpty_or_nonempty m
  · simp [constraintEnergy, partialTraceLeft, Matrix.trace]
  unfold constraintEnergy
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← trace_partialTraceLeft,
    partialTraceLeft_mul_rightLocal, partialTraceLeft_rightLocal_mul]

theorem partialTraceLeft_annihilation_iff (C : Matrix n n ℂ)
    (ρ : DensityMatrix (m × n)) :
    C * partialTraceLeft ρ.1 = 0 ↔ ((1 : Matrix m m ℂ) ⊗ₖ C) * ρ.1 = 0 := by
  rw [← constraintEnergy_eq_zero_iff C (posSemidef_partialTraceLeft ρ.2.1),
    constraintEnergy_partialTraceLeft, constraintEnergy_eq_zero_iff _ ρ.2.1]

/-- The constraint face of normalized states is exposed without an existence assumption. -/
theorem density_constraintFace_isExposed (C : σ → Matrix m m ℂ) :
    IsExposed ℝ {ρ : Matrix m m ℂ | ρ.trace = 1 ∧ ρ.PosSemidef}
      (constraintFace C {ρ | ρ.trace = 1}) :=
  constraintFace_isExposed C _

omit [Fintype σ] in
/-- Every constrained marginal has a constrained global extension, explicitly the product
with the maximally mixed ancillary state. -/
theorem constrained_partialTraceRight_surjective [Nonempty n]
    (C : σ → Matrix m m ℂ) (ρ : DensityMatrix m) :
    (∀ s, C s * ρ.1 = 0) ↔
      ∃ τ : DensityMatrix (m × n), partialTraceRight τ.1 = ρ.1 ∧
        ∀ s, (C s ⊗ₖ (1 : Matrix n n ℂ)) * τ.1 = 0 := by
  constructor
  · intro h
    refine ⟨partialTraceRightDensitySection ρ, partialTraceRight_section ρ.1, ?_⟩
    intro s
    apply (partialTraceRight_annihilation_iff (C s) _).mp
    simpa only [partialTraceRightDensitySection, partialTraceRight_section] using h s
  · rintro ⟨τ, hτ, hC⟩ s
    rw [← hτ]
    exact (partialTraceRight_annihilation_iff (C s) τ).mpr (hC s)

end GaloisForLFunctions.HTGeometry.Quantum
