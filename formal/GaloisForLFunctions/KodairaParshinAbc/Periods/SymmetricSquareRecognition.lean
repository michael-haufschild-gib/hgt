import GaloisForLFunctions.KodairaParshinAbc.Periods.SymmetricSquare
import Mathlib.Tactic

/-!
# Exact recognition of a monic symmetric square

For a third-order operator with rational polynomial coefficients, the
Wilczynski invariant vanishes exactly when the operator is a symmetric
square. The second-order coefficients are reconstructed explicitly from
the two highest coefficients; the remaining coefficient is measured by
the invariant. This is the recognition mechanism in §3.3 of arXiv:2611.13126.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc.Periods

open Polynomial

def recoveredSlope (b₂ : ℚ[X]) : ℚ[X] := C (1 / 3 : ℚ) * b₂

def recoveredPotential (b₂ b₁ : ℚ[X]) : ℚ[X] :=
  C (1 / 4 : ℚ) * b₁ - C (1 / 12 : ℚ) * b₂.derivative - C (1 / 18 : ℚ) * b₂ ^ 2

theorem recoveredSlope_coefficient (b₂ : ℚ[X]) : 3 * recoveredSlope b₂ = b₂ := by
  apply Polynomial.funext
  intro x
  simp [recoveredSlope]

theorem recoveredPotential_coefficient (b₂ b₁ : ℚ[X]) :
    (recoveredSlope b₂).derivative + 2 * recoveredSlope b₂ ^ 2 +
      4 * recoveredPotential b₂ b₁ = b₁ := by
  apply Polynomial.funext
  intro x
  simp [recoveredSlope, recoveredPotential, derivative_mul, pow_two]
  ring

/-- The invariant is exactly the defect in the reconstructed zeroth-order coefficient. -/
theorem wilczynski_reconstruction_defect (b₂ b₁ b₀ : ℚ[X]) :
    wilczynskiNumerator b₂ b₁ b₀ =
      54 * (2 * (recoveredPotential b₂ b₁).derivative +
        4 * recoveredSlope b₂ * recoveredPotential b₂ b₁ - b₀) := by
  apply Polynomial.funext
  intro x
  simp [wilczynskiNumerator, recoveredSlope, recoveredPotential, derivative_mul, pow_two]
  ring

theorem wilczynski_zero_iff_reconstruction (b₂ b₁ b₀ : ℚ[X]) :
    wilczynskiNumerator b₂ b₁ b₀ = 0 ↔
      b₀ = 2 * (recoveredPotential b₂ b₁).derivative +
        4 * recoveredSlope b₂ * recoveredPotential b₂ b₁ := by
  have h54 : (54 : ℚ[X]) ≠ 0 := by norm_num
  rw [wilczynski_reconstruction_defect, mul_eq_zero]
  simp only [h54, false_or, sub_eq_zero]
  exact eq_comm

/-- Vanishing of the invariant is a complete criterion, with no assumed lower-order factor. -/
theorem exists_symmetricSquare_iff (b₂ b₁ b₀ : ℚ[X]) :
    (∃ b c : ℚ[X], b₂ = 3 * b ∧ b₁ = b.derivative + 2 * b ^ 2 + 4 * c ∧
      b₀ = 2 * c.derivative + 4 * b * c) ↔
      wilczynskiNumerator b₂ b₁ b₀ = 0 := by
  constructor
  · rintro ⟨b, c, rfl, rfl, rfl⟩
    exact wilczynski_symmetricSquare b c
  · intro h
    exact ⟨recoveredSlope b₂, recoveredPotential b₂ b₁,
      (recoveredSlope_coefficient b₂).symm, (recoveredPotential_coefficient b₂ b₁).symm,
      (wilczynski_zero_iff_reconstruction b₂ b₁ b₀).mp h⟩

end GaloisForLFunctions.KodairaParshinAbc.Periods

#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.recoveredSlope_coefficient
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.recoveredPotential_coefficient
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.wilczynski_reconstruction_defect
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.wilczynski_zero_iff_reconstruction
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.exists_symmetricSquare_iff
