import GaloisForLFunctions.HTGeometry.FokasLenellsJumpGeometry
import GaloisForLFunctions.HTGeometry.RiemannGaussian.FiniteHardyInnerMultiplier

/-!
# Nonlocal jump geometry for the corpus's finite Hardy models

Half-amplitude rational inner boundary values supply independent reflection
coefficients satisfying the exact accretivity criterion of the nonlocal
Fokas–Lenells jump. Pairing one such coefficient with its complex conjugate
makes the energy independent of the rational inner phase: its sharp coercivity
constant is exactly `3/4`, for every polynomial and every real boundary point.

This applies the mechanism of Proposition 3.4 of Yan–Zhang–Zhu,
arXiv:2607.19649, to the existing finite residual-inner multiplier construction.
-/

open Complex Polynomial RiemannGaussian
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- Half-amplitude reflection data supplied by the existing rational inner boundary. -/
def hardyCoefficient (p : ℂ[X]) (x : ℝ) : ℂ := lowerRootInnerBoundaryValue p x / 2

@[simp] theorem norm_hardyCoefficient (p : ℂ[X]) (x : ℝ) :
    ‖hardyCoefficient p x‖ = (1/2 : ℝ) := by simp [hardyCoefficient]

/-- Independently chosen finite Hardy models produce positive nonlocal jumps. -/
theorem hardy_jump_positive (p q : ℂ[X]) (x : ℝ) :
    ∀ u v : ℂ, u ≠ 0 ∨ v ≠ 0 →
      0 < energy (hardyCoefficient p x) (hardyCoefficient q x) u v := by
  apply (positive_iff _ _).mpr
  have hb := norm_add_le (hardyCoefficient p x) (star (hardyCoefficient q x))
  simp only [norm_star, norm_hardyCoefficient] at hb
  linarith

/-- Pairing a Hardy coefficient with its conjugate removes its phase from the energy. -/
theorem hardy_conjugate_energy (p : ℂ[X]) (x : ℝ) (u v : ℂ) :
    energy (hardyCoefficient p x) (star (hardyCoefficient p x)) u v =
      normSq u + (3/4 : ℝ)*normSq v := by
  rw [energy_completion]
  simp only [star_star, sub_self, zero_div, zero_mul, add_zero]
  have hn : normSq (hardyCoefficient p x + hardyCoefficient p x) = 1 := by
    rw [← two_mul, Complex.normSq_eq_norm_sq, norm_mul, norm_ofNat,
      norm_hardyCoefficient]
    ring
  rw [hn]
  ring

/-- The rational inner phase changes the jump but leaves its sharp energy margin fixed. -/
theorem hardy_conjugate_sharp_coercivity (p : ℂ[X]) (x : ℝ) (u v : ℂ) :
    (3/4 : ℝ)*(normSq u + normSq v) ≤
      energy (hardyCoefficient p x) (star (hardyCoefficient p x)) u v ∧
    energy (hardyCoefficient p x) (star (hardyCoefficient p x)) 0 1 = (3/4 : ℝ) := by
  constructor
  · rw [hardy_conjugate_energy]
    nlinarith [normSq_nonneg u]
  · rw [hardy_conjugate_energy]
    simp

end
end GaloisForLFunctions.HTGeometry.FokasLenells
