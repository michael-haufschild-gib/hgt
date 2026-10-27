import GaloisForLFunctions.ConjugateDiagonalGeometry.ThetaSourceMetric
import GaloisForLFunctions.ConjugateDiagonalGeometry.MovingSourceMetric

/-!
# Positive theta-source formulas at moving ordinate and Hecke scale

Literal arithmetic theta amplitudes and first moments compute the full
conjugate-diagonal trace uniformly in the joint C² window. The same source-only
regulator serves every compact test and every finite moment order. The formula
evaluates the positive trace and its Hecke defect; it does not force that defect
to vanish.
-/

open Complex
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization

/-- A positive arithmetic formula for every moving collided moment in the joint C² window. -/
theorem thetaSource_uniform_moving_moments (f : CompactTest) (j : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ L τ : ℝ,
      |τ| ≤ (n : ℝ) / 2 → (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
        |thetaSourceMomentReading (sourceTwist τ f) L j n -
          ∑' ρ : zetaZeroConfig.carrier,
            zetaWeight (sourceTwist τ f) ρ * depthKernel L (zetaDepth ρ) ^ j| < ε := by
  simpa only [thetaSourceMomentReading_eq_common, zetaSourceTrace_depthKernel_eq] using
    commonSourceReading_uniform_moving_moments f j

/-- The full collided norm is recovered uniformly at every ordinate in the expanding window. -/
theorem thetaSource_uniform_moving_collided (f : CompactTest) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ τ : ℝ,
      |τ| ≤ (n : ℝ) / 2 →
        |thetaSourceMomentReading (sourceTwist τ f) 0 0 n -
          collidedForm zetaZeroConfig (twist τ f.1)| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := thetaSource_uniform_moving_moments f 0 ε hε
  refine ⟨N, fun n hn τ hτ => ?_⟩
  have hwindow : ((0 : ℕ) : ℝ) * |(0 : ℝ)| ≤ 2 * Real.log ((n : ℝ) + 1) := by
    rw [Nat.cast_zero, zero_mul]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by
      have h := Nat.cast_nonneg (α := ℝ) n
      linarith only [h]))
  simpa only [pow_zero, mul_one, zetaWeight, collidedForm, sourceTwist] using
    hN n hn 0 τ hτ hwindow

/-- The positive arithmetic formula computes the Hecke defect at logarithmic translation scales. -/
theorem thetaSource_uniform_moving_heckeDefect (f : CompactTest) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ L τ : ℝ,
      |τ| ≤ (n : ℝ) / 2 → |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
        |thetaSourceMomentReading (sourceTwist τ f) L 1 n -
          heckeDefect (sourceTwist τ f) L| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := thetaSource_uniform_moving_moments f 1 ε hε
  refine ⟨N, fun n hn L τ hτ hL => ?_⟩
  have hwindow : ((1 : ℕ) : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) := by
    simpa only [Nat.cast_one, one_mul] using hL
  simpa only [pow_one, heckeDefect] using hN n hn L τ hτ hwindow

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.thetaSource_uniform_moving_moments
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.thetaSource_uniform_moving_collided
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.thetaSource_uniform_moving_heckeDefect
