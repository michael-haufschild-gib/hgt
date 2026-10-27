import GaloisForLFunctions.ConjugateDiagonalGeometry.ThetaSourceMetric
import GaloisForLFunctions.ConjugateDiagonalGeometry.ExplicitSourceMetric

/-!
# Prescribed positive theta readings in moving arithmetic windows

Literal arithmetic theta amplitudes and first moments compute the full
conjugate-diagonal trace uniformly in the joint C² window. The same source-only
exponential regulator serves every compact test and every finite moment order.
No error-tested index or zero coordinate enters that regulator. The formula
evaluates the positive trace and its Hecke defect; it does not force that defect
to vanish.
-/

open Complex MeasureTheory
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization


/-- Literal arithmetic theta reading with the prescribed exponential regulator. -/
def explicitThetaSourceMomentReading (f : CompactTest) (L : ℝ) (j n : ℕ) : ℝ :=
  Real.pi⁻¹ * ∫ z, sourceCutoff n z * sourceDepthKernel f L j z *
    thetaSourceCurvature (explicitSourceRegulator n) z

theorem explicitThetaSourceMomentReading_nonneg (f : CompactTest) (L : ℝ) (j n : ℕ) :
    0 ≤ explicitThetaSourceMomentReading f L j n := by
  apply mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
  apply integral_nonneg
  intro z
  exact mul_nonneg (mul_nonneg (sourceCutoff n).nonneg
    (mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg (depthKernel_nonneg _ _) j)))
    (thetaSourceCurvature_nonneg (explicitSourceRegulator_pos n).le z)

theorem explicitThetaSourceMomentReading_eq_source (f : CompactTest) (L : ℝ) (j n : ℕ) :
    explicitThetaSourceMomentReading f L j n = explicitSourceReading (sourceDepthKernel f L j) n := by
  simp only [explicitThetaSourceMomentReading, explicitSourceReading,
    thetaSourceCurvature_eq_xiCurvatureDensity]

/-- A positive arithmetic formula for every moving collided moment in the joint C² window. -/
theorem explicitThetaSource_uniform_moving_moments (f : CompactTest) (j : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ L τ : ℝ,
      |τ| ≤ (n : ℝ) / 2 → (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
        |explicitThetaSourceMomentReading (sourceTwist τ f) L j n -
          ∑' ρ : zetaZeroConfig.carrier,
            zetaWeight (sourceTwist τ f) ρ * depthKernel L (zetaDepth ρ) ^ j| < ε := by
  simpa only [explicitThetaSourceMomentReading_eq_source, zetaSourceTrace_depthKernel_eq] using
    explicitSourceReading_uniform_moving_moments f j

/-- The full collided norm is recovered uniformly at every ordinate in the expanding window. -/
theorem explicitThetaSource_uniform_moving_collided (f : CompactTest) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ τ : ℝ,
      |τ| ≤ (n : ℝ) / 2 →
        |explicitThetaSourceMomentReading (sourceTwist τ f) 0 0 n -
          collidedForm zetaZeroConfig (twist τ f.1)| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := explicitThetaSource_uniform_moving_moments f 0 ε hε
  refine ⟨N, fun n hn τ hτ => ?_⟩
  have hwindow : ((0 : ℕ) : ℝ) * |(0 : ℝ)| ≤ 2 * Real.log ((n : ℝ) + 1) := by
    rw [Nat.cast_zero, zero_mul]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by
      have h := Nat.cast_nonneg (α := ℝ) n
      linarith only [h]))
  simpa only [pow_zero, mul_one, zetaWeight, collidedForm, sourceTwist] using
    hN n hn 0 τ hτ hwindow

/-- The positive arithmetic formula computes the Hecke defect at logarithmic translation scales. -/
theorem explicitThetaSource_uniform_moving_heckeDefect (f : CompactTest) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ L τ : ℝ,
      |τ| ≤ (n : ℝ) / 2 → |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
        |explicitThetaSourceMomentReading (sourceTwist τ f) L 1 n -
          heckeDefect (sourceTwist τ f) L| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := explicitThetaSource_uniform_moving_moments f 1 ε hε
  refine ⟨N, fun n hn L τ hτ hL => ?_⟩
  have hwindow : ((1 : ℕ) : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) := by
    simpa only [Nat.cast_one, one_mul] using hL
  simpa only [pow_one, heckeDefect] using hN n hn L τ hτ hwindow

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.explicitThetaSource_uniform_moving_moments
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.explicitThetaSource_uniform_moving_collided
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.explicitThetaSource_uniform_moving_heckeDefect
