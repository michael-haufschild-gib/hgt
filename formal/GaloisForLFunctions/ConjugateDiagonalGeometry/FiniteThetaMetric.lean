import GaloisForLFunctions.ConjugateDiagonalGeometry.FiniteThetaReadingError
import GaloisForLFunctions.ConjugateDiagonalGeometry.ExplicitThetaErrorCertificate

/-!
# The collided metric from finite integer theta readings

A prescribed finite theta prefix and regulator recover every fixed-order
collided moment uniformly in moving ordinate and Hecke windows. The error
splits into a vanishing quartic exponential and an arithmetic reference
tail. Multiplicities are retained throughout the full divisor trace.
-/

open Complex MeasureTheory Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization _root_.RHTower

/-- A positive collided-moment reading using only a prescribed finite integer theta prefix. -/
def finiteThetaSourceMomentReading (f : CompactTest) (L : ℝ) (j n : ℕ) : ℝ :=
  finiteThetaSourceReading (sourceDepthKernel f L j) n

lemma finiteThetaSourceMomentReading_nonneg (f : CompactTest) (L : ℝ) (j n : ℕ) :
    0 ≤ finiteThetaSourceMomentReading f L j n := by
  apply mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
  apply integral_nonneg
  intro z
  exact mul_nonneg (mul_nonneg (sourceCutoff n).nonneg
    (mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg (depthKernel_nonneg _ _) j)))
    (finiteThetaSourceCurvature_nonneg (explicitSourceRegulator_pos n).le _ z)

/-- Finite integer truncation and the actual theta reading agree uniformly in both motions. -/
theorem finiteThetaSource_uniform_approximation (f : CompactTest) (j : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ L τ : ℝ,
      |τ| ≤ (n : ℝ) → (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
      |finiteThetaSourceMomentReading (sourceTwist τ f) L j n -
        explicitThetaSourceMomentReading (sourceTwist τ f) L j n| < ε := by
  obtain ⟨A, hA1, hA⟩ := norm_tr_le_sourceGaussian f
  let B := ((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2) * (4 * Real.pi * finiteThetaPotentialConstant)
  have hB : 0 ≤ B := mul_nonneg (by positivity)
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) finiteThetaPotentialConstant_nonneg)
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_explicitWindowError B) ε hε
  refine ⟨max 1 N, fun n hn L τ hτ hL => ?_⟩
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hsmall := hN n ((le_max_right _ _).trans hn)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hB (Real.exp_pos _).le)] at hsmall
  rw [finiteThetaSourceMomentReading, explicitThetaSourceMomentReading_eq_source]
  exact (finiteThetaSourceReading_error_le_window f (by linarith only [hA1]) hA
    j hn1 L τ hτ hL).trans_lt hsmall

/-- Finitely many literal integer theta terms recover the full moving collided trace. -/
theorem finiteThetaSource_uniform_moving_moments (f : CompactTest) (j : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ L τ : ℝ,
      |τ| ≤ (n : ℝ) / 2 → (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
        |finiteThetaSourceMomentReading (sourceTwist τ f) L j n -
          ∑' ρ : zetaZeroConfig.carrier,
            zetaWeight (sourceTwist τ f) ρ * depthKernel L (zetaDepth ρ) ^ j| < ε := by
  intro ε hε
  obtain ⟨Nf, hf⟩ := finiteThetaSource_uniform_approximation f j (ε / 2) (by positivity)
  obtain ⟨Nt, ht⟩ := explicitThetaSource_uniform_moving_moments f j (ε / 2) (by positivity)
  refine ⟨max Nf Nt, fun n hn L τ hτ hL => ?_⟩
  have hτ' : |τ| ≤ (n : ℝ) := by
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    linarith only [hτ, hn0]
  have hfinite := hf n ((le_max_left _ _).trans hn) L τ hτ' hL
  have htheta := ht n ((le_max_right _ _).trans hn) L τ hτ hL
  have htriangle := dist_triangle
    (finiteThetaSourceMomentReading (sourceTwist τ f) L j n)
    (explicitThetaSourceMomentReading (sourceTwist τ f) L j n)
    (∑' ρ : zetaZeroConfig.carrier,
      zetaWeight (sourceTwist τ f) ρ * depthKernel L (zetaDepth ρ) ^ j)
  simp only [Real.dist_eq] at htriangle
  linarith only [hfinite, htheta, htriangle]

/-- The finite arithmetic readings have a source-only error certificate for the full zero trace. -/
theorem exists_finiteThetaSource_logarithmic_error_bound (f : CompactTest) (j : ℕ) :
    ∃ B D : ℝ, 0 ≤ B ∧ 0 ≤ D ∧ ∀ n : ℕ, 1 ≤ n → ∀ L τ : ℝ,
      |τ| ≤ (n : ℝ) / 2 → (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
      |finiteThetaSourceMomentReading (sourceTwist τ f) L j n -
        ∑' ρ : zetaZeroConfig.carrier,
          zetaWeight (sourceTwist τ f) ρ * depthKernel L (zetaDepth ρ) ^ j| ≤
      B * Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) +
        D * ((16 / (n : ℝ)) * (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4))) := by
  obtain ⟨A, hA1, hA⟩ := norm_tr_le_sourceGaussian f
  obtain ⟨B, D, hB, hD, hb⟩ := exists_explicitThetaSource_logarithmic_error_bound f j
  let F := ((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2) * (4 * Real.pi * finiteThetaPotentialConstant)
  have hF : 0 ≤ F := mul_nonneg (by positivity)
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) finiteThetaPotentialConstant_nonneg)
  refine ⟨F + B, D, add_nonneg hF hB, hD, ?_⟩
  intro n hn L τ hτ hL
  have hτ' : |τ| ≤ (n : ℝ) := by
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    linarith only [hτ, hn0]
  have hfinite := finiteThetaSourceReading_error_le_window f
    (by linarith only [hA1]) hA j hn L τ hτ' hL
  have htheta := hb n hn L τ hτ hL
  have htriangle := dist_triangle
    (finiteThetaSourceMomentReading (sourceTwist τ f) L j n)
    (explicitThetaSourceMomentReading (sourceTwist τ f) L j n)
    (∑' ρ : zetaZeroConfig.carrier,
      zetaWeight (sourceTwist τ f) ρ * depthKernel L (zetaDepth ρ) ^ j)
  simp only [Real.dist_eq, explicitThetaSourceMomentReading_eq_source,
    finiteThetaSourceMomentReading] at htriangle htheta ⊢
  dsimp only [F]
  nlinarith only [hfinite, htheta, htriangle]

/-- The full collided form is computed by positive finite integer theta readings. -/
theorem finiteThetaSource_uniform_moving_collided (f : CompactTest) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ τ : ℝ,
      |τ| ≤ (n : ℝ) / 2 →
        |finiteThetaSourceMomentReading (sourceTwist τ f) 0 0 n -
          collidedForm zetaZeroConfig (twist τ f.1)| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := finiteThetaSource_uniform_moving_moments f 0 ε hε
  refine ⟨N, fun n hn τ hτ => ?_⟩
  have hwindow : ((0 : ℕ) : ℝ) * |(0 : ℝ)| ≤ 2 * Real.log ((n : ℝ) + 1) := by
    rw [Nat.cast_zero, zero_mul]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by
      have h := Nat.cast_nonneg (α := ℝ) n
      linarith only [h]))
  simpa only [pow_zero, mul_one, zetaWeight, collidedForm, sourceTwist] using
    hN n hn 0 τ hτ hwindow

/-- The same finite readings compute the Hecke defect at logarithmic translation scales. -/
theorem finiteThetaSource_uniform_moving_heckeDefect (f : CompactTest) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ L τ : ℝ,
      |τ| ≤ (n : ℝ) / 2 → |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
        |finiteThetaSourceMomentReading (sourceTwist τ f) L 1 n -
          heckeDefect (sourceTwist τ f) L| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := finiteThetaSource_uniform_moving_moments f 1 ε hε
  refine ⟨N, fun n hn L τ hτ hL => ?_⟩
  have hwindow : ((1 : ℕ) : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) := by
    simpa only [Nat.cast_one, one_mul] using hL
  simpa only [pow_one, heckeDefect] using hN n hn L τ hτ hwindow

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.finiteThetaSource_uniform_moving_moments
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_finiteThetaSource_logarithmic_error_bound
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.finiteThetaSource_uniform_moving_collided
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.finiteThetaSource_uniform_moving_heckeDefect
