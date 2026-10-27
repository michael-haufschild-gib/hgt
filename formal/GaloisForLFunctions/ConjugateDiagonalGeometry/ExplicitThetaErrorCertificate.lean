import GaloisForLFunctions.ConjugateDiagonalGeometry.ExplicitThetaSourceMetric
import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceReferenceTailArithmetic

/-!
# Arithmetic error certificates for positive theta trace readings

A quartic exponential controls the local current error. The omitted divisor
mass is bounded on the zero-free right half-plane by the arithmetic xi
logarithmic derivative, and hence by a logarithm-over-radius envelope.
-/

open Complex MeasureTheory Filter Set Metric
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization _root_.RHTower

/-- Both errors in a moving collided moment admit constants independent of the motions. -/
theorem exists_explicitThetaSource_moving_error_bound (f : CompactTest) (j : ℕ) :
    ∃ B D : ℝ, 0 ≤ B ∧ 0 ≤ D ∧ ∀ n : ℕ, 1 ≤ n → ∀ L τ : ℝ,
      |τ| ≤ (n : ℝ) / 2 → (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
      |explicitThetaSourceMomentReading (sourceTwist τ f) L j n -
        ∑' ρ : zetaZeroConfig.carrier,
          zetaWeight (sourceTwist τ f) ρ * depthKernel L (zetaDepth ρ) ^ j| ≤
      B * Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) + D * sourceReferenceTail n := by
  obtain ⟨A, hA1, hA⟩ := norm_tr_le_sourceGaussian f
  obtain ⟨C, hC, hlocal⟩ := exists_explicitSourceLocalError_bound
  obtain ⟨D, hD, htail⟩ := moving_depth_trace_tail_le f j
  refine ⟨(((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2) * (2 * Real.pi + 8 * C)),
    D, by positivity, hD, ?_⟩
  intro n hn L τ hτ hL
  have hτ' : |τ| ≤ (n : ℝ) := by
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    linarith only [hτ, hn0]
  have hsource := explicitSourceMomentCurrentError_le_window f
    (by linarith only [hA1]) hA hC.le j n L τ (hlocal n hn) hτ' hL
  have hcurrent := xiCurrentPairing_eq_trace
    (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)
    ((sourceCutoff n).contDiff.mul (contDiff_sourceDepthKernel (sourceTwist τ f) L j))
    (sourceCutoff n).hasCompactSupport.mul_right
  rw [hcurrent] at hsource
  have ht := htail n L τ hτ hL
  have htriangle := dist_triangle
    (explicitSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n)
    (zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z))
    (zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j))
  simp only [Real.dist_eq] at htriangle
  rw [abs_sub_comm
    (zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z))
    (zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j))] at htriangle
  rw [explicitThetaSourceMomentReading_eq_source, ← zetaSourceTrace_depthKernel_eq]
  exact htriangle.trans (add_le_add hsource ht)

/-- Right-half-plane xi data certify the error in the full positive theta reading. -/
theorem exists_explicitThetaSource_sourceLogDeriv_error_bound (f : CompactTest) (j : ℕ) :
    ∃ B D : ℝ, 0 ≤ B ∧ 0 ≤ D ∧ ∀ n : ℕ, 1 ≤ n → ∀ L τ : ℝ,
      |τ| ≤ (n : ℝ) / 2 → (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
      |explicitThetaSourceMomentReading (sourceTwist τ f) L j n -
        ∑' ρ : zetaZeroConfig.carrier,
          zetaWeight (sourceTwist τ f) ρ * depthKernel L (zetaDepth ρ) ^ j| ≤
      B * Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) +
        D * ((16 / (n : ℝ)) * (logDeriv xi (widthPoint (n : ℝ) 0)).re) := by
  obtain ⟨B, D, hB, hD, hb⟩ := exists_explicitThetaSource_moving_error_bound f j
  refine ⟨B, D, hB, hD, fun n hn L τ hτ hL => (hb n hn L τ hτ hL).trans ?_⟩
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (sourceReferenceTail_le_sourceLogDeriv hn) hD)

/-- An arithmetic logarithm-over-radius envelope certifies every moving theta moment. -/
theorem exists_explicitThetaSource_logarithmic_error_bound (f : CompactTest) (j : ℕ) :
    ∃ B D : ℝ, 0 ≤ B ∧ 0 ≤ D ∧ ∀ n : ℕ, 1 ≤ n → ∀ L τ : ℝ,
      |τ| ≤ (n : ℝ) / 2 → (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
      |explicitThetaSourceMomentReading (sourceTwist τ f) L j n -
        ∑' ρ : zetaZeroConfig.carrier,
          zetaWeight (sourceTwist τ f) ρ * depthKernel L (zetaDepth ρ) ^ j| ≤
      B * Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) +
        D * ((16 / (n : ℝ)) * (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4))) := by
  obtain ⟨B, D, hB, hD, hb⟩ := exists_explicitThetaSource_moving_error_bound f j
  refine ⟨B, D, hB, hD, fun n hn L τ hτ hL => (hb n hn L τ hτ hL).trans ?_⟩
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (sourceReferenceTail_le_log_div hn) hD)

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_explicitThetaSource_sourceLogDeriv_error_bound
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_explicitThetaSource_logarithmic_error_bound
