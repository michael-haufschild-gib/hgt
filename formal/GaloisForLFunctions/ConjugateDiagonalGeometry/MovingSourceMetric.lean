import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceWindowError
import GaloisForLFunctions.ConjugateDiagonalGeometry.MovingSourceTail

/-!
# Simultaneous source evaluation of moving collided moments

The positive arithmetic source approximates the full actual divisor trace
uniformly in a linearly expanding ordinate window and a logarithmic Hecke
window. Local current error and omitted divisor mass are controlled separately
by proved vanishing bounds.
-/

open Complex Filter Set Metric
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization

theorem zetaSourceTrace_depthKernel_eq (f : CompactTest) (L : ℝ) (j : ℕ) :
    zetaSourceTrace (sourceDepthKernel f L j) =
      ∑' ρ : zetaZeroConfig.carrier, zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ j := by
  apply tsum_congr
  intro ρ
  dsimp only [sourceDepthKernel, zetaWeight, zetaDepth]
  ring

/-- One arithmetic regulator recovers the full moving trace throughout the joint C² window. -/
theorem commonSourceReading_uniform_moving_moments (f : CompactTest) (j : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ L τ : ℝ,
      |τ| ≤ (n : ℝ) / 2 → (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
        |commonSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n -
          zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j)| < ε := by
  intro ε hε
  obtain ⟨Ns, hs⟩ := commonSourceReading_uniform_cutoff_current f j (ε / 2) (by positivity)
  obtain ⟨Nt, ht⟩ := uniform_moving_depth_trace_tail f j (ε / 2) (by positivity)
  refine ⟨max Ns Nt, fun n hn L τ hτ hL => ?_⟩
  have hτ' : |τ| ≤ (n : ℝ) := by
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    linarith only [hτ, hn0]
  have hsource := hs n ((le_max_left _ _).trans hn) L τ hτ' hL
  have htail := ht n ((le_max_right _ _).trans hn) L τ hτ hL
  have hcurrent := xiCurrentPairing_eq_trace
    (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)
    ((sourceCutoff n).contDiff.mul (contDiff_sourceDepthKernel (sourceTwist τ f) L j))
    (sourceCutoff n).hasCompactSupport.mul_right
  rw [hcurrent] at hsource
  have htriangle := dist_triangle
    (commonSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n)
    (zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z))
    (zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j))
  simp only [Real.dist_eq] at htriangle
  rw [abs_sub_comm
    (zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z))
    (zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j))] at htriangle
  linarith only [hsource, htail, htriangle]

end GaloisForLFunctions.ConjugateDiagonalGeometry
