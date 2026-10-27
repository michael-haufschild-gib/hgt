import GaloisForLFunctions.ConjugateDiagonalGeometry.MovingSourceTailControl
import GaloisForLFunctions.ConjugateDiagonalGeometry.CommonSourceRegulator

/-!
# A common summable tail for moving arithmetic moments

The omitted part of the actual xi reference density tends to zero. Every
allowed moving source moment is bounded by one fixed multiple of this tail,
including the boundary of the logarithmic translation window.
-/

open Complex Filter Set Metric
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization _root_.RHTower

/-- The omitted part of the fixed summable xi reference density. -/
def sourceReferenceTail (n : ℕ) : ℝ :=
  ∑' ρ : zetaZeroConfig.carrier,
    (1 - sourceCutoff n ρ) *
      ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))))

private theorem sourceReferenceTerm_nonneg (ρ : zetaZeroConfig.carrier) :
    0 ≤ (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))) :=
  div_nonneg (Nat.cast_nonneg _) (add_nonneg zero_le_one (Complex.normSq_nonneg _))

private theorem sourceReferenceTailTerm_nonneg (n : ℕ) (ρ : zetaZeroConfig.carrier) :
    0 ≤ (1 - sourceCutoff n ρ) *
      ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
  mul_nonneg (sub_nonneg.mpr (sourceCutoff n).le_one) (sourceReferenceTerm_nonneg ρ)

private theorem sourceReferenceTailTerm_le (n : ℕ) (ρ : zetaZeroConfig.carrier) :
    (1 - sourceCutoff n ρ) *
      ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) ≤
        (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))) :=
  mul_le_of_le_one_left (sourceReferenceTerm_nonneg ρ)
    (by
      have hcut : 0 ≤ sourceCutoff n ρ := (sourceCutoff n).nonneg
      linarith only [hcut])

theorem summable_sourceReferenceTail (n : ℕ) :
    Summable (fun ρ : zetaZeroConfig.carrier => (1 - sourceCutoff n ρ) *
      ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
  Summable.of_nonneg_of_le (sourceReferenceTailTerm_nonneg n)
    (sourceReferenceTailTerm_le n) summable_zetaZeroConfig

theorem sourceReferenceTail_nonneg (n : ℕ) : 0 ≤ sourceReferenceTail n :=
  tsum_nonneg (sourceReferenceTailTerm_nonneg n)

/-- The reference tail vanishes without any quantitative zero-counting premise. -/
theorem tendsto_sourceReferenceTail : Tendsto sourceReferenceTail atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    (f := fun n (ρ : zetaZeroConfig.carrier) => (1 - sourceCutoff n ρ) *
      ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))))
    (g := fun _ => (0 : ℝ))
    (bound := fun ρ => (zetaZeroConfig.mult ρ : ℝ) /
      (1 + Complex.normSq (gammaOf (ρ : ℂ)))) summable_zetaZeroConfig
    (fun ρ => tendsto_const_nhds.congr' ((sourceCutoff_eventually_one ρ).mono
      fun n hn => by dsimp only; rw [hn, sub_self, zero_mul]))
    (Eventually.of_forall fun n ρ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sourceReferenceTailTerm_nonneg n ρ)]
      exact sourceReferenceTailTerm_le n ρ)
  change Tendsto (fun n : ℕ => ∑' ρ : zetaZeroConfig.carrier,
    (1 - sourceCutoff n ρ) *
      ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) atTop (𝓝 0)
  simpa only [tsum_zero] using h

/-- One vanishing reference tail bounds every omitted moment in the joint moving window. -/
theorem moving_depth_trace_tail_le (f : CompactTest) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ L τ : ℝ,
      |τ| ≤ (n : ℝ) / 2 → (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
        |zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j) -
          zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)| ≤
            C * sourceReferenceTail n := by
  obtain ⟨C, hC, hb⟩ := sourceDepthKernel_moving_tail_bound f j
  refine ⟨C, hC, fun n L τ hτ hL => ?_⟩
  have hφ (z : ℂ) : 0 ≤ sourceDepthKernel (sourceTwist τ f) L j z :=
    mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg (depthKernel_nonneg _ _) _)
  have hs : Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * sourceDepthKernel (sourceTwist τ f) L j ρ) := by
    simpa only [sourceDepthKernel, zetaWeight, zetaDepth, mul_assoc] using
      summable_zeta_kernel_pow (sourceTwist τ f) L j
  have hχs : Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) *
        (sourceCutoff n ρ * sourceDepthKernel (sourceTwist τ f) L j ρ)) := by
    refine Summable.of_nonneg_of_le
      (fun ρ => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (sourceCutoff n).nonneg (hφ ρ)))
      (fun ρ => ?_) hs
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (hφ ρ) (sourceCutoff n).le_one) (Nat.cast_nonneg _)
  have hp (ρ : zetaZeroConfig.carrier) :
      (1 - sourceCutoff n ρ) *
        ((zetaZeroConfig.mult ρ : ℝ) * sourceDepthKernel (sourceTwist τ f) L j ρ) ≤
      C * ((1 - sourceCutoff n ρ) *
        ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) := by
    by_cases hχ : sourceCutoff n ρ = 1
    · simp only [hχ, sub_self, zero_mul, mul_zero, le_refl]
    calc
      (1 - sourceCutoff n ρ) *
          ((zetaZeroConfig.mult ρ : ℝ) * sourceDepthKernel (sourceTwist τ f) L j ρ) ≤
          (1 - sourceCutoff n ρ) * ((zetaZeroConfig.mult ρ : ℝ) *
            (C / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hb n L τ hτ hL ρ hχ) (Nat.cast_nonneg _))
          (sub_nonneg.mpr (sourceCutoff n).le_one)
      _ = _ := by ring
  have ht0 (ρ : zetaZeroConfig.carrier) : 0 ≤ (1 - sourceCutoff n ρ) *
      ((zetaZeroConfig.mult ρ : ℝ) * sourceDepthKernel (sourceTwist τ f) L j ρ) :=
    mul_nonneg (sub_nonneg.mpr (sourceCutoff n).le_one)
      (mul_nonneg (Nat.cast_nonneg _) (hφ ρ))
  have hts := Summable.of_nonneg_of_le ht0 hp ((summable_sourceReferenceTail n).mul_left C)
  have he : zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j) -
      zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z) =
      ∑' ρ : zetaZeroConfig.carrier, (1 - sourceCutoff n ρ) *
        ((zetaZeroConfig.mult ρ : ℝ) * sourceDepthKernel (sourceTwist τ f) L j ρ) := by
    rw [zetaSourceTrace, zetaSourceTrace, ← hs.tsum_sub hχs]
    apply tsum_congr
    intro ρ
    ring
  rw [he, abs_of_nonneg (tsum_nonneg ht0)]
  calc
    (∑' ρ : zetaZeroConfig.carrier, (1 - sourceCutoff n ρ) *
        ((zetaZeroConfig.mult ρ : ℝ) * sourceDepthKernel (sourceTwist τ f) L j ρ)) ≤
        ∑' ρ : zetaZeroConfig.carrier, C * ((1 - sourceCutoff n ρ) *
          ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
      hts.tsum_le_tsum hp ((summable_sourceReferenceTail n).mul_left C)
    _ = C * sourceReferenceTail n := tsum_mul_left

/-- Uniform removal of the divisor cutoff for the full C² source-test space. -/
theorem uniform_moving_depth_trace_tail (f : CompactTest) (j : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ L τ : ℝ,
      |τ| ≤ (n : ℝ) / 2 → (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
        |zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j) -
          zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)| < ε := by
  obtain ⟨C, hC, hb⟩ := moving_depth_trace_tail_le f j
  have ht : Tendsto (fun n => C * sourceReferenceTail n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_sourceReferenceTail.const_mul C
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht ε hε
  refine ⟨N, fun n hn L τ hτ hL => ?_⟩
  have hsmall : C * sourceReferenceTail n < ε := by
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (mul_nonneg hC (sourceReferenceTail_nonneg n))] using hN n hn
  exact (hb n L τ hτ hL).trans_lt hsmall

end GaloisForLFunctions.ConjugateDiagonalGeometry
