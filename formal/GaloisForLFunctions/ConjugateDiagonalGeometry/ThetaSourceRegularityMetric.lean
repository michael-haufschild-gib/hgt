import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceRegularityWindow
import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceRegularityTail
import GaloisForLFunctions.ConjugateDiagonalGeometry.ThetaSourceMetric
import GaloisForLFunctions.ConjugateDiagonalGeometry.MovingSourceMetric

/-!
# Common theta readings on regularity-dependent logarithmic windows

The same arithmetic source schedule recovers normalized moments throughout
the closed window paid by the test's regularity. Smooth compact tests permit
every fixed logarithmic aperture and every fixed moment order.
-/

open Complex MeasureTheory Filter Set Metric
open scoped Topology ContDiff
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization _root_.RHTower

private lemma exists_regularity_source_radius (f : CompactTest) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ u, f.1 u ≠ 0 → |u| ≤ a := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp
    f.2.2.isCompact.isBounded
  refine ⟨|r|, abs_nonneg r, fun u hu => ?_⟩
  have h : u ∈ closedBall (0 : ℝ) r := hr (subset_tsupport _ hu)
  have h' : |u| ≤ r := by simpa only [mem_closedBall, Real.dist_eq, sub_zero] using h
  exact h'.trans (le_abs_self r)

/-- One stage works for all normalized moments in the closed regularity aperture. -/
theorem thetaSource_uniform_regularity_moments (f : CompactTest) (k : ℕ)
    (hreg : ContDiff ℝ (k + 2) f.1) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ (j : ℕ) (L τ : ℝ),
      |τ| ≤ (n : ℝ) / 2 →
      (j : ℝ) * |L| ≤ ((2 * k + 2 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) →
      |thetaSourceMomentReading (sourceTwist τ f) L j n -
        ∑' ρ : zetaZeroConfig.carrier,
          zetaWeight (sourceTwist τ f) ρ * depthKernel L (zetaDepth ρ) ^ j| / 4 ^ j < ε := by
  obtain ⟨A, hA1, hbound⟩ := norm_tr_le_sourceGaussian f
  obtain ⟨a, ha, hsupp⟩ := exists_regularity_source_radius f
  let C : ℝ := sourceRegularityTailConstant f k a
  have hC : 0 ≤ C := sourceRegularityTailConstant_nonneg f k a
  have ht : Tendsto (fun n : ℕ =>
      sourceRegularityWindowError A ((2 * k + 2 : ℕ) : ℝ) n + C * sourceReferenceTail n)
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_sourceRegularityWindowError A ((2 * k + 2 : ℕ) : ℝ)).add
        (tendsto_sourceReferenceTail.const_mul C)
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht ε hε
  refine ⟨N, fun n hn j L τ hτ hL => ?_⟩
  have hnonneg : 0 ≤ sourceRegularityWindowError A ((2 * k + 2 : ℕ) : ℝ) n +
      C * sourceReferenceTail n :=
    add_nonneg (sourceRegularityWindowError_nonneg _ _ _)
      (mul_nonneg hC (sourceReferenceTail_nonneg n))
  have hsmall := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hsmall
  have hτ' : |τ| ≤ (n : ℝ) := by
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    linarith only [hτ, hn0]
  have hsource := sourceMomentCurrentError_le_regularity_window f
    (by linarith only [hA1]) hbound (Nat.cast_nonneg (2 * k + 2)) j n L τ hτ' hL
  rw [xiCurrentPairing_eq_trace
    (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)
    ((sourceCutoff n).contDiff.mul (contDiff_sourceDepthKernel (sourceTwist τ f) L j))
    (sourceCutoff n).hasCompactSupport.mul_right] at hsource
  have htail := source_regularity_moving_trace_tail_le f k hreg ha hsupp j n L τ hτ hL
  have htail' :
      |zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j) -
        zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)| ≤
      4 ^ j * (C * sourceReferenceTail n) := by
    refine htail.trans ?_
    have hp : (2 : ℝ) ^ j ≤ 4 ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
    have hm := mul_le_mul_of_nonneg_right hp (mul_nonneg hC (sourceReferenceTail_nonneg n))
    change (C * 2 ^ j) * sourceReferenceTail n ≤ _
    nlinarith only [hm]
  have htriangle := dist_triangle
    (commonSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n)
    (zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z))
    (zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j))
  simp only [Real.dist_eq] at htriangle
  rw [abs_sub_comm
    (zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z))
    (zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j))] at htriangle
  have htotal :
      |commonSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n -
        zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j)| ≤
      4 ^ j * (sourceRegularityWindowError A ((2 * k + 2 : ℕ) : ℝ) n +
        C * sourceReferenceTail n) :=
    (htriangle.trans (add_le_add hsource htail')).trans_eq (by ring)
  rw [thetaSourceMomentReading_eq_common, ← zetaSourceTrace_depthKernel_eq]
  refine (show _ ≤ sourceRegularityWindowError A ((2 * k + 2 : ℕ) : ℝ) n +
    C * sourceReferenceTail n from ?_).trans_lt hsmall
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ j)).2
  exact htotal.trans_eq (mul_comm _ _)

/-- Smooth tests admit every fixed logarithmic Hecke aperture along the same source schedule. -/
theorem thetaSource_uniform_smooth_log_windows (f : CompactTest)
    (hreg : ContDiff ℝ ∞ f.1) (j : ℕ) (c : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ L τ : ℝ,
      |τ| ≤ (n : ℝ) / 2 → |L| ≤ c * Real.log ((n : ℝ) + 1) →
      |thetaSourceMomentReading (sourceTwist τ f) L j n -
        ∑' ρ : zetaZeroConfig.carrier,
          zetaWeight (sourceTwist τ f) ρ * depthKernel L (zetaDepth ρ) ^ j| < ε := by
  let k : ℕ := ⌈(j : ℝ) * c⌉₊
  have hk : (j : ℝ) * c ≤ ((2 * k + 2 : ℕ) : ℝ) := by
    have hceil : (j : ℝ) * c ≤ (k : ℝ) := Nat.le_ceil _
    exact hceil.trans (by exact_mod_cast (show k ≤ 2 * k + 2 by omega))
  have hfinite : ContDiff ℝ (k + 2) f.1 := hreg.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl (k + 2))
  intro ε hε
  obtain ⟨N, hN⟩ := thetaSource_uniform_regularity_moments f k hfinite
    (ε / 4 ^ j) (by positivity)
  refine ⟨N, fun n hn L τ hτ hL => ?_⟩
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hwindow : (j : ℝ) * |L| ≤
      ((2 * k + 2 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) := by
    calc
      (j : ℝ) * |L| ≤ (j : ℝ) * (c * Real.log ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg j)
      _ = ((j : ℝ) * c) * Real.log ((n : ℝ) + 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hk hlog
  have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 ^ j)).mp (hN n hn j L τ hτ hwindow)
  refine h.trans_eq ?_
  field_simp [show (4 : ℝ) ^ j ≠ 0 by positivity]

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.thetaSource_uniform_regularity_moments
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.thetaSource_uniform_smooth_log_windows
