import GaloisForLFunctions.ConjugateDiagonalGeometry.StripSourceCutoff
import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceApertureMovingTail

/-!
# Omitted trace for the fixed-strip exhaustion

Every actual zero omitted by the stretched cutoff is already outside the
radial cutoff. Its entire trace tail is therefore paid by the existing
arithmetic reference tail, uniformly over the joint source aperture.
-/

open Complex Set Metric
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization _root_.RHTower

/-- A zero not fully retained by the strip cutoff lies outside the old radial support. -/
lemma sourceCutoff_eq_zero_of_stripSourceCutoff_ne_one (n : ℕ)
    (ρ : zetaZeroConfig.carrier) (hχ : stripSourceCutoff n ρ ≠ 1) : sourceCutoff n ρ = 0 := by
  by_contra hne
  have hs := subset_tsupport _ hne
  rw [(sourceCutoff n).tsupport_eq, mem_closedBall, dist_zero_right] at hs
  apply hχ
  exact stripSourceCutoff_eq_one_of_strip_im_le n (zetaZeroConfig.strip ρ ρ.2)
    ((Complex.abs_im_le_norm _).trans hs)

/-- The stretched exhaustion inherits the old uniform arithmetic trace tail. -/
theorem stripSource_aperture_moving_trace_tail_le (f : CompactTest) {a : ℝ} (ha : 0 ≤ a)
    (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ a) (j n : ℕ) (L τ : ℝ)
    (hτ : |τ| ≤ (n : ℝ) / 2)
    (hwindow : a + (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1)) :
    |zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j) -
      zetaSourceTrace (fun z => stripSourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)| ≤
      (sourceTestSize f ^ 2 * (40 * 2 ^ j)) * sourceReferenceTail n := by
  let C := sourceTestSize f ^ 2 * (40 * 2 ^ j)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hφ (z : ℂ) : 0 ≤ sourceDepthKernel (sourceTwist τ f) L j z :=
    mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg (depthKernel_nonneg _ _) _)
  have hs : Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * sourceDepthKernel (sourceTwist τ f) L j ρ) := by
    simpa only [sourceDepthKernel, zetaWeight, zetaDepth, mul_assoc] using
      summable_zeta_kernel_pow (sourceTwist τ f) L j
  have hχs : Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) *
        (stripSourceCutoff n ρ * sourceDepthKernel (sourceTwist τ f) L j ρ)) := by
    refine Summable.of_nonneg_of_le
      (fun ρ => mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (stripSourceCutoff_nonneg n ρ) (hφ ρ)))
      (fun ρ => ?_) hs
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (hφ ρ) (stripSourceCutoff_le_one n ρ)) (Nat.cast_nonneg _)
  have hp (ρ : zetaZeroConfig.carrier) :
      (1 - stripSourceCutoff n ρ) *
        ((zetaZeroConfig.mult ρ : ℝ) * sourceDepthKernel (sourceTwist τ f) L j ρ) ≤
      C * ((1 - sourceCutoff n ρ) *
        ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) := by
    by_cases hχ : stripSourceCutoff n ρ = 1
    · rw [hχ, sub_self, zero_mul]
      exact mul_nonneg hC
        (mul_nonneg (sub_nonneg.mpr (sourceCutoff n).le_one)
          (div_nonneg (Nat.cast_nonneg _)
            (add_nonneg zero_le_one (Complex.normSq_nonneg _))))
    have hold := sourceCutoff_eq_zero_of_stripSourceCutoff_ne_one n ρ hχ
    have holdne : sourceCutoff n ρ ≠ 1 := by rw [hold]; norm_num
    have hb := sourceDepthKernel_aperture_moving_tail_le f ha hsupp j n L τ hτ hwindow ρ holdne
    rw [hold, sub_zero, one_mul]
    calc
      (1 - stripSourceCutoff n ρ) *
          ((zetaZeroConfig.mult ρ : ℝ) * sourceDepthKernel (sourceTwist τ f) L j ρ) ≤
        (zetaZeroConfig.mult ρ : ℝ) * sourceDepthKernel (sourceTwist τ f) L j ρ :=
          mul_le_of_le_one_left (mul_nonneg (Nat.cast_nonneg _) (hφ ρ))
            (by linarith only [stripSourceCutoff_nonneg n ρ])
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (C / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
        mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = _ := by ring
  have ht0 (ρ : zetaZeroConfig.carrier) : 0 ≤ (1 - stripSourceCutoff n ρ) *
      ((zetaZeroConfig.mult ρ : ℝ) * sourceDepthKernel (sourceTwist τ f) L j ρ) :=
    mul_nonneg (sub_nonneg.mpr (stripSourceCutoff_le_one n ρ))
      (mul_nonneg (Nat.cast_nonneg _) (hφ ρ))
  have hts := Summable.of_nonneg_of_le ht0 hp ((summable_sourceReferenceTail n).mul_left C)
  have he : zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j) -
      zetaSourceTrace (fun z => stripSourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z) =
      ∑' ρ : zetaZeroConfig.carrier, (1 - stripSourceCutoff n ρ) *
        ((zetaZeroConfig.mult ρ : ℝ) * sourceDepthKernel (sourceTwist τ f) L j ρ) := by
    rw [zetaSourceTrace, zetaSourceTrace, ← hs.tsum_sub hχs]
    apply tsum_congr
    intro ρ
    ring
  rw [he, abs_of_nonneg (tsum_nonneg ht0)]
  calc
    (∑' ρ : zetaZeroConfig.carrier, (1 - stripSourceCutoff n ρ) *
        ((zetaZeroConfig.mult ρ : ℝ) * sourceDepthKernel (sourceTwist τ f) L j ρ)) ≤
      ∑' ρ : zetaZeroConfig.carrier, C * ((1 - sourceCutoff n ρ) *
        ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
      hts.tsum_le_tsum hp ((summable_sourceReferenceTail n).mul_left C)
    _ = C * sourceReferenceTail n := tsum_mul_left

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.stripSource_aperture_moving_trace_tail_le
