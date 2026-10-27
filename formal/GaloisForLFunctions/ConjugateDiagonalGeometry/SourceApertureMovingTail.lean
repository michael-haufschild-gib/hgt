import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceTestApertureBounds
import GaloisForLFunctions.ConjugateDiagonalGeometry.MovingSourceTail

/-!
# Moving tails with a shared physical and Hecke aperture

Fourth-order transform decay absorbs the combined exponential cost of
physical support and Hecke motion. The remaining divisor tail is uniform
in the test, with its explicit C² source size retained as a quadratic factor.
-/

open Complex Set Metric
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization _root_.RHTower

private theorem moving_source_tail_ratio_le (n : ℕ) (τ : ℝ)
    (hτ : |τ| ≤ (n : ℝ) / 2) (ρ : zetaZeroConfig.carrier)
    (hχ : sourceCutoff n ρ ≠ 1) :
    ((n : ℝ) + 1) ^ 2 / (1 + ((ρ : ℂ).im - τ) ^ 2) ^ 2 ≤
      40 / (1 + Complex.normSq (gammaOf (ρ : ℂ))) := by
  have hs := zetaZeroConfig.strip ρ ρ.2
  have hy : (n : ℝ) < |(ρ : ℂ).im| := by
    by_contra h
    exact hχ (sourceCutoff_eq_one_of_im_le n ρ (le_of_not_gt h))
  have hsep : |(ρ : ℂ).im| ≤ 2 * |(ρ : ℂ).im - τ| := by
    have h := abs_add_le ((ρ : ℂ).im - τ) τ
    rw [sub_add_cancel] at h
    linarith only [h, hτ, hy]
  have hysq : (ρ : ℂ).im ^ 2 ≤ 4 * ((ρ : ℂ).im - τ) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (ρ : ℂ).im) hsep 2
    norm_num only [mul_pow, sq_abs] at h
    exact h
  have hn2 : (n : ℝ) ^ 2 ≤ (ρ : ℂ).im ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (Nat.cast_nonneg n) hy.le 2
  have hN : ((n : ℝ) + 1) ^ 2 ≤ 8 * (1 + ((ρ : ℂ).im - τ) ^ 2) := by
    nlinarith only [hn2, hysq, sq_nonneg ((n : ℝ) - 1), sq_nonneg ((ρ : ℂ).im - τ)]
  have hre : (gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := by
    rw [gammaOf, Complex.div_I]
    simp
  have him : (gammaOf (ρ : ℂ)).im = -((ρ : ℂ).re - 1 / 2) := by
    rw [gammaOf, Complex.div_I]
    simp
  have hgamma : Complex.normSq (gammaOf (ρ : ℂ)) ≤ (ρ : ℂ).im ^ 2 + 1 / 4 := by
    rw [Complex.normSq_apply, hre, him]
    nlinarith only [mul_nonneg hs.1 (sub_nonneg.mpr hs.2)]
  have hQ : 1 + Complex.normSq (gammaOf (ρ : ℂ)) ≤
      5 * (1 + ((ρ : ℂ).im - τ) ^ 2) := by
    nlinarith only [hgamma, hysq, sq_nonneg ((ρ : ℂ).im - τ)]
  have hQpos : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) :=
    add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg _)
  apply (div_le_div_iff₀ (by positivity) hQpos).2
  calc
    ((n : ℝ) + 1) ^ 2 * (1 + Complex.normSq (gammaOf (ρ : ℂ))) ≤
        (8 * (1 + ((ρ : ℂ).im - τ) ^ 2)) *
          (5 * (1 + ((ρ : ℂ).im - τ) ^ 2)) :=
      mul_le_mul hN hQ hQpos.le (by positivity)
    _ = _ := by ring

/-- Physical support and Hecke motion share one logarithmic tail allowance. -/
theorem sourceDepthKernel_aperture_moving_tail_le (f : CompactTest) {a : ℝ} (ha : 0 ≤ a)
    (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ a) (j n : ℕ) (L τ : ℝ)
    (hτ : |τ| ≤ (n : ℝ) / 2)
    (hwindow : a + (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1))
    (ρ : zetaZeroConfig.carrier) (hχ : sourceCutoff n ρ ≠ 1) :
    sourceDepthKernel (sourceTwist τ f) L j ρ ≤
      (sourceTestSize f ^ 2 * (40 * 2 ^ j)) /
        (1 + Complex.normSq (gammaOf (ρ : ℂ))) := by
  have hre : ((ρ : ℂ) - (τ : ℂ) * Complex.I).re = (ρ : ℂ).re := by simp
  have him : ((ρ : ℂ) - (τ : ℂ) * Complex.I).im = (ρ : ℂ).im - τ := by simp
  have hs : 0 ≤ ((ρ : ℂ) - (τ : ℂ) * Complex.I).re ∧
      ((ρ : ℂ) - (τ : ℂ) * Complex.I).re ≤ 1 := by
    simpa only [hre] using zetaZeroConfig.strip ρ ρ.2
  have hw := normSq_tr_strip_le_sourceTestSize f ha hsupp hs
  rw [him] at hw
  have hk : depthKernel L (zetaDepth ρ) ^ j ≤ 2 ^ j * Real.exp ((j : ℝ) * |L|) := by
    calc
      depthKernel L (zetaDepth ρ) ^ j ≤ (2 * Real.exp |L|) ^ j :=
        pow_le_pow_left₀ (depthKernel_nonneg _ _) (depthKernel_zeta_le_exp L ρ) j
      _ = _ := by rw [mul_pow, Real.exp_nat_mul]
  have he : Real.exp a * Real.exp ((j : ℝ) * |L|) ≤ ((n : ℝ) + 1) ^ 2 := by
    rw [← Real.exp_add]
    refine (Real.exp_le_exp.mpr hwindow).trans_eq ?_
    have h := Real.exp_nat_mul (Real.log ((n : ℝ) + 1)) 2
    norm_num only [Nat.cast_ofNat] at h
    rw [h, Real.exp_log (by positivity)]
  dsimp only [sourceDepthKernel, sourceTwist]
  rw [tr_twist]
  change Complex.normSq (tr f.1 ((ρ : ℂ) - (τ : ℂ) * Complex.I)) *
    depthKernel L (zetaDepth ρ) ^ j ≤ _
  calc
    Complex.normSq (tr f.1 ((ρ : ℂ) - (τ : ℂ) * Complex.I)) *
        depthKernel L (zetaDepth ρ) ^ j ≤
      (sourceTestSize f ^ 2 * Real.exp a / (1 + ((ρ : ℂ).im - τ) ^ 2) ^ 2) *
        (2 ^ j * Real.exp ((j : ℝ) * |L|)) :=
      mul_le_mul hw hk (pow_nonneg (depthKernel_nonneg _ _) _) (by positivity)
    _ = (sourceTestSize f ^ 2 * 2 ^ j) *
        ((Real.exp a * Real.exp ((j : ℝ) * |L|)) / (1 + ((ρ : ℂ).im - τ) ^ 2) ^ 2) := by ring
    _ ≤ (sourceTestSize f ^ 2 * 2 ^ j) *
        (((n : ℝ) + 1) ^ 2 / (1 + ((ρ : ℂ).im - τ) ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right he (sq_nonneg _)) (by positivity)
    _ ≤ (sourceTestSize f ^ 2 * 2 ^ j) *
        (40 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
      mul_le_mul_of_nonneg_left (moving_source_tail_ratio_le n τ hτ ρ hχ) (by positivity)
    _ = _ := by ring

/-- The full omitted trace has an explicit bound uniform in both test and moment order. -/
theorem sourceAperture_moving_trace_tail_le (f : CompactTest) {a : ℝ} (ha : 0 ≤ a)
    (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ a) (j n : ℕ) (L τ : ℝ)
    (hτ : |τ| ≤ (n : ℝ) / 2)
    (hwindow : a + (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1)) :
    |zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j) -
      zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)| ≤
      (sourceTestSize f ^ 2 * (40 * 2 ^ j)) * sourceReferenceTail n := by
  let C := sourceTestSize f ^ 2 * (40 * 2 ^ j)
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
    have hb := sourceDepthKernel_aperture_moving_tail_le f ha hsupp j n L τ hτ hwindow ρ hχ
    calc
      (1 - sourceCutoff n ρ) *
          ((zetaZeroConfig.mult ρ : ℝ) * sourceDepthKernel (sourceTwist τ f) L j ρ) ≤
        (1 - sourceCutoff n ρ) * ((zetaZeroConfig.mult ρ : ℝ) *
          (C / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
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

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.sourceAperture_moving_trace_tail_le
