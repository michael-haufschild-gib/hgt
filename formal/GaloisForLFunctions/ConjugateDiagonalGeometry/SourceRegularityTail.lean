import GaloisForLFunctions.ConjugateDiagonalGeometry.MovingSourceTail
import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceTestApertureBounds
import GaloisForLFunctions.RHTower.ImaginaryShiftQuadraticFourierDefect

/-!
# Regularity pays the logarithmic tail aperture

For a compact test with r derivatives, squared transform decay pays the
closed joint window of width (2r-2) log(n+1). The remaining tail is a fixed
multiple of the actual summable xi reference density.
-/

open Complex MeasureTheory Set Metric
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization _root_.RHTower

/-- Actual L¹ source size at a specified derivative order. -/
def sourceRegularitySize (f : CompactTest) (r : ℕ) : ℝ :=
  2 ^ r * ((∫ u, ‖f.1 u‖) + ∫ u, ‖iteratedDeriv r f.1 u‖)

lemma sourceRegularitySize_nonneg (f : CompactTest) (r : ℕ) :
    0 ≤ sourceRegularitySize f r := by
  unfold sourceRegularitySize
  exact mul_nonneg (by positivity)
    (add_nonneg (integral_nonneg fun _ => norm_nonneg _)
      (integral_nonneg fun _ => norm_nonneg _))

/-- Higher derivatives give the corresponding vertical transform decay. -/
lemma norm_tr_le_sourceRegularitySize (f : CompactTest) (r : ℕ)
    (hreg : ContDiff ℝ r f.1) {a : ℝ}
    (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ a) (z : ℂ) :
    ‖tr f.1 z‖ ≤ Real.exp (|z.re - 1 / 2| * a) * sourceRegularitySize f r /
      (1 + |z.im|) ^ r := by
  have hre : (gammaOf z).re = z.im := by
    rw [gammaOf, Complex.div_I]
    simp
  have him : |(gammaOf z).im| = |z.re - 1 / 2| := by
    rw [gammaOf, Complex.div_I]
    simp only [Complex.neg_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.I_re, Complex.I_im]
    norm_num
    exact abs_sub_comm _ _
  apply (le_div_iff₀ (by positivity : 0 < (1 + |z.im|) ^ r)).2
  calc
    ‖tr f.1 z‖ * (1 + |z.im|) ^ r ≤
        2 ^ r * Real.exp (|z.re - 1 / 2| * a) *
          ((∫ u, ‖f.1 u‖) + ∫ u, ‖iteratedDeriv r f.1 u‖) := by
      simpa only [tr, hre, him] using norm_paperFT_mul_one_add_pow_le hreg hsupp (gammaOf z)
    _ = _ := by unfold sourceRegularitySize; ring

/-- On the zero strip, squared order-r decay has only the physical aperture cost. -/
lemma normSq_tr_strip_le_sourceRegularitySize (f : CompactTest) (r : ℕ)
    (hreg : ContDiff ℝ r f.1) {a : ℝ} (ha : 0 ≤ a)
    (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ a) {z : ℂ} (hz : 0 ≤ z.re ∧ z.re ≤ 1) :
    Complex.normSq (tr f.1 z) ≤
      sourceRegularitySize f r ^ 2 * Real.exp a / (1 + |z.im|) ^ (2 * r) := by
  have hδ : |z.re - 1 / 2| ≤ (1 / 2 : ℝ) :=
    abs_le.mpr ⟨by linarith only [hz.1], by linarith only [hz.2]⟩
  have hnorm : ‖tr f.1 z‖ ≤
      Real.exp (a / 2) * sourceRegularitySize f r / (1 + |z.im|) ^ r := by
    refine (norm_tr_le_sourceRegularitySize f r hreg hsupp z).trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (sourceRegularitySize_nonneg f r)
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hδ ha
    linarith only [h]
  have he : Real.exp (a / 2) ^ 2 = Real.exp a := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [Complex.normSq_eq_norm_sq]
  refine (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans_eq ?_
  rw [div_pow, mul_pow, he, ← pow_mul, Nat.mul_comm r 2]
  ring

private lemma regularity_moving_tail_ratio_le (q n : ℕ) (τ : ℝ)
    (hτ : |τ| ≤ (n : ℝ) / 2) (ρ : zetaZeroConfig.carrier)
    (hχ : sourceCutoff n ρ ≠ 1) :
    ((n : ℝ) + 1) ^ q / (1 + |(ρ : ℂ).im - τ|) ^ (q + 2) ≤
      (5 * 2 ^ q) / (1 + Complex.normSq (gammaOf (ρ : ℂ))) := by
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
      5 * (1 + |(ρ : ℂ).im - τ|) ^ 2 := by
    nlinarith only [hgamma, hysq, abs_nonneg ((ρ : ℂ).im - τ), sq_abs ((ρ : ℂ).im - τ)]
  have hQpos : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) :=
    add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg _)
  have hN : (n : ℝ) + 1 ≤ 2 * (1 + |(ρ : ℂ).im - τ|) := by
    linarith only [hy, hsep]
  have hp : ((n : ℝ) + 1) ^ q ≤ 2 ^ q * (1 + |(ρ : ℂ).im - τ|) ^ q := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hN q
  apply (div_le_div_iff₀ (by positivity) hQpos).2
  calc
    ((n : ℝ) + 1) ^ q * (1 + Complex.normSq (gammaOf (ρ : ℂ))) ≤
        (2 ^ q * (1 + |(ρ : ℂ).im - τ|) ^ q) *
          (5 * (1 + |(ρ : ℂ).im - τ|) ^ 2) :=
      mul_le_mul hp hQ hQpos.le (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- Actual source constant for the closed regularity aperture. -/
def sourceRegularityTailConstant (f : CompactTest) (k : ℕ) (a : ℝ) : ℝ :=
  5 * 2 ^ (2 * k + 2) * sourceRegularitySize f (k + 2) ^ 2 * Real.exp a

lemma sourceRegularityTailConstant_nonneg (f : CompactTest) (k : ℕ) (a : ℝ) :
    0 ≤ sourceRegularityTailConstant f k a := by
  unfold sourceRegularityTailConstant
  positivity

/-- Order k+2 regularity pays the closed aperture (2k+2) log(n+1). -/
theorem sourceDepthKernel_regularity_tail_le (f : CompactTest) (k : ℕ)
    (hreg : ContDiff ℝ (k + 2) f.1) {a : ℝ} (ha : 0 ≤ a)
    (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ a) (j n : ℕ) (L τ : ℝ)
    (hτ : |τ| ≤ (n : ℝ) / 2)
    (hwindow : (j : ℝ) * |L| ≤ ((2 * k + 2 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1))
    (ρ : zetaZeroConfig.carrier) (hχ : sourceCutoff n ρ ≠ 1) :
    sourceDepthKernel (sourceTwist τ f) L j ρ ≤
      (sourceRegularityTailConstant f k a * 2 ^ j) /
        (1 + Complex.normSq (gammaOf (ρ : ℂ))) := by
  have hre : ((ρ : ℂ) - (τ : ℂ) * Complex.I).re = (ρ : ℂ).re := by simp
  have him : ((ρ : ℂ) - (τ : ℂ) * Complex.I).im = (ρ : ℂ).im - τ := by simp
  have hs : 0 ≤ ((ρ : ℂ) - (τ : ℂ) * Complex.I).re ∧
      ((ρ : ℂ) - (τ : ℂ) * Complex.I).re ≤ 1 := by
    simpa only [hre] using zetaZeroConfig.strip ρ ρ.2
  have hw := normSq_tr_strip_le_sourceRegularitySize f (k + 2) hreg ha hsupp hs
  rw [him, show 2 * (k + 2) = (2 * k + 2) + 2 by omega] at hw
  have hexp : Real.exp ((j : ℝ) * |L|) ≤ ((n : ℝ) + 1) ^ (2 * k + 2) := by
    refine (Real.exp_le_exp.mpr hwindow).trans_eq ?_
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hk : depthKernel L (zetaDepth ρ) ^ j ≤ 2 ^ j * ((n : ℝ) + 1) ^ (2 * k + 2) := by
    calc
      depthKernel L (zetaDepth ρ) ^ j ≤ (2 * Real.exp |L|) ^ j :=
        pow_le_pow_left₀ (depthKernel_nonneg _ _) (depthKernel_zeta_le_exp L ρ) j
      _ = 2 ^ j * Real.exp ((j : ℝ) * |L|) := by rw [mul_pow, Real.exp_nat_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
  dsimp only [sourceDepthKernel, sourceTwist]
  rw [tr_twist]
  change Complex.normSq (tr f.1 ((ρ : ℂ) - (τ : ℂ) * Complex.I)) *
    depthKernel L (zetaDepth ρ) ^ j ≤ _
  calc
    Complex.normSq (tr f.1 ((ρ : ℂ) - (τ : ℂ) * Complex.I)) *
        depthKernel L (zetaDepth ρ) ^ j ≤
      (sourceRegularitySize f (k + 2) ^ 2 * Real.exp a /
        (1 + |(ρ : ℂ).im - τ|) ^ ((2 * k + 2) + 2)) *
          (2 ^ j * ((n : ℝ) + 1) ^ (2 * k + 2)) :=
      mul_le_mul hw hk (pow_nonneg (depthKernel_nonneg _ _) _) (by positivity)
    _ = (sourceRegularitySize f (k + 2) ^ 2 * Real.exp a * 2 ^ j) *
        (((n : ℝ) + 1) ^ (2 * k + 2) /
          (1 + |(ρ : ℂ).im - τ|) ^ ((2 * k + 2) + 2)) := by ring
    _ ≤ (sourceRegularitySize f (k + 2) ^ 2 * Real.exp a * 2 ^ j) *
        ((5 * 2 ^ (2 * k + 2)) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
      mul_le_mul_of_nonneg_left (regularity_moving_tail_ratio_le (2 * k + 2) n τ hτ ρ hχ)
        (by positivity)
    _ = _ := by unfold sourceRegularityTailConstant; ring

/-- One actual vanishing reference tail controls the whole regularity window. -/
theorem source_regularity_moving_trace_tail_le (f : CompactTest) (k : ℕ)
    (hreg : ContDiff ℝ (k + 2) f.1) {a : ℝ} (ha : 0 ≤ a)
    (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ a) (j n : ℕ) (L τ : ℝ)
    (hτ : |τ| ≤ (n : ℝ) / 2)
    (hwindow : (j : ℝ) * |L| ≤ ((2 * k + 2 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1)) :
    |zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j) -
      zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)| ≤
      (sourceRegularityTailConstant f k a * 2 ^ j) * sourceReferenceTail n := by
  let C := sourceRegularityTailConstant f k a * 2 ^ j
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
          (mul_le_mul_of_nonneg_left
            (sourceDepthKernel_regularity_tail_le f k hreg ha hsupp j n L τ hτ hwindow ρ hχ)
            (Nat.cast_nonneg _)) (sub_nonneg.mpr (sourceCutoff n).le_one)
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

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.sourceDepthKernel_regularity_tail_le
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.source_regularity_moving_trace_tail_le
