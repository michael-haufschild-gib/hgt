import GaloisForLFunctions.RHTower.GaussianGapSignPhaseTransition
import GaloisForLFunctions.InfiniteRankWeilTheory.TheTowersOfZeta

/-!+# The finite part of the Gaussian prime current

Subtracting every Gamma mode from the Gaussian prime discrepancy recovers its
continued finite part at every real point of the open strip. The entire zero
series is retained, with multiplicity; its remainder converges by an inverse-square
majorant. Reflection cancels the completed logarithmic derivatives and leaves
the exact polar and archimedean background.
-/

open Complex Filter Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- The full Gamma-mode field of the Gaussian prime discrepancy. -/
def gaussianZeroModes (σ y : ℝ) : ℂ :=
  ∑' q : XiZeroCopy,
    sigmaZeroAmplitude σ q * (y : ℂ) ^ (-((xiZero q - σ) / 2))

/-- The actual prime-minus-continuum current with its full zero field removed. -/
def gaussianPrimeFinitePart (σ y : ℝ) : ℂ :=
  ((gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y : ℝ) : ℂ) +
    gaussianZeroModes σ y

private def zeroFinitePart (σ : ℝ) (q : XiZeroCopy) : ℂ :=
  (1 / 2 - σ) / ((xiZero q - 1 / 2) * (xiZero q - σ))

private theorem zeroFinitePart_eq (σ : ℝ) (q : XiZeroCopy) :
    zeroFinitePart σ q = (xiZero q - 1 / 2)⁻¹ + ((σ : ℂ) - xiZero q)⁻¹ := by
  have hκ := XiAtlasFinitePart.xiZero_sub_half_ne_zero q
  have ha : xiZero q - σ ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at him
    exact xi_ne_zero_of_abs_im_le_one (by rw [him, abs_zero]; norm_num) (xi_xiZero q)
  rw [show (σ : ℂ) - xiZero q = -(xiZero q - σ) by ring, inv_neg]
  unfold zeroFinitePart
  rw [show 1 / 2 - (σ : ℂ) = (xiZero q - σ) - (xiZero q - 1 / 2) by ring]
  generalize xiZero q - 1 / 2 = κ at hκ ⊢
  generalize xiZero q - σ = a at ha ⊢
  field_simp
  ring

/-- Each Gamma-subtracted germ converges to its paired partial fraction. -/
theorem tendsto_sigmaZeroRemainder_finitePart {σ : ℝ} (hσ : σ < 3 / 2)
    (q : XiZeroCopy) :
    Tendsto (fun y : ℝ => sigmaZeroRemainder σ y q) (𝓝[>] 0)
      (𝓝 ((xiZero q - 1 / 2)⁻¹ + ((σ : ℂ) - xiZero q)⁻¹)) := by
  have hy0 : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hbound : ∀ y : ℝ, 0 < y →
      ‖sigmaZeroRemainder σ y q - (Real.exp (-y) : ℂ) * zeroFinitePart σ q‖ ≤
        9 / 4 * (2 * y + 2 * y ^ 2) * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
    intro y hy
    convert norm_sigmaZeroGerm_sub_le hσ hy q using 1
    simp only [sigmaZeroRemainder, zeroFinitePart]
    congr 1
    ring
  have hd : Tendsto (fun y : ℝ => sigmaZeroRemainder σ y q -
      (Real.exp (-y) : ℂ) * zeroFinitePart σ q) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : Tendsto (fun y : ℝ =>
        9 / 4 * (2 * y + 2 * y ^ 2) * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
      convert (((hy0.const_mul 2).add ((hy0.pow 2).const_mul 2)).const_mul
        (9 / 4)).mul_const (‖(xiZero q - 1 / 2)⁻¹‖ ^ 2) using 1
      norm_num
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (by filter_upwards [self_mem_nhdsWithin] with y hy; exact hbound y hy) hb
  have he : Tendsto (fun y : ℝ => (Real.exp (-y) : ℂ) * zeroFinitePart σ q)
      (𝓝[>] 0) (𝓝 (zeroFinitePart σ q)) := by
    have hr : Tendsto (fun y : ℝ => Real.exp (-y)) (𝓝[>] 0) (𝓝 1) := by
      simpa only [Function.comp_def, neg_zero, Real.exp_zero] using
        (Real.continuous_exp.tendsto (-0)).comp hy0.neg
    simpa only [Function.comp_def, Complex.ofReal_one, one_mul] using
      ((Complex.continuous_ofReal.tendsto 1).comp hr).mul_const (zeroFinitePart σ q)
  have ht := hd.add he
  simpa only [zero_add, sub_add_cancel, zeroFinitePart_eq] using ht

/-- The complete remainder series converges to the continued Xi current,
including when zeros lie to the right of the observation point. -/
theorem tendsto_tsum_sigmaZeroRemainder {σ : ℝ} (hσ : σ < 3 / 2) :
    Tendsto (fun y : ℝ => ∑' q : XiZeroCopy, sigmaZeroRemainder σ y q)
      (𝓝[>] 0) (𝓝 (logDeriv xi (σ : ℂ))) := by
  have hxi : xi (σ : ℂ) ≠ 0 := xi_ne_zero_of_abs_im_le_one (by simp)
  rw [logDeriv_xi_eq_partialFraction hxi]
  refine tendsto_tsum_of_dominated_convergence
    (summable_norm_inv_xiZero_sub_half_sq.mul_left (3 / 2 * |1 / 2 - σ| + 9))
    (fun q => tendsto_sigmaZeroRemainder_finitePart hσ q) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with y hy q
  exact norm_sigmaZeroRemainder_le hσ hy.1 hy.2.le q

/-- Full Gaussian renormalization recovers the polar and archimedean current
minus the completed logarithmic derivative throughout the real open strip. -/
theorem tendsto_gaussianPrimeFinitePart {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    Tendsto (gaussianPrimeFinitePart σ) (𝓝[>] 0)
      (𝓝 (gaussianArchimedeanCurrent (σ : ℂ) - logDeriv xi (σ : ℂ))) := by
  have hA := tendsto_gaussianArchimedeanCurrent_sub_MB (c := 2) two_pos
    (s := (σ : ℂ)) (by simpa using hσ0)
  have hM := (tendsto_const_nhds (x := gaussianArchimedeanCurrent (σ : ℂ))).sub hA
  simp only [sub_zero, sub_sub_cancel] at hM
  have h := hM.sub (tendsto_tsum_sigmaZeroRemainder (by linarith : σ < 3 / 2))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [gaussianPrimeFinitePart, sigmaGap_eq_archimedean_sub_zeroSeries hσ0 hσ1 hy,
    gaussianZeroModes]
  ring

/-- Reflection of the full finite part retains exactly the polar and
archimedean background; no zero-height transport is inserted. -/
theorem tendsto_gaussianPrimeFinitePart_reflection {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Tendsto (fun y : ℝ => gaussianPrimeFinitePart σ y +
        gaussianPrimeFinitePart (1 - σ) y) (𝓝[>] 0)
      (𝓝 (gaussianArchimedeanCurrent (σ : ℂ) +
        gaussianArchimedeanCurrent (1 - (σ : ℂ)))) := by
  have h := (tendsto_gaussianPrimeFinitePart hσ0 hσ1.le).add
    (tendsto_gaussianPrimeFinitePart (by linarith : 0 < 1 - σ) (by linarith))
  push_cast at h
  rw [logDeriv_xi_one_sub] at h
  convert h using 1
  congr 1
  ring

/-- Every mode strictly left of the observation point vanishes with the damping. -/
private theorem tendsto_gaussianMode_zero {σ : ℝ} (q : XiZeroCopy)
    (hq : (xiZero q).re < σ) :
    Tendsto (fun y : ℝ => sigmaZeroAmplitude σ q *
      (y : ℂ) ^ (-((xiZero q - σ) / 2))) (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hp : 0 < (σ - (xiZero q).re) / 2 := by linarith
  have ht := (Real.continuousAt_rpow_const 0 ((σ - (xiZero q).re) / 2)
    (Or.inr hp.le)).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  rw [Real.zero_rpow hp.ne'] at ht
  have h := ht.const_mul ‖sigmaZeroAmplitude σ q‖
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  congr 2
  simp only [Complex.neg_re, Complex.div_ofNat_re, Complex.sub_re, Complex.ofReal_re]
  ring

/-- The entire complementary zero tail vanishes after a finite exceptional layer
is removed. No uniform gap between that tail and the observation line is needed. -/
theorem tendsto_gaussianModes_complement {σ : ℝ} (hσ1 : σ ≤ 1)
    (F : Finset XiZeroCopy) (hF : ∀ q ∉ F, (xiZero q).re < σ) :
    Tendsto (fun y : ℝ => ∑' q : {q : XiZeroCopy // q ∉ F},
      sigmaZeroAmplitude σ q * (y : ℂ) ^ (-((xiZero q - σ) / 2)))
      (𝓝[>] 0) (𝓝 0) := by
  have hs := (summable_norm_sigmaZeroAmplitude hσ1).subtype {q : XiZeroCopy | q ∉ F}
  have hz : (0 : ℂ) = ∑' _q : {q : XiZeroCopy // q ∉ F}, (0 : ℂ) := tsum_zero.symm
  rw [hz]
  refine tendsto_tsum_of_dominated_convergence hs
    (fun q => tendsto_gaussianMode_zero q (hF q q.property)) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with y hy q
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy.1]
  have he : 0 ≤ (-((xiZero q - σ) / 2)).re := by
    simp only [Complex.neg_re, Complex.div_ofNat_re, Complex.sub_re, Complex.ofReal_re]
    have hq := hF q q.property
    linarith
  exact mul_le_of_le_one_right (norm_nonneg _)
    (Real.rpow_le_one hy.1.le hy.2.le he)

/-- Subtracting just the finite exceptional Gamma field recovers the full
continued background, while the complete infinite complementary tail decays. -/
theorem tendsto_gaussianPrimeCurrent_add_finite_modes {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (F : Finset XiZeroCopy)
    (hF : ∀ q ∉ F, (xiZero q).re < σ) :
    Tendsto (fun y : ℝ =>
      ((gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y : ℝ) : ℂ) +
        ∑ q ∈ F, sigmaZeroAmplitude σ q * (y : ℂ) ^ (-((xiZero q - σ) / 2)))
      (𝓝[>] 0)
      (𝓝 (gaussianArchimedeanCurrent (σ : ℂ) - logDeriv xi (σ : ℂ))) := by
  have ht := (tendsto_gaussianPrimeFinitePart hσ0 hσ1).sub
    (tendsto_gaussianModes_complement hσ1 F hF)
  rw [sub_zero] at ht
  refine ht.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with y hy
  have hR : Summable fun q : XiZeroCopy => sigmaZeroRemainder σ y q :=
    Summable.of_norm_bounded
      (summable_norm_inv_xiZero_sub_half_sq.mul_left (3 / 2 * |1 / 2 - σ| + 9))
      (fun q => norm_sigmaZeroRemainder_le (by linarith) hy.1 hy.2.le q)
  have hB : Summable fun q : XiZeroCopy =>
      sigmaZeroAmplitude σ q * (y : ℂ) ^ (-((xiZero q - σ) / 2)) := by
    apply ((summable_sigmaZeroGerm hσ1 hy.1).sub hR).congr
    intro q
    rw [sigmaZeroRemainder, sub_sub_cancel]
  rw [gaussianPrimeFinitePart, gaussianZeroModes, ← hB.sum_add_tsum_subtype_compl F]
  ring

/-- Failure of AAL gives one nonempty finite top field whose removal recovers
the continued prime current at every real observation point between top and tail. -/
theorem not_asymptoticAbscissaLaw_has_gaussian_finitePart
    (hnot : ¬ RHTower.AsymptoticAbscissaLaw) :
    ∃ (F : Finset XiZeroCopy) (β θ : ℝ), F.Nonempty ∧ 1 / 2 < β ∧ β < 1 ∧ θ < β ∧
      (∀ q ∈ F, (xiZero q).re = β) ∧ ∀ σ : ℝ, max θ 0 < σ → σ < β →
        Tendsto (fun y : ℝ =>
          ((gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y : ℝ) : ℂ) +
            ∑ q ∈ F, sigmaZeroAmplitude σ q * (y : ℂ) ^ (-((xiZero q - σ) / 2)))
          (𝓝[>] 0)
          (𝓝 (gaussianArchimedeanCurrent (σ : ℂ) - logDeriv xi (σ : ℂ))) := by
  rw [InfiniteRankWeilTheory.asymptoticAbscissaLaw_zetaConfig_iff,
    InfiniteRankWeilTheory.not_asymptoticAbscissaLaw_iff_hasIsolatedTop] at hnot
  obtain ⟨F, β, θ, hF, hβ, hθ, htop, hrest⟩ := hnot
  have hβ1 : β < 1 := by
    obtain ⟨q, hq⟩ := hF
    rw [← htop q hq]
    exact xiZeroCopy_re_lt_one q
  refine ⟨F, β, θ, hF, hβ, hβ1, hθ, htop, fun σ hσ hσβ => ?_⟩
  apply tendsto_gaussianPrimeCurrent_add_finite_modes
    (lt_of_le_of_lt (le_max_right _ _) hσ) (by linarith) F
  intro q hq
  exact (hrest q hq).trans_lt (lt_of_le_of_lt (le_max_left _ _) hσ)

#print axioms tendsto_gaussianPrimeFinitePart
#print axioms tendsto_gaussianPrimeFinitePart_reflection
#print axioms tendsto_gaussianPrimeCurrent_add_finite_modes
#print axioms not_asymptoticAbscissaLaw_has_gaussian_finitePart

end GaloisForLFunctions.EulerFETransportTheory
