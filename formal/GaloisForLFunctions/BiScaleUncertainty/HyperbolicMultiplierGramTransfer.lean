import GaloisForLFunctions.BiScaleUncertainty.CosecantSecantDualDecomposition
import GaloisForLFunctions.BiScaleUncertainty.SynchronizedCosetSineLeverage
import GaloisForLFunctions.BiScaleUncertainty.SignedDyadicCollarPartition

/-!
# Hyperbolic multiplier Gram transfer

The sine multiplier of an odd source is even, but its translates need not inherit the
source's orthogonality. Retaining their full Gram energy gives an unconditional transfer
to a secant correlation collar with an explicit cosine-increment companion. The exact
increment identity records why the companion cannot be discarded with the same sign.

All theorems take actual compactly supported continuous sources and arbitrary finite
nodes and weights. No zero-grid, parity, or unknown energy estimate is assumed.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported InnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
noncomputable section
variable {ι : Type*}

/-- Hyperbolic cosine multiplication on the compact-continuous source space. -/
def coshCompact (α : ℝ) (f : C_c(ℝ, ℝ)) : C_c(ℝ, ℝ) :=
  ⟨⟨coshMultiplier α f, continuous_coshMultiplier α f.continuous⟩,
    hasCompactSupport_coshMultiplier α f.hasCompactSupport⟩

/-- Hyperbolic sine multiplication on the compact-continuous source space. -/
def sinhCompact (α : ℝ) (f : C_c(ℝ, ℝ)) : C_c(ℝ, ℝ) :=
  ⟨⟨sinhMultiplier α f, continuous_sinhMultiplier α f.continuous⟩,
    hasCompactSupport_sinhMultiplier α f.hasCompactSupport⟩

/-- Correlation with an arbitrary finite translation packet is controlled by its full Gram
energy, including every off-diagonal entry. -/
theorem translationPacket_correlation_le (f : C_c(ℝ, ℝ))
    (s : Finset ι) (w t : ι → ℝ) (y : ℝ) :
    (∑ i ∈ s, w i * autocorr f (t i - y)) ≤
      Real.sqrt (autocorr f 0 * translationGramEnergy f s w t) := by
  let P := ∑ i ∈ s, (w i : ℂ) • translationFeature f (t i)
  have hpair : RCLike.re (inner ℂ (translationFeature f y) P) =
      ∑ i ∈ s, w i * autocorr f (t i - y) := by
    change RCLike.re (inner ℂ (translationFeature f y)
      (∑ i ∈ s, (w i : ℂ) • translationFeature f (t i))) = _
    rw [inner_sum]
    simp_rw [inner_smul_right, translationFeature_inner]
    simp
  have hn : ‖translationFeature f y‖ ^ 2 = autocorr f 0 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), translationFeature_inner]
    simp
  have hp : ‖P‖ ^ 2 = translationGramEnergy f s w t :=
    translationFeature_packet_energy f s w t
  have h := re_inner_le_norm (𝕜 := ℂ) (translationFeature f y) P
  rw [hpair] at h
  calc
    _ ≤ ‖translationFeature f y‖ * ‖P‖ := h
    _ = Real.sqrt (autocorr f 0 * translationGramEnergy f s w t) := by
      rw [← hn, ← hp, Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- Exact hyperbolic difference of full Gram energies. Source zeros identify the two
off-diagonal Gram entries; they do not make either entry vanish. -/
theorem translationGramEnergy_cosh_sub_sinh (f : C_c(ℝ, ℝ)) (α : ℝ)
    (s : Finset ι) (w t : ι → ℝ) :
    translationGramEnergy (coshCompact α f) s w t -
        translationGramEnergy (sinhCompact α f) s w t =
      ∑ i ∈ s, ∑ j ∈ s,
        w i * w j * Real.cosh (α * (t j - t i)) * autocorr f (t j - t i) := by
  unfold translationGramEnergy
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  change w i * w j * autocorr (coshMultiplier α f) _ -
    w i * w j * autocorr (sinhMultiplier α f) _ = _
  rw [← mul_sub, autocorr_coshMultiplier_sub_sinhMultiplier
    (f := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport]
  ring

/-- The measured failure of the sine multiplier's translation packet to have clique energy. -/
def sinhCliqueGramDefect (f : C_c(ℝ, ℝ)) (α : ℝ)
    (s : Finset ι) (w t : ι → ℝ) : ℝ :=
  translationGramEnergy (sinhCompact α f) s w t -
    autocorr (sinhCompact α f) 0 * ∑ i ∈ s, w i ^ 2

/-- Exact Gram energy with its measurable deviation from the diagonal clique model. -/
theorem sinhGram_eq_diagonal_add_defect (f : C_c(ℝ, ℝ)) (α : ℝ)
    (s : Finset ι) (w t : ι → ℝ) :
    translationGramEnergy (sinhCompact α f) s w t =
      autocorr (sinhCompact α f) 0 * (∑ i ∈ s, w i ^ 2) +
        sinhCliqueGramDefect f α s w t := by
  unfold sinhCliqueGramDefect
  ring

/-- Secant weights pulled back through the half-scale hyperbolic intertwiner. -/
def secantTransferWeights (b t : ι → ℝ) (y : ℝ) (i : ι) : ℝ :=
  b i / Real.cosh ((t i - y) / 2) ^ 2

/-- Secant correlation with the explicit cosine-increment companion required for a
lower-bound transfer from the sine multiplier. -/
def compensatedSecantCollar (f : C_c(ℝ, ℝ))
    (s : Finset ι) (b t : ι → ℝ) (y : ℝ) : ℝ :=
  ∑ i ∈ s, (b i * (autocorr f (t i - y) * archSechHalfWeight (t i - y)) +
    secantTransferWeights b t y i *
      (autocorr (coshCompact (1 / 2) f) 0 -
        autocorr (coshCompact (1 / 2) f) (t i - y)))

/-- Pointwise compensated secant transfer, with no grid assumption. -/
theorem secant_compensated_eq (f : C_c(ℝ, ℝ)) (x : ℝ) :
    autocorr f x * archSechHalfWeight x +
        (autocorr (coshCompact (1 / 2) f) 0 -
          autocorr (coshCompact (1 / 2) f) x) / Real.cosh (x / 2) ^ 2 =
      (autocorr (coshCompact (1 / 2) f) 0 -
        autocorr (sinhCompact (1 / 2) f) x) / Real.cosh (x / 2) ^ 2 := by
  rw [autocorr_mul_archSechHalfWeight_eq_cosh_sub_sinh
    (f := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport]
  change (_ - _) / _ +
    (autocorr (coshMultiplier (1 / 2) f) 0 - autocorr (coshMultiplier (1 / 2) f) x) / _ =
    (autocorr (coshMultiplier (1 / 2) f) 0 - autocorr (sinhMultiplier (1 / 2) f) x) / _
  ring

/-- Exact cancellation of the cosine correlations in the finite collar. -/
theorem compensatedSecantCollar_eq (f : C_c(ℝ, ℝ))
    (s : Finset ι) (b t : ι → ℝ) (y : ℝ) :
    compensatedSecantCollar f s b t y =
      autocorr (coshCompact (1 / 2) f) 0 * (∑ i ∈ s, secantTransferWeights b t y i) -
        ∑ i ∈ s, secantTransferWeights b t y i *
          autocorr (sinhCompact (1 / 2) f) (t i - y) := by
  unfold compensatedSecantCollar
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := congrArg (fun z : ℝ => b i * z) (secant_compensated_eq f (t i - y))
  dsimp [secantTransferWeights]
  linear_combination h

/-- Full multi-node lower-bound transfer to the compensated secant collar. The square root
contains the actual sine-multiplier Gram energy, not an assumed diagonal approximation. -/
theorem compensatedSecantCollar_ge_gram (f : C_c(ℝ, ℝ))
    (s : Finset ι) (b t : ι → ℝ) (y : ℝ) :
    autocorr (coshCompact (1 / 2) f) 0 * (∑ i ∈ s, secantTransferWeights b t y i) -
        Real.sqrt (autocorr (sinhCompact (1 / 2) f) 0 *
          translationGramEnergy (sinhCompact (1 / 2) f) s (secantTransferWeights b t y) t) ≤
      compensatedSecantCollar f s b t y := by
  rw [compensatedSecantCollar_eq]
  exact sub_le_sub_left
    (translationPacket_correlation_le (sinhCompact (1 / 2) f) s
      (secantTransferWeights b t y) t y) _

/-- The transfer with the original energy, the sine energy, and the exact clique defect
displayed separately. Vanishing defect recovers the clique sphere coefficient. -/
theorem compensatedSecantCollar_ge_clique_defect (f : C_c(ℝ, ℝ))
    (s : Finset ι) (b t : ι → ℝ) (y : ℝ) :
    (autocorr f 0 + autocorr (sinhCompact (1 / 2) f) 0) *
        (∑ i ∈ s, secantTransferWeights b t y i) -
      Real.sqrt (autocorr (sinhCompact (1 / 2) f) 0 *
        (autocorr (sinhCompact (1 / 2) f) 0 *
          (∑ i ∈ s, secantTransferWeights b t y i ^ 2) +
          sinhCliqueGramDefect f (1 / 2) s (secantTransferWeights b t y) t)) ≤
      compensatedSecantCollar f s b t y := by
  have h := compensatedSecantCollar_ge_gram f s b t y
  rw [sinhGram_eq_diagonal_add_defect] at h
  have h0 := autocorr_coshMultiplier_zero_eq f.continuous f.hasCompactSupport (1 / 2)
  change autocorr (coshCompact (1 / 2) f) 0 =
    autocorr f 0 + autocorr (sinhCompact (1 / 2) f) 0 at h0
  rwa [h0] at h

/-- The ordinary clique sphere lower bound survives with an explicit penalty for the
positive part of the measured multiplier Gram defect. Negative defects cost nothing. -/
theorem compensatedSecantCollar_ge_clique_penalty (f : C_c(ℝ, ℝ))
    (s : Finset ι) (b t : ι → ℝ) (y : ℝ) :
    autocorr f 0 * (∑ i ∈ s, secantTransferWeights b t y i) +
        autocorr (sinhCompact (1 / 2) f) 0 *
          ((∑ i ∈ s, secantTransferWeights b t y i) -
            Real.sqrt (∑ i ∈ s, secantTransferWeights b t y i ^ 2)) -
        Real.sqrt (autocorr (sinhCompact (1 / 2) f) 0 *
          max (sinhCliqueGramDefect f (1 / 2) s (secantTransferWeights b t y) t) 0) ≤
      compensatedSecantCollar f s b t y := by
  let R := autocorr (sinhCompact (1 / 2) f) 0
  let A := ∑ i ∈ s, secantTransferWeights b t y i ^ 2
  let D := sinhCliqueGramDefect f (1 / 2) s (secantTransferWeights b t y) t
  have hR : 0 ≤ R := autocorr_zero_nonneg _
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ R * max D 0 := mul_nonneg hR (le_max_right _ _)
  have hsq : (R * Real.sqrt A) ^ 2 = R * (R * A) := by
    rw [mul_pow, Real.sq_sqrt hA]
    ring
  have hroot : Real.sqrt (R * (R * A + D)) ≤
      R * Real.sqrt A + Real.sqrt (R * max D 0) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hcost : R * D ≤ R * max D 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hR
    have hcross : 0 ≤ (R * Real.sqrt A) * Real.sqrt (R * max D 0) := by positivity
    nlinarith [Real.sq_sqrt hB]
  have h := compensatedSecantCollar_ge_clique_defect f s b t y
  change (autocorr f 0 + R) * (∑ i ∈ s, secantTransferWeights b t y i) -
    Real.sqrt (R * (R * A + D)) ≤ _ at h
  change autocorr f 0 * (∑ i ∈ s, secantTransferWeights b t y i) +
    R * ((∑ i ∈ s, secantTransferWeights b t y i) - Real.sqrt A) -
      Real.sqrt (R * max D 0) ≤ _
  nlinarith

/-- Signed-kernel version of the transfer. In particular the actual plastic crossover
kernel can be inserted as `k`; no identification with the secant kernel is required. -/
theorem kernel_compensated_ge_gram (f : C_c(ℝ, ℝ))
    (s : Finset ι) (k t : ι → ℝ) (y : ℝ) :
    autocorr (coshCompact (1 / 2) f) 0 *
        (∑ i ∈ s, k i / Real.cosh ((t i - y) / 2)) -
      Real.sqrt (autocorr (sinhCompact (1 / 2) f) 0 *
        translationGramEnergy (sinhCompact (1 / 2) f) s
          (fun i => k i / Real.cosh ((t i - y) / 2)) t) ≤
      ∑ i ∈ s, (k i * autocorr f (t i - y) +
        k i / Real.cosh ((t i - y) / 2) *
          (autocorr (coshCompact (1 / 2) f) 0 -
            autocorr (coshCompact (1 / 2) f) (t i - y))) := by
  let b : ι → ℝ := fun i => k i * Real.cosh ((t i - y) / 2)
  have hv : secantTransferWeights b t y =
      fun i => k i / Real.cosh ((t i - y) / 2) := by
    funext i
    dsimp [secantTransferWeights, b]
    field_simp [(Real.cosh_pos ((t i - y) / 2)).ne']
  have h := compensatedSecantCollar_ge_gram f s b t y
  rw [hv] at h
  refine h.trans_eq ?_
  unfold compensatedSecantCollar
  rw [hv]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp [b, archSechHalfWeight]
  field_simp [(Real.cosh_pos ((t i - y) / 2)).ne']

/-- Exact secant-increment identity: the sine-multiplier increment has a minus sign. -/
theorem secant_increment_eq_multiplier_difference (f : C_c(ℝ, ℝ)) (x : ℝ) :
    (autocorr f 0 - autocorr f x) * archSechHalfWeight x =
      autocorr f 0 * (archSechHalfWeight x - 1 / Real.cosh (x / 2) ^ 2) +
        ((autocorr (coshCompact (1 / 2) f) 0 - autocorr (coshCompact (1 / 2) f) x) -
          (autocorr (sinhCompact (1 / 2) f) 0 - autocorr (sinhCompact (1 / 2) f) x)) /
            Real.cosh (x / 2) ^ 2 := by
  have hx := autocorr_mul_archSechHalfWeight_eq_cosh_sub_sinh
    f.continuous f.hasCompactSupport x
  have h0 := autocorr_coshMultiplier_zero_eq f.continuous f.hasCompactSupport (1 / 2)
  change autocorr (coshCompact (1 / 2) f) 0 =
    autocorr f 0 + autocorr (sinhCompact (1 / 2) f) 0 at h0
  change autocorr f x * archSechHalfWeight x =
    (autocorr (coshCompact (1 / 2) f) x - autocorr (sinhCompact (1 / 2) f) x) / _ at hx
  rw [h0]
  linear_combination -hx

/-- Continuous collar weights remain continuous after secant transfer. -/
theorem continuous_secantTransferWeights (b : ι → C(ℝ, ℝ)) (t : ι → ℝ) (i : ι) :
    Continuous (fun y => secantTransferWeights (fun j => b j y) t y i) := by
  unfold secantTransferWeights
  exact (b i).continuous.div
    ((Real.continuous_cosh.comp ((continuous_const.sub continuous_id).div_const 2)).pow 2)
    (fun y => pow_ne_zero 2 (Real.cosh_pos _).ne')

/-- Continuity of the actual compensated collar, without differentiability of the source. -/
theorem continuous_compensatedSecantCollar (f : C_c(ℝ, ℝ))
    (s : Finset ι) (b : ι → C(ℝ, ℝ)) (t : ι → ℝ) :
    Continuous (fun y => compensatedSecantCollar f s (fun i => b i y) t y) := by
  simp_rw [compensatedSecantCollar_eq]
  refine (continuous_const.mul (continuous_finsetSum s fun i _ =>
    continuous_secantTransferWeights b t i)).sub ?_
  refine continuous_finsetSum s fun i _ => ?_
  exact (continuous_secantTransferWeights b t i).mul
    ((continuous_autocorr_compact (sinhCompact (1 / 2) f)).comp
      (continuous_const.sub continuous_id))

/-- Integrated multi-node transfer on an arbitrary compact collar interval. The interval is
ordered by `min` and `max`, so no endpoint-order or integrability premise is required. -/
theorem integral_compensatedSecantCollar_ge_gram (f : C_c(ℝ, ℝ))
    (s : Finset ι) (b : ι → C(ℝ, ℝ)) (t : ι → ℝ) (a z : ℝ) :
    (∫ y in min a z..max a z,
      autocorr (coshCompact (1 / 2) f) 0 *
          (∑ i ∈ s, secantTransferWeights (fun j => b j y) t y i) -
        Real.sqrt (autocorr (sinhCompact (1 / 2) f) 0 *
          translationGramEnergy (sinhCompact (1 / 2) f) s
            (secantTransferWeights (fun j => b j y) t y) t)) ≤
      ∫ y in min a z..max a z, compensatedSecantCollar f s (fun i => b i y) t y := by
  have hv := continuous_secantTransferWeights b t
  have hg : Continuous (fun y => translationGramEnergy (sinhCompact (1 / 2) f) s
      (secantTransferWeights (fun j => b j y) t y) t) := by
    unfold translationGramEnergy
    exact continuous_finsetSum s fun i _ => continuous_finsetSum s fun j _ =>
      ((hv i).mul (hv j)).mul continuous_const
  have hl : Continuous (fun y =>
      autocorr (coshCompact (1 / 2) f) 0 *
          (∑ i ∈ s, secantTransferWeights (fun j => b j y) t y i) -
        Real.sqrt (autocorr (sinhCompact (1 / 2) f) 0 *
          translationGramEnergy (sinhCompact (1 / 2) f) s
            (secantTransferWeights (fun j => b j y) t y) t)) :=
    (continuous_const.mul (continuous_finsetSum s fun i _ => hv i)).sub
      (Real.continuous_sqrt.comp (continuous_const.mul hg))
  exact intervalIntegral.integral_mono_on (min_le_max : min a z ≤ max a z)
    (hl.intervalIntegrable _ _)
    ((continuous_compensatedSecantCollar f s b t).intervalIntegrable _ _)
    (fun y _ => compensatedSecantCollar_ge_gram f s (fun i => b i y) t y)

end
end GaloisForLFunctions.BiScaleUncertainty
