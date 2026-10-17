import GaloisForLFunctions.BiScaleUncertainty.CompactSourcePairVariance

/-!
# Exact source-lobe mass and nodal variance loss

The positive-lag modulus defect is exactly four times the product of the two
weighted source-lobe masses. Zero lobe mass detects absence of that sign on
the entire nonzero source, including disconnected components and zero sources.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.PathCongestion
set_option autoImplicit false

def sourceAbs (f : C(ℝ, ℝ)) : C(ℝ, ℝ) := ⟨fun x => |f x|, f.continuous.abs⟩

def sourcePositiveMass (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) : ℝ :=
  ∫ u, ψ u ^ 2 * max (f u) 0

def sourceNegativeMass (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) : ℝ :=
  sourcePositiveMass ψ (-f)

theorem integrable_sourcePositiveMass (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) :
    Integrable (fun u => ψ u ^ 2 * max (f u) 0) := by
  have h := integrable_sourceMoment ψ
    (⟨fun u => max (f u) 0, f.continuous.max continuous_const⟩ : C(ℝ, ℝ)) 1
  change Integrable (fun u => ψ u ^ 2 * (max (f u) 0) ^ 1) at h
  simpa only [pow_one] using h

theorem sourcePositiveMass_nonneg (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) :
    0 ≤ sourcePositiveMass ψ f := integral_nonneg (fun _ => by positivity)

theorem sourceNegativeMass_nonneg (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) :
    0 ≤ sourceNegativeMass ψ f := sourcePositiveMass_nonneg ψ (-f)

theorem sourcePositiveMass_eq_zero_iff (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) :
    sourcePositiveMass ψ f = 0 ↔ ∀ u, ψ u ≠ 0 → f u ≤ 0 := by
  constructor
  · intro hi
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall (fun u => show 0 ≤ ψ u ^ 2 * max (f u) 0 by positivity))
      (integrable_sourcePositiveMass ψ f)).mp hi
    have hz := Measure.eq_of_ae_eq hae
      ((ψ.continuous.pow 2).mul (f.continuous.max continuous_const)) continuous_const
    intro u hu
    have hm : max (f u) 0 = 0 :=
      (mul_eq_zero.mp (congrFun hz u)).resolve_left (pow_ne_zero _ hu)
    exact (le_max_left (f u) 0).trans (le_of_eq hm)
  · intro hf
    apply integral_eq_zero_of_ae
    filter_upwards [] with u
    by_cases hu : ψ u = 0
    · simp [hu]
    · simp [max_eq_right (hf u hu)]

theorem sourceNegativeMass_eq_zero_iff (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) :
    sourceNegativeMass ψ f = 0 ↔ ∀ u, ψ u ≠ 0 → 0 ≤ f u := by
  simpa only [sourceNegativeMass, ContinuousMap.neg_apply, neg_nonpos] using
    sourcePositiveMass_eq_zero_iff ψ (-f)

theorem sourceMoment_one_eq_lobe_difference (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) :
    sourceMoment ψ f 1 = sourcePositiveMass ψ f - sourceNegativeMass ψ f := by
  rw [sourcePositiveMass, sourceNegativeMass, sourcePositiveMass,
    ← integral_sub (integrable_sourcePositiveMass ψ f) (integrable_sourcePositiveMass ψ (-f))]
  apply integral_congr_ae
  filter_upwards [] with u
  change ψ u ^ 2 * f u ^ 1 = ψ u ^ 2 * max (f u) 0 - ψ u ^ 2 * max (-f u) 0
  rcases le_total 0 (f u) with h | h
  · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]

theorem sourceMoment_abs_one_eq_lobe_sum (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) :
    sourceMoment ψ (sourceAbs f) 1 = sourcePositiveMass ψ f + sourceNegativeMass ψ f := by
  rw [sourcePositiveMass, sourceNegativeMass, sourcePositiveMass,
    ← integral_add (integrable_sourcePositiveMass ψ f) (integrable_sourcePositiveMass ψ (-f))]
  apply integral_congr_ae
  filter_upwards [] with u
  change ψ u ^ 2 * |f u| ^ 1 = ψ u ^ 2 * max (f u) 0 + ψ u ^ 2 * max (-f u) 0
  rcases le_total 0 (f u) with h | h
  · simp [abs_of_nonneg h, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  · simp [abs_of_nonpos h, max_eq_right h, max_eq_left (neg_nonneg.mpr h)]

theorem weightedVariance_modulus_difference (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) :
    weightedVariance ψ f - weightedVariance ψ (sourceAbs f) =
      4 * sourcePositiveMass ψ f * sourceNegativeMass ψ f := by
  have h₀ : sourceMoment ψ (sourceAbs f) 0 = sourceMoment ψ f 0 := by
    simp [sourceMoment]
  have h₂ : sourceMoment ψ (sourceAbs f) 2 = sourceMoment ψ f 2 := by
    simp [sourceMoment, sourceAbs, sq_abs]
  rw [weightedVariance, weightedVariance, h₀, h₂,
    sourceMoment_one_eq_lobe_difference, sourceMoment_abs_one_eq_lobe_sum]
  ring

def nodalLagGap (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) (e : Edge) : ℝ :=
  sourcePair ψ e * (4 * (max (f (e.2+e.1)) 0 * max (-f e.2) 0 +
    max (-f (e.2+e.1)) 0 * max (f e.2) 0))

theorem nodalLagGap_nonneg (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) (e : Edge) :
    0 ≤ nodalLagGap ψ f e := mul_nonneg (sourcePair_nonneg ψ e) (by positivity)

theorem nodalLagGap_eq_difference (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) (e : Edge) :
    nodalLagGap ψ f e = lagGap ψ f e - lagGap ψ (sourceAbs f) e := by
  have h := nodal_mulJump_sq_decomp
    (fun j : ℕ => if j = 1 then f e.2 else f (e.2+e.1)) 2 1
  have hd : (f (e.2+e.1)-f e.2)^2 = (|f (e.2+e.1)|-|f e.2|)^2 +
      4*(max (f (e.2+e.1)) 0 * max (-f e.2) 0 +
        max (-f (e.2+e.1)) 0 * max (f e.2) 0) := by
    simpa [mulJump, seqPos, seqNeg] using h
  dsimp [nodalLagGap, lagGap, pairGap, sourceAbs, sourcePair]
  rw [hd]
  ring

theorem integrable_nodalLagGap (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) :
    Integrable (nodalLagGap ψ f) (volume.prod volume) := by
  change Integrable (fun e => nodalLagGap ψ f e) (volume.prod volume)
  simp_rw [nodalLagGap_eq_difference]
  exact (integrable_lagGap ψ f).sub (integrable_lagGap ψ (sourceAbs f))

/-- Positive lags count each opposite-sign source pair exactly once. -/
theorem integral_positive_nodalLagGap (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) :
    (∫ e, nodalLagGap ψ f e ∂(volume.restrict (Ioi (0 : ℝ))).prod volume) =
      4 * sourcePositiveMass ψ f * sourceNegativeMass ψ f := by
  simp_rw [nodalLagGap_eq_difference]
  rw [integral_sub
    ((integrable_lagGap ψ f).mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl))
    ((integrable_lagGap ψ (sourceAbs f)).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)),
    integral_positive_lagGap, integral_positive_lagGap, weightedVariance_modulus_difference]

theorem lintegral_positive_nodalLagGap (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) :
    (∫⁻ e, ENNReal.ofReal (nodalLagGap ψ f e)
      ∂(volume.restrict (Ioi (0 : ℝ))).prod volume) =
      ENNReal.ofReal (4 * sourcePositiveMass ψ f * sourceNegativeMass ψ f) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((integrable_nodalLagGap ψ f).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl))
    (Eventually.of_forall (nodalLagGap_nonneg ψ f)), integral_positive_nodalLagGap]

end GaloisForLFunctions.BiScaleUncertainty.PathCongestion
