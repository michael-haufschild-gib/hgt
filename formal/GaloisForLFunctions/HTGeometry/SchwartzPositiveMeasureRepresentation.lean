import GaloisForLFunctions.HTGeometry.SchwartzCompactPositiveFunctional

/-!
# Positive momentum forms are exactly positive temperate spectral measures

This module closes the Bochner--Schwartz representation in the precise Schwartz-form category.
It proves compactly supported Schwartz functions are dense by an explicit expanding cutoff with
`O((n+1)⁻¹)` control in every Schwartz seminorm.  Consequently the Riesz measure reconstructed
from compact spectral packets represents the original jointly continuous nonnegative
momentum-symmetric sesquilinear form on all of Schwartz space.
-/

open Complex Function Filter Set MeasureTheory TopologicalSpace
open scoped SchwartzMap FourierTransform Topology Polynomial ContDiff CompactlySupported

noncomputable section

namespace SchwartzMap

def scaledUnitCutoff (n : ℕ) : SchwartzMap ℝ ℂ := by
  let r : ℝ := n + 1
  have hr : r ≠ 0 := by dsimp [r]; positivity
  let c : ℝ := r⁻¹
  have hc : c ≠ 0 := inv_ne_zero hr
  let g : ℝ → ℂ := fun t => compactIntervalCutoff 0 (c * t)
  have hgcompact : HasCompactSupport g :=
    (compactIntervalCutoff_hasCompactSupport 0).comp_homeomorph
      (Homeomorph.mulLeft₀ c hc)
  have hgcont : ContDiff ℝ (⊤ : ℕ∞) g :=
    (compactIntervalCutoff 0).smooth ⊤ |>.comp (contDiff_const.mul contDiff_id)
  exact hgcompact.toSchwartzMap hgcont

@[simp] theorem scaledUnitCutoff_apply (n : ℕ) (t : ℝ) :
    scaledUnitCutoff n t = compactIntervalCutoff 0 (((n : ℝ) + 1)⁻¹ * t) := rfl

theorem scaledUnitCutoff_hasCompactSupport (n : ℕ) :
    HasCompactSupport (scaledUnitCutoff n) := by
  rw [scaledUnitCutoff]
  exact (compactIntervalCutoff_hasCompactSupport 0).comp_homeomorph
    (Homeomorph.mulLeft₀ (((n : ℝ) + 1)⁻¹) (by positivity))

theorem compactIntervalCutoff_zero_norm_le_one (t : ℝ) :
    ‖compactIntervalCutoff 0 t‖ ≤ 1 := by
  rw [compactIntervalCutoff]
  let b : ContDiffBump (0 : ℝ) :=
    ⟨|0| + 1, |0| + 2, by positivity, by linarith⟩
  change ‖((b t : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_of_nonneg b.nonneg]
  exact b.le_one

theorem scaledUnitCutoff_norm_le_one (n : ℕ) (t : ℝ) :
    ‖scaledUnitCutoff n t‖ ≤ 1 := by
  rw [scaledUnitCutoff_apply]
  exact compactIntervalCutoff_zero_norm_le_one _

theorem scaledUnitCutoff_apply_of_abs_le (n : ℕ) {t : ℝ}
    (ht : |t| ≤ (n : ℝ) + 1) : scaledUnitCutoff n t = 1 := by
  rw [scaledUnitCutoff_apply]
  apply compactIntervalCutoff_apply_of_abs_le_add_one
  have hr : 0 < (n : ℝ) + 1 := by positivity
  rw [abs_mul, abs_inv, abs_of_pos hr]
  simpa [div_eq_inv_mul] using (div_le_one hr).mpr ht

theorem iteratedDeriv_scaledUnitCutoff (n i : ℕ) (t : ℝ) :
    iteratedDeriv i (scaledUnitCutoff n) t =
      (((n : ℝ) + 1)⁻¹) ^ i •
        iteratedDeriv i (compactIntervalCutoff 0) ((((n : ℝ) + 1)⁻¹) * t) := by
  change iteratedDeriv i
    (fun x : ℝ => compactIntervalCutoff 0 ((((n : ℝ) + 1)⁻¹) * x)) t = _
  rw [congrFun (iteratedDeriv_comp_const_smul
    ((compactIntervalCutoff 0).smooth i) (((n : ℝ) + 1)⁻¹)) t]

def compactSupportApproximation (n : ℕ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (scaledUnitCutoff n) f

@[simp] theorem compactSupportApproximation_apply (n : ℕ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    compactSupportApproximation n f t = scaledUnitCutoff n t * f t := by
  rw [compactSupportApproximation, SchwartzMap.smulLeftCLM_apply_apply]
  · rfl
  · exact (scaledUnitCutoff n).hasTemperateGrowth

theorem compactSupportApproximation_hasCompactSupport (n : ℕ) (f : SchwartzMap ℝ ℂ) :
    HasCompactSupport (compactSupportApproximation n f) := by
  rw [HasCompactSupport]
  apply IsCompact.of_isClosed_subset
    (show IsCompact (tsupport (scaledUnitCutoff n)) from
      scaledUnitCutoff_hasCompactSupport n)
    (isClosed_tsupport (compactSupportApproximation n f))
  intro t ht
  exact (SchwartzMap.tsupport_smulLeftCLM_subset (scaledUnitCutoff n) f ht).2

theorem iteratedDeriv_scaledUnitCutoff_sub_one (n i : ℕ) (t : ℝ) :
    iteratedDeriv i (fun x : ℝ => scaledUnitCutoff n x - 1) t =
      if i = 0 then scaledUnitCutoff n t - 1 else
        (((n : ℝ) + 1)⁻¹) ^ i •
          iteratedDeriv i (compactIntervalCutoff 0) ((((n : ℝ) + 1)⁻¹) * t) := by
  change iteratedDeriv i
    ((scaledUnitCutoff n : ℝ → ℂ) - (fun _ : ℝ => 1)) t = _
  rw [iteratedDeriv_sub
    ((scaledUnitCutoff n).smooth i |>.contDiffAt)
    (contDiffAt_const (x := t)), iteratedDeriv_const,
    iteratedDeriv_scaledUnitCutoff]
  split_ifs with hi
  · subst i
    simp
  · simp

theorem iteratedDeriv_compactSupportApproximation_sub (n m : ℕ)
    (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    iteratedDeriv m (fun x : ℝ => compactSupportApproximation n f x - f x) t =
      ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℂ) *
          iteratedDeriv i (fun x : ℝ => scaledUnitCutoff n x - 1) t *
          iteratedDeriv (m - i) f t := by
  have heq : (fun x : ℝ => compactSupportApproximation n f x - f x) =
      fun x : ℝ => (scaledUnitCutoff n x - 1) * f x := by
    funext x
    rw [compactSupportApproximation_apply]
    ring
  rw [heq]
  exact iteratedDeriv_mul
    (((scaledUnitCutoff n).smooth m).sub contDiff_const |>.contDiffAt)
    (f.smooth m |>.contDiffAt)

theorem norm_iteratedDeriv_scaledUnitCutoff_sub_one_le (n i : ℕ) (t : ℝ)
    (hi : i ≠ 0) :
    ‖iteratedDeriv i (fun x : ℝ => scaledUnitCutoff n x - 1) t‖ ≤
      ((n : ℝ) + 1)⁻¹ *
        SchwartzMap.seminorm ℂ 0 i (compactIntervalCutoff 0) := by
  rw [iteratedDeriv_scaledUnitCutoff_sub_one, if_neg hi, norm_smul]
  have hr : 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hri_nonneg : 0 ≤ ((n : ℝ) + 1)⁻¹ := inv_nonneg.mpr (by positivity)
  have hri_le_one : ((n : ℝ) + 1)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hr
  have hpow : ((n : ℝ) + 1)⁻¹ ^ i ≤ ((n : ℝ) + 1)⁻¹ := by
    simpa only [pow_one] using
      pow_le_pow_of_le_one hri_nonneg hri_le_one (Nat.one_le_iff_ne_zero.mpr hi)
  have hbase :
      ‖iteratedDeriv i (compactIntervalCutoff 0) ((((n : ℝ) + 1)⁻¹) * t)‖ ≤
        SchwartzMap.seminorm ℂ 0 i (compactIntervalCutoff 0) := by
    simpa only [pow_zero, one_mul] using
      SchwartzMap.le_seminorm' ℂ 0 i (compactIntervalCutoff 0)
        ((((n : ℝ) + 1)⁻¹) * t)
  rw [Real.norm_of_nonneg (pow_nonneg hri_nonneg i)]
  exact mul_le_mul hpow hbase (norm_nonneg _) hri_nonneg

theorem weighted_cutoff_zero_term_le (n k m : ℕ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    |t| ^ k * ‖(scaledUnitCutoff n t - 1) * iteratedDeriv m f t‖ ≤
      (2 * SchwartzMap.seminorm ℂ (k + 1) m f) / ((n : ℝ) + 1) := by
  have hrpos : 0 < (n : ℝ) + 1 := by positivity
  by_cases ht : |t| ≤ (n : ℝ) + 1
  · rw [scaledUnitCutoff_apply_of_abs_le n ht]
    simp only [sub_self, zero_mul, norm_zero, mul_zero]
    exact div_nonneg (mul_nonneg (by norm_num) (apply_nonneg _ _)) hrpos.le
  · have hrt : (n : ℝ) + 1 ≤ |t| := le_of_lt (lt_of_not_ge ht)
    have htail : |t| ^ k * ‖iteratedDeriv m f t‖ ≤
        SchwartzMap.seminorm ℂ (k + 1) m f / ((n : ℝ) + 1) := by
      rw [le_div_iff₀ hrpos]
      calc
        (|t| ^ k * ‖iteratedDeriv m f t‖) * ((n : ℝ) + 1) =
            (|t| ^ k * ((n : ℝ) + 1)) * ‖iteratedDeriv m f t‖ := by ring
        _ ≤ (|t| ^ k * |t|) * ‖iteratedDeriv m f t‖ := by gcongr
        _ = |t| ^ (k + 1) * ‖iteratedDeriv m f t‖ := by rw [pow_succ]
        _ ≤ SchwartzMap.seminorm ℂ (k + 1) m f :=
          SchwartzMap.le_seminorm' ℂ (k + 1) m f t
    have hdiff : ‖scaledUnitCutoff n t - 1‖ ≤ 2 := by
      calc
        ‖scaledUnitCutoff n t - 1‖ ≤ ‖scaledUnitCutoff n t‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (scaledUnitCutoff_norm_le_one n t) (by norm_num)
        _ = 2 := by norm_num
    calc
      |t| ^ k * ‖(scaledUnitCutoff n t - 1) * iteratedDeriv m f t‖ =
          ‖scaledUnitCutoff n t - 1‖ *
            (|t| ^ k * ‖iteratedDeriv m f t‖) := by rw [norm_mul]; ring
      _ ≤ 2 * (SchwartzMap.seminorm ℂ (k + 1) m f / ((n : ℝ) + 1)) := by
        gcongr
      _ = (2 * SchwartzMap.seminorm ℂ (k + 1) m f) / ((n : ℝ) + 1) := by ring

theorem weighted_cutoff_nonzero_term_le (n k m i : ℕ) (f : SchwartzMap ℝ ℂ) (t : ℝ)
    (hi : i ≠ 0) :
    |t| ^ k *
        ‖iteratedDeriv i (fun x : ℝ => scaledUnitCutoff n x - 1) t *
          iteratedDeriv (m - i) f t‖ ≤
      (SchwartzMap.seminorm ℂ 0 i (compactIntervalCutoff 0) *
        SchwartzMap.seminorm ℂ k (m - i) f) / ((n : ℝ) + 1) := by
  have hcut := norm_iteratedDeriv_scaledUnitCutoff_sub_one_le n i t hi
  have hf := SchwartzMap.le_seminorm' ℂ k (m - i) f t
  rw [norm_mul]
  calc
    |t| ^ k *
        (‖iteratedDeriv i (fun x : ℝ => scaledUnitCutoff n x - 1) t‖ *
          ‖iteratedDeriv (m - i) f t‖) =
        ‖iteratedDeriv i (fun x : ℝ => scaledUnitCutoff n x - 1) t‖ *
          (|t| ^ k * ‖iteratedDeriv (m - i) f t‖) := by ring
    _ ≤ (((n : ℝ) + 1)⁻¹ *
          SchwartzMap.seminorm ℂ 0 i (compactIntervalCutoff 0)) *
        SchwartzMap.seminorm ℂ k (m - i) f := by
      exact mul_le_mul hcut hf (by positivity)
        (mul_nonneg (inv_nonneg.mpr (by positivity)) (apply_nonneg _ _))
    _ = (SchwartzMap.seminorm ℂ 0 i (compactIntervalCutoff 0) *
        SchwartzMap.seminorm ℂ k (m - i) f) / ((n : ℝ) + 1) := by
      rw [div_eq_mul_inv]
      ring

def compactSupportApproximationSeminormBound (k m : ℕ) (f : SchwartzMap ℝ ℂ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
    if i = 0 then 2 * SchwartzMap.seminorm ℂ (k + 1) m f
    else SchwartzMap.seminorm ℂ 0 i (compactIntervalCutoff 0) *
      SchwartzMap.seminorm ℂ k (m - i) f

theorem compactSupportApproximationSeminormBound_nonneg (k m : ℕ)
    (f : SchwartzMap ℝ ℂ) : 0 ≤ compactSupportApproximationSeminormBound k m f := by
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg (by positivity)
  split_ifs
  · exact mul_nonneg (by norm_num) (apply_nonneg _ _)
  · exact mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)

theorem compactSupportApproximation_sub_seminorm_le (n k m : ℕ)
    (f : SchwartzMap ℝ ℂ) :
    SchwartzMap.seminorm ℂ k m (compactSupportApproximation n f - f) ≤
      compactSupportApproximationSeminormBound k m f / ((n : ℝ) + 1) := by
  apply SchwartzMap.seminorm_le_bound' ℂ k m _
    (div_nonneg (compactSupportApproximationSeminormBound_nonneg k m f)
      (show 0 ≤ (n : ℝ) + 1 by positivity))
  intro t
  have hderiv : iteratedDeriv m
      (fun x : ℝ => (compactSupportApproximation n f - f) x) t =
      ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℂ) *
          iteratedDeriv i (fun x : ℝ => scaledUnitCutoff n x - 1) t *
          iteratedDeriv (m - i) f t := by
    exact iteratedDeriv_compactSupportApproximation_sub n m f t
  rw [hderiv]
  calc
    |t| ^ k * ‖∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℂ) *
          iteratedDeriv i (fun x : ℝ => scaledUnitCutoff n x - 1) t *
          iteratedDeriv (m - i) f t‖ ≤
        |t| ^ k * ∑ i ∈ Finset.range (m + 1),
          ‖(m.choose i : ℂ) *
            iteratedDeriv i (fun x : ℝ => scaledUnitCutoff n x - 1) t *
            iteratedDeriv (m - i) f t‖ := by
      gcongr
      exact norm_sum_le _ _
    _ = ∑ i ∈ Finset.range (m + 1), |t| ^ k *
          ‖(m.choose i : ℂ) *
            iteratedDeriv i (fun x : ℝ => scaledUnitCutoff n x - 1) t *
            iteratedDeriv (m - i) f t‖ := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (m + 1),
        ((m.choose i : ℝ) *
          (if i = 0 then 2 * SchwartzMap.seminorm ℂ (k + 1) m f
          else SchwartzMap.seminorm ℂ 0 i (compactIntervalCutoff 0) *
            SchwartzMap.seminorm ℂ k (m - i) f)) / ((n : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hiz : i = 0
      · subst i
        simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, if_pos]
        simpa only [iteratedDeriv_scaledUnitCutoff_sub_one, if_pos, zero_mul,
          Nat.sub_zero] using weighted_cutoff_zero_term_le n k m f t
      · simp only [if_neg hiz]
        rw [norm_mul, norm_mul, norm_natCast]
        calc
          |t| ^ k * ((m.choose i : ℝ) *
              ‖iteratedDeriv i (fun x : ℝ => scaledUnitCutoff n x - 1) t‖ *
              ‖iteratedDeriv (m - i) f t‖) =
              (m.choose i : ℝ) *
                (|t| ^ k *
                  ‖iteratedDeriv i (fun x : ℝ => scaledUnitCutoff n x - 1) t *
                    iteratedDeriv (m - i) f t‖) := by rw [norm_mul]; ring
          _ ≤ (m.choose i : ℝ) *
              ((SchwartzMap.seminorm ℂ 0 i (compactIntervalCutoff 0) *
                SchwartzMap.seminorm ℂ k (m - i) f) / ((n : ℝ) + 1)) := by
            gcongr
            exact weighted_cutoff_nonzero_term_le n k m i f t hiz
          _ = ((m.choose i : ℝ) *
              (SchwartzMap.seminorm ℂ 0 i (compactIntervalCutoff 0) *
                SchwartzMap.seminorm ℂ k (m - i) f)) / ((n : ℝ) + 1) := by ring
    _ = compactSupportApproximationSeminormBound k m f / ((n : ℝ) + 1) := by
      rw [compactSupportApproximationSeminormBound, Finset.sum_div]

theorem tendsto_compactSupportApproximation_sub_seminorm (k m : ℕ)
    (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun n : ℕ =>
      SchwartzMap.seminorm ℂ k m (compactSupportApproximation n f - f))
      atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun n : ℕ =>
      compactSupportApproximationSeminormBound k m f / ((n : ℝ) + 1))
      atTop (𝓝 0) := hden.const_div_atTop _
  exact squeeze_zero
    (fun n => apply_nonneg _ _)
    (fun n => compactSupportApproximation_sub_seminorm_le n k m f)
    hbound

theorem tendsto_compactSupportApproximation (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun n : ℕ => compactSupportApproximation n f) atTop (𝓝 f) := by
  rw [(schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds]
  rintro ⟨k, m⟩ ε hε
  simpa only [schwartzSeminormFamily_apply] using
    (tendsto_compactSupportApproximation_sub_seminorm k m f).eventually
      (Iio_mem_nhds hε)

theorem spectralMeasureForm_fourierPullback_diag_re
    (μ : MeasureTheory.Measure ℝ) [μ.HasTemperateGrowth]
    (f : SchwartzMap ℝ ℂ) :
    ((spectralMeasureForm μ).fourierPullback f f).re =
      ∫ t, pointwiseNormSqReal f t ∂μ := by
  rw [ContinuousSchwartzSesquilinearForm.fourierPullback_apply,
    spectralMeasureForm_apply]
  simp only [FourierTransform.fourier_fourierInv_eq]
  let h : SchwartzMap ℝ ℂ := pointwiseMulConj f f
  have hint : MeasureTheory.Integrable h μ := h.integrable
  change RCLike.re (∫ t, h t ∂μ) = ∫ t, pointwiseNormSqReal f t ∂μ
  rw [← integral_re hint]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  simp [h, pointwiseMulConj_apply, pointwiseNormSqReal_apply, Complex.mul_conj,
    Complex.normSq]

def ContinuousSchwartzSesquilinearForm.compactSpectralRieszForm
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) : ContinuousSchwartzSesquilinearForm :=
  @spectralMeasureForm (Q.compactSpectralRieszMeasure hQ hQnonneg)
    (Q.compactSpectralRieszMeasure_hasTemperateGrowth hQ hQnonneg)

theorem ContinuousSchwartzSesquilinearForm.compactSpectralRieszMeasure_fourierPullback_diag
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) (f : SchwartzMap ℝ ℂ)
    (hf : HasCompactSupport f) :
    (Q.compactSpectralRieszForm hQ hQnonneg).fourierPullback f f =
      Q.fourierPullback f f := by
  let μ := Q.compactSpectralRieszMeasure hQ hQnonneg
  letI : μ.HasTemperateGrowth :=
    Q.compactSpectralRieszMeasure_hasTemperateGrowth hQ hQnonneg
  change (spectralMeasureForm μ).fourierPullback f f = Q.fourierPullback f f
  obtain ⟨B, hB⟩ := hf.isCompact.isBounded.exists_norm_le
  let R : ℝ := max B 0
  have hR : 0 ≤ R := le_max_right _ _
  have hfR : tsupport f ⊆ {t : ℝ | |t| ≤ R} := by
    intro t ht
    have hnorm : ‖t‖ ≤ B := hB t ht
    simpa only [Real.norm_eq_abs] using! hnorm.trans (le_max_left _ _)
  have hreQ := Q.integral_pointwiseNormSqReal_compactSpectralRieszMeasure
    hQ hQnonneg f hR hfR
  have hreM := spectralMeasureForm_fourierPullback_diag_re μ f
  have himQ := (Q.fourierPullback_isNonnegative hQnonneg f).2
  have himM := ((spectralMeasureForm μ).fourierPullback_isNonnegative
    (spectralMeasureForm_isNonnegative μ) f).2
  apply Complex.ext
  · exact hreM.trans hreQ
  · exact himM.trans himQ.symm

theorem ContinuousSchwartzSesquilinearForm.compactSpectralRieszMeasure_fourierPullback_diag_all
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) (f : SchwartzMap ℝ ℂ) :
    (Q.compactSpectralRieszForm hQ hQnonneg).fourierPullback f f =
      Q.fourierPullback f f := by
  let μ := Q.compactSpectralRieszMeasure hQ hQnonneg
  letI : μ.HasTemperateGrowth :=
    Q.compactSpectralRieszMeasure_hasTemperateGrowth hQ hQnonneg
  change (spectralMeasureForm μ).fourierPullback f f = Q.fourierPullback f f
  let A := (spectralMeasureForm μ).fourierPullback
  let fn : ℕ → SchwartzMap ℝ ℂ := fun n => compactSupportApproximation n f
  have hfn : Tendsto fn atTop (𝓝 f) := tendsto_compactSupportApproximation f
  have hA : Tendsto (fun n => A (fn n) (fn n)) atTop (𝓝 (A f f)) :=
    A.tendsto_apply hfn hfn
  have hQlim : Tendsto (fun n => Q.fourierPullback (fn n) (fn n)) atTop
      (𝓝 (Q.fourierPullback f f)) := Q.fourierPullback.tendsto_apply hfn hfn
  have heq : (fun n => A (fn n) (fn n)) =
      fun n => Q.fourierPullback (fn n) (fn n) := by
    funext n
    exact Q.compactSpectralRieszMeasure_fourierPullback_diag hQ hQnonneg (fn n)
      (compactSupportApproximation_hasCompactSupport n f)
  rw [heq] at hA
  exact tendsto_nhds_unique hA hQlim

theorem ContinuousSchwartzSesquilinearForm.eq_of_isHermitian_of_diag_eq
    (A B : ContinuousSchwartzSesquilinearForm)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hdiag : ∀ f, A f f = B f f) : A = B := by
  have hfun : A.toFun = B.toFun := by
    funext u v
    have hplus := hdiag (u + v)
    have hI := hdiag (u + Complex.I • v)
    have huu := hdiag u
    have hvv := hdiag v
    have hAh := hA u v
    have hBh := hB u v
    simp only [ContinuousSchwartzSesquilinearForm.apply_add_left,
      ContinuousSchwartzSesquilinearForm.apply_add_right,
      ContinuousSchwartzSesquilinearForm.apply_smul_left,
      ContinuousSchwartzSesquilinearForm.apply_smul_right] at hplus hI
    rw [huu, hvv, hAh, hBh] at hplus hI
    apply Complex.ext
    · norm_num [Complex.ext_iff, Complex.add_re, Complex.mul_re,
        Complex.conj_re, Complex.conj_im] at hplus hI ⊢
      linarith
    · norm_num [Complex.ext_iff, Complex.add_im, Complex.mul_im,
        Complex.conj_re, Complex.conj_im] at hplus hI ⊢
      linarith
  cases A
  cases B
  simp only at hfun
  cases hfun
  rfl

theorem ContinuousSchwartzSesquilinearForm.compactSpectralRieszForm_eq
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) :
    Q.compactSpectralRieszForm hQ hQnonneg = Q := by
  let μ := Q.compactSpectralRieszMeasure hQ hQnonneg
  letI : μ.HasTemperateGrowth :=
    Q.compactSpectralRieszMeasure_hasTemperateGrowth hQ hQnonneg
  change spectralMeasureForm μ = Q
  apply ContinuousSchwartzSesquilinearForm.eq_of_isHermitian_of_diag_eq
  · exact spectralMeasureForm_isHermitian μ
  · exact Q.isHermitian_of_isNonnegative hQnonneg
  · intro u
    have hdiag := Q.compactSpectralRieszMeasure_fourierPullback_diag_all hQ hQnonneg
      ((fourierTransformCLM ℂ) u)
    change (spectralMeasureForm μ).fourierPullback ((fourierTransformCLM ℂ) u)
        ((fourierTransformCLM ℂ) u) =
      Q.fourierPullback ((fourierTransformCLM ℂ) u) ((fourierTransformCLM ℂ) u) at hdiag
    simpa only [ContinuousSchwartzSesquilinearForm.fourierPullback_apply,
      fourierTransformCLM_apply, FourierTransform.fourierInv_fourier_eq] using hdiag

theorem temperateGrowthIsFiniteMeasureOnCompacts
    (μ : Measure ℝ) [μ.HasTemperateGrowth] : IsFiniteMeasureOnCompacts μ where
  lt_top_of_isCompact K hK := by
    let n := μ.integrablePower
    let w : ℝ → ℝ := fun x => (1 + ‖x‖) ^ (-(n : ℝ))
    have hwint : Integrable w μ := μ.integrable_pow_neg_integrablePower
    have hwcont : Continuous w := by
      dsimp [w]
      apply Continuous.rpow (by fun_prop) continuous_const
      intro x
      left
      positivity
    have hwpos : ∀ x, 0 < w x := by
      intro x
      exact Real.rpow_pos_of_pos (by positivity) _
    obtain ⟨c, hcpos, hc⟩ := hK.exists_forall_le' hwcont.continuousOn
      (fun x hx => hwpos x)
    let g : ℝ → ℝ := fun x => c⁻¹ * w x
    have hgint : Integrable g μ := hwint.const_mul c⁻¹
    have hnonneg : 0 ≤ᵐ[μ] g := Filter.Eventually.of_forall (fun x => by
      exact mul_nonneg (inv_nonneg.mpr hcpos.le) (hwpos x).le)
    have hge : ∀ x ∈ K, 1 ≤ g x := by
      intro x hx
      dsimp [g]
      rw [← div_eq_inv_mul, le_div_iff₀ hcpos]
      simpa using hc x hx
    exact (hgint.measure_le_integral hnonneg hge).trans_lt ENNReal.ofReal_lt_top

theorem CompactContinuousSchwartzApproximation.tendsto_integral
    {f : C_c(ℝ, ℝ)} (A : CompactContinuousSchwartzApproximation f)
    (μ : Measure ℝ) [μ.HasTemperateGrowth] :
    Tendsto (fun n => ∫ t, A.seq n t ∂μ) atTop (𝓝 (∫ t, f t ∂μ)) := by
  letI : IsFiniteMeasureOnCompacts μ := temperateGrowthIsFiniteMeasureOnCompacts μ
  let K : Set ℝ := tsupport f ∪ Set.Icc (-A.radius) A.radius
  have hK : IsCompact K := f.hasCompactSupport.isCompact.union isCompact_Icc
  have hKmeas : MeasurableSet K := hK.measurableSet
  have hμK : μ K < ⊤ := hK.measure_lt_top
  have hfint : Integrable f μ := f.integrable
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / (μ.real K + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hAu := A.tendsto_uniform δ hδ
  rw [eventually_atTop] at hAu
  obtain ⟨N, hN⟩ := hAu
  refine ⟨N, ?_⟩
  intro n hn
  have hseqint : Integrable (A.seq n) μ := (A.seq n).integrable
  have hdiffzero : ∀ x ∉ K, A.seq n x - f x = 0 := by
    intro x hx
    have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hxf => hx (Or.inl hxf))
    have hseqx : A.seq n x = 0 := image_eq_zero_of_notMem_tsupport (fun hxs => by
      have habs := A.seq_tsupport n hxs
      apply hx
      right
      exact ⟨neg_le_of_abs_le habs, le_of_abs_le habs⟩)
    rw [hseqx, hfx, sub_self]
  have hindicator : K.indicator (fun x => A.seq n x - f x) =
      fun x => A.seq n x - f x := by
    funext x
    by_cases hx : x ∈ K
    · simp [hx]
    · simp [hx, hdiffzero x hx]
  have hset : (∫ x, A.seq n x - f x ∂μ) = ∫ x in K, A.seq n x - f x ∂μ := by
    rw [← integral_indicator hKmeas, hindicator]
  rw [Real.dist_eq, ← integral_sub hseqint hfint, hset, ← Real.norm_eq_abs]
  calc
    ‖∫ x in K, A.seq n x - f x ∂μ‖ ≤ δ * μ.real K := by
      apply norm_setIntegral_le_of_norm_le_const hμK
      intro x hx
      simpa only [Real.norm_eq_abs] using (hN n hn x).le
    _ < ε := by
      have hm : 0 ≤ μ.real K := ENNReal.toReal_nonneg
      have hfrac : μ.real K / (μ.real K + 1) < 1 :=
        (div_lt_one (by positivity)).mpr (by linarith)
      calc
        δ * μ.real K = ε * (μ.real K / (μ.real K + 1)) := by
          dsimp [δ]
          ring
        _ < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
        _ = ε := mul_one _

theorem CompactContinuousSchwartzApproximation.diagonalSequence_spectralMeasureForm
    {f : C_c(ℝ, ℝ)} (A : CompactContinuousSchwartzApproximation f)
    (μ : Measure ℝ) [μ.HasTemperateGrowth] (n : ℕ) :
    A.diagonalSequence (spectralMeasureForm μ) n = ∫ t, A.seq n t ∂μ := by
  rw [CompactContinuousSchwartzApproximation.diagonalSequence,
    ContinuousSchwartzSesquilinearForm.compactIntervalDiagonalFunctional_apply,
    ContinuousSchwartzSesquilinearForm.fourierPullback_apply,
    spectralMeasureForm_apply]
  simp only [FourierTransform.fourier_fourierInv_eq]
  let h : SchwartzMap ℝ ℂ := pointwiseMulConj
    (realToComplexSchwartz (A.seq n)) (compactIntervalCutoff (A.radius + 4))
  have hint : Integrable h μ := h.integrable
  change RCLike.re (∫ t, h t ∂μ) = ∫ t, A.seq n t ∂μ
  rw [← integral_re hint]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ tsupport (A.seq n)
  · have habs : |t| ≤ A.radius := A.seq_tsupport n ht
    have hcut : compactIntervalCutoff (A.radius + 4) t = 1 := by
      apply compactIntervalCutoff_apply_of_abs_le
      have hRabs : |A.radius + 4| = A.radius + 4 :=
        abs_of_nonneg (by linarith [A.radius_nonneg])
      rw [hRabs]
      linarith
    simp [h, pointwiseMulConj_apply, realToComplexSchwartz_apply, hcut]
  · have hz : A.seq n t = 0 := image_eq_zero_of_notMem_tsupport ht
    simp [h, pointwiseMulConj_apply, realToComplexSchwartz_apply, hz]

theorem compactSpectralRieszMeasure_spectralMeasureForm
    (μ : Measure ℝ) [μ.HasTemperateGrowth] :
    let Q := spectralMeasureForm μ
    Q.compactSpectralRieszMeasure (spectralMeasureForm_momentumSymmetric μ)
      (spectralMeasureForm_isNonnegative μ) = μ := by
  letI : IsFiniteMeasureOnCompacts μ := temperateGrowthIsFiniteMeasureOnCompacts μ
  dsimp only
  let Q := spectralMeasureForm μ
  let hQ := spectralMeasureForm_momentumSymmetric μ
  let hQnonneg := spectralMeasureForm_isNonnegative μ
  letI : (Q.compactSpectralRieszMeasure hQ hQnonneg).Regular := by
    change (RealRMK.rieszMeasure _).Regular
    infer_instance
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [Q.integral_compactSpectralRieszMeasure hQ hQnonneg]
  let A := chosenCompactContinuousSchwartzApproximation f
  rw [Q.compactContinuousDiagonalValue_eq hQ hQnonneg A]
  apply tendsto_nhds_unique (A.tendsto_diagonalLimit Q hQ hQnonneg)
  have hint := A.tendsto_integral μ
  apply Tendsto.congr' _ hint
  filter_upwards with n
  exact (A.diagonalSequence_spectralMeasureForm μ n).symm

theorem ContinuousSchwartzSesquilinearForm.compactSpectralRieszMeasure_congr
    {Q R : ContinuousSchwartzSesquilinearForm} (h : Q = R)
    (hQ : Q.MomentumSymmetric) (hQnonneg : Q.IsNonnegative)
    (hR : R.MomentumSymmetric) (hRnonneg : R.IsNonnegative) :
    Q.compactSpectralRieszMeasure hQ hQnonneg =
      R.compactSpectralRieszMeasure hR hRnonneg := by
  subst R
  rfl

theorem spectralMeasureForm_eq_iff_measure_eq
    (μ ν : Measure ℝ) [μ.HasTemperateGrowth] [ν.HasTemperateGrowth] :
    spectralMeasureForm μ = spectralMeasureForm ν ↔ μ = ν := by
  constructor
  · intro hforms
    calc
      μ = (spectralMeasureForm μ).compactSpectralRieszMeasure
          (spectralMeasureForm_momentumSymmetric μ)
          (spectralMeasureForm_isNonnegative μ) :=
        (compactSpectralRieszMeasure_spectralMeasureForm μ).symm
      _ = (spectralMeasureForm ν).compactSpectralRieszMeasure
          (spectralMeasureForm_momentumSymmetric ν)
          (spectralMeasureForm_isNonnegative ν) := by
        exact ContinuousSchwartzSesquilinearForm.compactSpectralRieszMeasure_congr hforms
          _ _ _ _
      _ = ν := compactSpectralRieszMeasure_spectralMeasureForm ν
  · rintro rfl
    rfl

/-- A positive measure of temperate growth represents `Q` on the Fourier side. -/
def TemperateSpectralRepresentation
    (Q : ContinuousSchwartzSesquilinearForm) (μ : Measure ℝ) : Prop :=
  ∃ hμ : μ.HasTemperateGrowth, Q = @spectralMeasureForm μ hμ

/-- Every nonnegative momentum-symmetric continuous Schwartz form has exactly one
positive temperate spectral measure. -/
theorem existsUnique_temperateSpectralRepresentation
    (Q : ContinuousSchwartzSesquilinearForm)
    (hQ : Q.MomentumSymmetric) (hQnonneg : Q.IsNonnegative) :
    ∃! μ : Measure ℝ, TemperateSpectralRepresentation Q μ := by
  let μ := Q.compactSpectralRieszMeasure hQ hQnonneg
  have hμ : μ.HasTemperateGrowth :=
    Q.compactSpectralRieszMeasure_hasTemperateGrowth hQ hQnonneg
  refine ⟨μ, ⟨hμ, ?_⟩, ?_⟩
  · exact (Q.compactSpectralRieszForm_eq hQ hQnonneg).symm
  · intro ν hν
    rcases hν with ⟨hνtemp, hνrep⟩
    letI : μ.HasTemperateGrowth := hμ
    letI : ν.HasTemperateGrowth := hνtemp
    apply (spectralMeasureForm_eq_iff_measure_eq ν μ).mp
    exact hνrep.symm.trans
      (Q.compactSpectralRieszForm_eq hQ hQnonneg).symm

end SchwartzMap
