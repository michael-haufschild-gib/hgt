import GaloisForLFunctions.RHTower.FourierPlancherelIntegral
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaEsscherResolventFrame

/-!
# Resolvent-frame Plancherel law for the theta source

The all-complex source-character row on one horizontal line is the ordinary Fourier transform
of an Esscher-tilted source vector.  Plancherel therefore identifies its total row energy with
the physical source energy.  At zero tilt this is exactly the canonical singular metric form.

This exposes a structural loss mechanism: determinant weighting cancels the scalar resolvent
denominator before Fourier synthesis, so every resulting positive quadratic completion sees the
source metric but forgets zero orientation.
-/

open Complex MeasureTheory Set FourierTransform

namespace RHTower.HedenmalmThetaSource

noncomputable section

open GaloisForLFunctions.HTGeometry HedenmalmQuantile

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-- Physical source profile associated with an Esscher line. -/
def thetaEsscherSourceProfile (h : ℝ) (u : SourceSpace thetaSource) (x : ℝ) : ℂ :=
  (Real.exp (h * x) : ℂ) * (u x : ℂ) / (Real.sqrt thetaSource.mass : ℂ)

/-- Every theta source vector is square-integrable for ordinary Lebesgue measure.  Boundedness of
the theta density makes the unweighted norm weaker than the defining reciprocal-density norm. -/
theorem memLp_two_sourceSpace_volume (u : SourceSpace thetaSource) :
    MemLp (fun x => (u x : ℂ)) 2 (volume : Measure ℝ) := by
  have hu : AEStronglyMeasurable (fun x => (u x : ℂ)) (volume : Measure ℝ) :=
    (aestronglyMeasurable_withDensity_realDensity_iff
      (measurable_sourceWeight thetaSource) (sourceWeight_pos thetaSource)).mp
      (Lp.aestronglyMeasurable u)
  have hweighted : MemLp
      (fun x => sqrtWeight (sourceWeight thetaSource) x * (u x : ℂ)) 2
      (volume : Measure ℝ) :=
    (memLp_two_withDensity_iff
      (measurable_sourceWeight thetaSource) (sourceWeight_pos thetaSource)).mp
      (Lp.memLp u)
  have hB : 0 < thetaBound :=
    lt_of_lt_of_le (thetaSource.pos_k 0) (thetaSource_le 0)
  refine MemLp.of_le_mul (c := Real.sqrt thetaBound) hweighted hu ?_
  filter_upwards with x
  have hk : 0 < thetaSource.k x := thetaSource.pos_k x
  have hsqrt : Real.sqrt (thetaSource.k x) ≤ Real.sqrt thetaBound :=
    Real.sqrt_le_sqrt (thetaSource_le x)
  have hsw : sqrtWeight (sourceWeight thetaSource) x =
      (((Real.sqrt (thetaSource.k x))⁻¹ : ℝ) : ℂ) := by
    rw [sqrtWeight]
    norm_cast
    rw [show sourceWeight thetaSource x = (thetaSource.k x)⁻¹ from rfl, Real.sqrt_inv]
  have hsqrtne : Real.sqrt (thetaSource.k x) ≠ 0 :=
    (Real.sqrt_pos.mpr hk).ne'
  have hsqrtnec : ((Real.sqrt (thetaSource.k x) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrtne
  have hrecover : ((Real.sqrt (thetaSource.k x) : ℝ) : ℂ) *
      (sqrtWeight (sourceWeight thetaSource) x * (u x : ℂ)) = (u x : ℂ) := by
    rw [hsw]
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ hsqrtnec, one_mul]
  calc
    ‖(u x : ℂ)‖ =
        ‖((Real.sqrt (thetaSource.k x) : ℝ) : ℂ) *
          (sqrtWeight (sourceWeight thetaSource) x * (u x : ℂ))‖ := by
      rw [hrecover]
    _ = Real.sqrt (thetaSource.k x) *
        ‖sqrtWeight (sourceWeight thetaSource) x * (u x : ℂ)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ Real.sqrt thetaBound *
        ‖sqrtWeight (sourceWeight thetaSource) x * (u x : ℂ)‖ :=
      mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)

theorem integrable_thetaEsscherSourceProfile_zero (u : SourceSpace thetaSource) :
    Integrable (thetaEsscherSourceProfile 0 u) (volume : Measure ℝ) := by
  have h := (integrable_sourceSpace thetaSource u).const_mul
    ((Real.sqrt thetaSource.mass : ℂ)⁻¹)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [thetaEsscherSourceProfile, div_eq_mul_inv, mul_comm]

theorem memLp_two_thetaEsscherSourceProfile_zero (u : SourceSpace thetaSource) :
    MemLp (thetaEsscherSourceProfile 0 u) 2 (volume : Measure ℝ) := by
  have h := (memLp_two_sourceSpace_volume u).const_mul
    ((Real.sqrt thetaSource.mass : ℂ)⁻¹)
  apply MemLp.ae_eq (g := thetaEsscherSourceProfile 0 u)
    (Filter.Eventually.of_forall fun x => ?_) h
  simp [thetaEsscherSourceProfile, div_eq_mul_inv, mul_comm]

/-- Zero-tilt physical energy is the ordinary source energy divided by total theta mass. -/
theorem integral_norm_sq_thetaEsscherSourceProfile_zero (u : SourceSpace thetaSource) :
    (∫ x : ℝ, ‖thetaEsscherSourceProfile 0 u x‖ ^ (2 : ℕ)) =
      (∫ x : ℝ, ‖(u x : ℂ)‖ ^ (2 : ℕ)) / thetaSource.mass := by
  rw [← MeasureTheory.integral_div]
  apply integral_congr_ae
  filter_upwards with x
  rw [thetaEsscherSourceProfile, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul,
    norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow,
    Real.sq_sqrt thetaSource.mass_pos.le]

/-- The source-character moment of a quantile vector is the Fourier transform of its physical
Esscher profile, with the exact `2*pi` frequency conversion. -/
theorem thetaComplexResolventMoment_quantileUnitary_eq_fourier
    (h tau : ℝ) (u : SourceSpace thetaSource) :
    thetaComplexResolventMoment (thetaEsscherResolventParameter h tau)
        (quantileUnitary thetaSource u) =
      𝓕 (thetaEsscherSourceProfile h u) (tau / (2 * Real.pi)) := by
  have hu : AEStronglyMeasurable (fun x => (u x : ℂ)) (volume : Measure ℝ) :=
    (aestronglyMeasurable_withDensity_realDensity_iff
      (measurable_sourceWeight thetaSource) (sourceWeight_pos thetaSource)).mp
      (Lp.aestronglyMeasurable u)
  have hsource : AEStronglyMeasurable
      (fun x => sourceChar (thetaEsscherResolventParameter h tau) x * (u x : ℂ))
      (volume : Measure ℝ) :=
    (continuous_sourceChar (thetaEsscherResolventParameter h tau)).aestronglyMeasurable.mul hu
  rw [thetaComplexResolventMoment]
  calc
    (∫ t,
        sourceChar (thetaEsscherResolventParameter h tau) (thetaSource.quantileFun t) *
          quantileUnitary thetaSource u t ∂unitIntervalMeasure) =
        ∫ t,
          quantileTransform thetaSource
            (fun x => sourceChar (thetaEsscherResolventParameter h tau) x * (u x : ℂ)) t
            ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [quantileUnitary_ae thetaSource u] with t ht
      rw [ht]
      unfold quantileTransform
      ring
    _ = ∫ t in Ioo (0 : ℝ) 1,
          quantileTransform thetaSource
            (fun x => sourceChar (thetaEsscherResolventParameter h tau) x * (u x : ℂ)) t := by
      rw [unitIntervalMeasure_eq]
    _ = (∫ x, sourceChar (thetaEsscherResolventParameter h tau) x * (u x : ℂ)) /
          (Real.sqrt thetaSource.mass : ℂ) :=
      integral_quantileTransform thetaSource hsource
    _ = 𝓕 (thetaEsscherSourceProfile h u) (tau / (2 * Real.pi)) := by
      rw [Real.fourier_real_eq]
      rw [← integral_div]
      apply integral_congr_ae
      filter_upwards with x
      change sourceChar (thetaEsscherResolventParameter h tau) x * (u x : ℂ) /
          (Real.sqrt thetaSource.mass : ℂ) =
        (Real.fourierChar (-(x * (tau / (2 * Real.pi)))) : ℂ) *
          thetaEsscherSourceProfile h u x
      rw [Real.fourierChar_apply]
      unfold thetaEsscherSourceProfile sourceChar thetaEsscherResolventParameter
      have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      have harg : ((2 * Real.pi * (-(x * (tau / (2 * Real.pi)))) : ℝ) : ℂ) =
          -((x : ℂ) * (tau : ℂ)) := by
        push_cast
        field_simp
      rw [harg, Complex.ofReal_exp]
      have hexp :
          Complex.exp (Complex.I *
              (-(tau : ℂ) - (h : ℂ) * Complex.I) * (x : ℂ)) =
            Complex.exp (-((x : ℂ) * (tau : ℂ)) * Complex.I) *
              Complex.exp (((h * x : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [hexp]
      ring

/-- Plancherel synthesis of one Esscher moment line. -/
theorem integral_norm_sq_thetaComplexResolventMoment_quantileUnitary
    (h : ℝ) (u : SourceSpace thetaSource)
    (hL1 : Integrable (thetaEsscherSourceProfile h u) (volume : Measure ℝ))
    (hL2 : MemLp (thetaEsscherSourceProfile h u) 2 (volume : Measure ℝ)) :
    (∫ tau : ℝ,
        ‖thetaComplexResolventMoment (thetaEsscherResolventParameter h tau)
          (quantileUnitary thetaSource u)‖ ^ (2 : ℕ)) =
      2 * Real.pi * ∫ x : ℝ, ‖thetaEsscherSourceProfile h u x‖ ^ (2 : ℕ) := by
  have hline : (fun tau : ℝ =>
      ‖thetaComplexResolventMoment (thetaEsscherResolventParameter h tau)
        (quantileUnitary thetaSource u)‖ ^ (2 : ℕ)) =
      fun tau : ℝ => ‖𝓕 (thetaEsscherSourceProfile h u)
        (tau / (2 * Real.pi))‖ ^ (2 : ℕ) := by
    funext tau
    rw [thetaComplexResolventMoment_quantileUnitary_eq_fourier]
  rw [hline]
  let H : ℝ → ℝ := fun xi => ‖𝓕 (thetaEsscherSourceProfile h u) xi‖ ^ (2 : ℕ)
  have hscale := MeasureTheory.Measure.integral_comp_div H (2 * Real.pi)
  rw [hscale, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  simp only [smul_eq_mul]
  rw [GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq hL1 hL2]

/-- **Polarized Plancherel synthesis.**  The complete complex cross-pairing of two critical
source-character rows is the physical source cross-pairing.  Thus retaining off-diagonal Gram
terms does not repair the phase loss caused by determinant weighting. -/
theorem integral_conj_mul_criticalMoment_eq_sourcePairing
    (u v : SourceSpace thetaSource) :
    (∫ tau : ℝ,
        (starRingEnd ℂ)
            (thetaComplexResolventMoment (thetaEsscherResolventParameter 0 tau)
              (quantileUnitary thetaSource u)) *
          thetaComplexResolventMoment (thetaEsscherResolventParameter 0 tau)
            (quantileUnitary thetaSource v)) =
      (2 * Real.pi : ℝ) •
        ∫ x : ℝ,
          (starRingEnd ℂ) (thetaEsscherSourceProfile 0 u x) *
            thetaEsscherSourceProfile 0 v x := by
  let fu : Lp ℂ 2 (volume : Measure ℝ) :=
    (memLp_two_thetaEsscherSourceProfile_zero u).toLp
      (thetaEsscherSourceProfile 0 u)
  let fv : Lp ℂ 2 (volume : Measure ℝ) :=
    (memLp_two_thetaEsscherSourceProfile_zero v).toLp
      (thetaEsscherSourceProfile 0 v)
  have hfuAE : ((𝓕 fu : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      𝓕 (thetaEsscherSourceProfile 0 u) := by
    exact GaloisForLFunctions.RHTower.coeFn_fourier_toLp
      (integrable_thetaEsscherSourceProfile_zero u)
      (memLp_two_thetaEsscherSourceProfile_zero u)
  have hfvAE : ((𝓕 fv : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      𝓕 (thetaEsscherSourceProfile 0 v) := by
    exact GaloisForLFunctions.RHTower.coeFn_fourier_toLp
      (integrable_thetaEsscherSourceProfile_zero v)
      (memLp_two_thetaEsscherSourceProfile_zero v)
  have hfuSource : ((fu : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      thetaEsscherSourceProfile 0 u :=
    (memLp_two_thetaEsscherSourceProfile_zero u).coeFn_toLp
  have hfvSource : ((fv : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      thetaEsscherSourceProfile 0 v :=
    (memLp_two_thetaEsscherSourceProfile_zero v).coeFn_toLp
  let H : ℝ → ℂ := fun xi =>
    (starRingEnd ℂ) (𝓕 (thetaEsscherSourceProfile 0 u) xi) *
      𝓕 (thetaEsscherSourceProfile 0 v) xi
  have hscale := MeasureTheory.Measure.integral_comp_div H (2 * Real.pi)
  have hfrequency :
      (∫ xi : ℝ, H xi) =
        ∫ x : ℝ,
          (starRingEnd ℂ) (thetaEsscherSourceProfile 0 u x) *
            thetaEsscherSourceProfile 0 v x := by
    calc
      (∫ xi : ℝ, H xi) =
          ∫ xi : ℝ,
            inner ℂ ((𝓕 fu : Lp ℂ 2 (volume : Measure ℝ)) xi)
              ((𝓕 fv : Lp ℂ 2 (volume : Measure ℝ)) xi) := by
        apply integral_congr_ae
        filter_upwards [hfuAE, hfvAE] with xi hui hvi
        rw [RCLike.inner_apply, hui, hvi]
        ring
      _ = inner ℂ (𝓕 fu : Lp ℂ 2 (volume : Measure ℝ))
          (𝓕 fv : Lp ℂ 2 (volume : Measure ℝ)) := by
        rw [MeasureTheory.L2.inner_def]
      _ = inner ℂ fu fv := by rw [Lp.inner_fourier_eq]
      _ = ∫ x : ℝ,
          (starRingEnd ℂ) (thetaEsscherSourceProfile 0 u x) *
            thetaEsscherSourceProfile 0 v x := by
        rw [MeasureTheory.L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hfuSource, hfvSource] with x hux hvx
        rw [RCLike.inner_apply, hux, hvx]
        ring
  have hline : (fun tau : ℝ =>
      (starRingEnd ℂ)
          (thetaComplexResolventMoment (thetaEsscherResolventParameter 0 tau)
            (quantileUnitary thetaSource u)) *
        thetaComplexResolventMoment (thetaEsscherResolventParameter 0 tau)
          (quantileUnitary thetaSource v)) = fun tau : ℝ => H (tau / (2 * Real.pi)) := by
    funext tau
    rw [thetaComplexResolventMoment_quantileUnitary_eq_fourier,
      thetaComplexResolventMoment_quantileUnitary_eq_fourier]
  rw [hline, hscale, abs_of_pos (mul_pos (by norm_num) Real.pi_pos), hfrequency]

/-- Determinant weighting cancels the scalar resolvent denominator pointwise on every exterior
line.  This is the precise algebraic source of divisor blindness in positive row energies. -/
theorem norm_rootA_sq_mul_norm_pinnedMean_resolvent_sq
    {h : ℝ} (hh : 1 / 2 ≤ |h|) (tau : ℝ) (u : SourceSpace thetaSource) :
    ‖rootA thetaSource (thetaEsscherResolventParameter h tau) 1‖ ^ (2 : ℕ) *
        ‖pinnedMean
          (thetaComplexResolvent (thetaEsscherResolventParameter h tau)
            (quantileUnitary thetaSource u))‖ ^ (2 : ℕ) =
      ‖thetaComplexResolventMoment (thetaEsscherResolventParameter h tau)
        (quantileUnitary thetaSource u)‖ ^ (2 : ℕ) := by
  have hz :=
    isUnit_thetaSourcePencil_thetaEsscherResolventParameter_of_half_le_abs hh tau
  have hA : rootA thetaSource (thetaEsscherResolventParameter h tau) 1 ≠ 0 :=
    rootA_one_ne_zero_of_sourcePencil_isUnit hz
  rw [pinnedMean_thetaComplexResolvent_eq hz, norm_div, div_pow]
  field_simp [norm_ne_zero_iff.mpr hA]

/-- Full polarized cancellation: even complex cross-Gram data loses the scalar divisor after
determinant weighting.  No diagonalization or absolute value is used here. -/
theorem norm_rootA_sq_mul_conj_pinnedMean_mul_pinnedMean
    {h : ℝ} (hh : 1 / 2 ≤ |h|) (tau : ℝ) (u v : SourceSpace thetaSource) :
    ((‖rootA thetaSource (thetaEsscherResolventParameter h tau) 1‖ ^ (2 : ℕ) : ℝ) : ℂ) *
        (starRingEnd ℂ)
          (pinnedMean
            (thetaComplexResolvent (thetaEsscherResolventParameter h tau)
              (quantileUnitary thetaSource u))) *
        pinnedMean
          (thetaComplexResolvent (thetaEsscherResolventParameter h tau)
            (quantileUnitary thetaSource v)) =
      (starRingEnd ℂ)
          (thetaComplexResolventMoment (thetaEsscherResolventParameter h tau)
            (quantileUnitary thetaSource u)) *
        thetaComplexResolventMoment (thetaEsscherResolventParameter h tau)
          (quantileUnitary thetaSource v) := by
  have hz :=
    isUnit_thetaSourcePencil_thetaEsscherResolventParameter_of_half_le_abs hh tau
  let A : ℂ := rootA thetaSource (thetaEsscherResolventParameter h tau) 1
  have hA : A ≠ 0 := rootA_one_ne_zero_of_sourcePencil_isUnit hz
  have hstarA : (starRingEnd ℂ) A ≠ 0 := by simpa using hA
  rw [pinnedMean_thetaComplexResolvent_eq hz,
    pinnedMean_thetaComplexResolvent_eq hz, map_div₀]
  change ((‖A‖ ^ (2 : ℕ) : ℝ) : ℂ) *
      ((starRingEnd ℂ)
          (thetaComplexResolventMoment (thetaEsscherResolventParameter h tau)
            (quantileUnitary thetaSource u)) /
        (starRingEnd ℂ) A) *
      (thetaComplexResolventMoment (thetaEsscherResolventParameter h tau)
          (quantileUnitary thetaSource v) / A) = _
  rw [← HedenmalmQuantile.conj_mul_self]
  field_simp [hA, hstarA]

/-- **Exterior determinant-weighted resolvent-frame synthesis.**  Whenever the tilted physical
profile lies in `L¹ ∩ L²`, its total determinant-weighted resolvent-row energy is exactly its
physical Plancherel energy. -/
theorem integral_detWeighted_resolventRow_eq_sourceEnergy
    {h : ℝ} (hh : 1 / 2 ≤ |h|) (u : SourceSpace thetaSource)
    (hL1 : Integrable (thetaEsscherSourceProfile h u) (volume : Measure ℝ))
    (hL2 : MemLp (thetaEsscherSourceProfile h u) 2 (volume : Measure ℝ)) :
    (∫ tau : ℝ,
        ‖rootA thetaSource (thetaEsscherResolventParameter h tau) 1‖ ^ (2 : ℕ) *
          ‖pinnedMean
            (thetaComplexResolvent (thetaEsscherResolventParameter h tau)
              (quantileUnitary thetaSource u))‖ ^ (2 : ℕ)) =
      2 * Real.pi * ∫ x : ℝ, ‖thetaEsscherSourceProfile h u x‖ ^ (2 : ℕ) := by
  calc
    (∫ tau : ℝ,
        ‖rootA thetaSource (thetaEsscherResolventParameter h tau) 1‖ ^ (2 : ℕ) *
          ‖pinnedMean
            (thetaComplexResolvent (thetaEsscherResolventParameter h tau)
              (quantileUnitary thetaSource u))‖ ^ (2 : ℕ)) =
        ∫ tau : ℝ,
          ‖thetaComplexResolventMoment (thetaEsscherResolventParameter h tau)
            (quantileUnitary thetaSource u)‖ ^ (2 : ℕ) := by
      apply integral_congr_ae
      filter_upwards with tau
      exact norm_rootA_sq_mul_norm_pinnedMean_resolvent_sq hh tau u
    _ = 2 * Real.pi * ∫ x : ℝ, ‖thetaEsscherSourceProfile h u x‖ ^ (2 : ℕ) :=
      integral_norm_sq_thetaComplexResolventMoment_quantileUnitary h u hL1 hL2

/-- **Unconditional metric synthesis.**  Total critical-line source-character row energy is
exactly `2*pi` times the canonical singular metric quadratic form. -/
theorem integral_norm_sq_criticalMoment_eq_thetaMetric
    (u : SourceSpace thetaSource) :
    (∫ tau : ℝ,
        ‖thetaComplexResolventMoment (thetaEsscherResolventParameter 0 tau)
          (quantileUnitary thetaSource u)‖ ^ (2 : ℕ)) =
      2 * Real.pi *
        (inner ℂ (thetaMetricOperator (quantileUnitary thetaSource u))
          (quantileUnitary thetaSource u) : ℂ).re := by
  have hmetric := congrArg Complex.re
    (inner_thetaMetricOperator_quantileUnitary u)
  have hmetricReal :
      (inner ℂ (thetaMetricOperator (quantileUnitary thetaSource u))
        (quantileUnitary thetaSource u) : ℂ).re =
        (∫ x : ℝ, ‖(u x : ℂ)‖ ^ (2 : ℕ)) / thetaSource.mass := by
    simpa using hmetric
  calc
    (∫ tau : ℝ,
        ‖thetaComplexResolventMoment (thetaEsscherResolventParameter 0 tau)
          (quantileUnitary thetaSource u)‖ ^ (2 : ℕ)) =
        2 * Real.pi * ∫ x : ℝ, ‖thetaEsscherSourceProfile 0 u x‖ ^ (2 : ℕ) :=
      integral_norm_sq_thetaComplexResolventMoment_quantileUnitary 0 u
        (integrable_thetaEsscherSourceProfile_zero u)
        (memLp_two_thetaEsscherSourceProfile_zero u)
    _ = 2 * Real.pi * ((∫ x : ℝ, ‖(u x : ℂ)‖ ^ (2 : ℕ)) / thetaSource.mass) := by
      rw [integral_norm_sq_thetaEsscherSourceProfile_zero]
    _ = 2 * Real.pi *
        (inner ℂ (thetaMetricOperator (quantileUnitary thetaSource u))
          (quantileUnitary thetaSource u) : ℂ).re := by
      rw [hmetricReal]

end

end RHTower.HedenmalmThetaSource
