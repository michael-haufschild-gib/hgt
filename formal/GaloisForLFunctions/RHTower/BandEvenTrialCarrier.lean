import GaloisForLFunctions.RHTower.BandKaiserL2Trial

/-!
# Generic continuous even trials in the physical `L²` carrier

Analytic concentration estimates are most naturally proved for a continuous even function on the
normalized interval `[-1,1]`.  This module packages its zero extension as an element of the actual
complex even `L²(ℝ)` carrier and records the exact norm, Fourier-tail, and physical-dilation
identities.  It removes the need to rebuild this measure-theoretic bridge for each sharp trial.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

open GaloisForLFunctions.RHTower

/-- Zero extension of a continuous normalized trial as an `L²(ℝ)` class. -/
def continuousEvenBandL2 (psi : ℝ → ℝ) (hpsi : Continuous psi) : SoninL2 :=
  (memLp_bandTrunc hpsi 2).toLp (bandTrunc psi)

theorem continuousEvenBandL2_coeFn (psi : ℝ → ℝ) (hpsi : Continuous psi) :
    (continuousEvenBandL2 psi hpsi : ℝ → ℂ) =ᵐ[volume] bandTrunc psi :=
  (memLp_bandTrunc hpsi 2).coeFn_toLp

theorem bandTrunc_even_of_even {psi : ℝ → ℝ} (heven : Function.Even psi) (x : ℝ) :
    bandTrunc psi (-x) = bandTrunc psi x := by
  simp only [bandTrunc]
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · have hneg : -x ∈ Icc (-1 : ℝ) 1 := by
      constructor <;> linarith [hx.1, hx.2]
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hneg, heven]
  · have hneg : -x ∉ Icc (-1 : ℝ) 1 := by
      intro h
      apply hx
      constructor <;> linarith [h.1, h.2]
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hneg]

theorem continuousEvenBandL2_mem_evenSubspace
    (psi : ℝ → ℝ) (hpsi : Continuous psi) (heven : Function.Even psi) :
    continuousEvenBandL2 psi hpsi ∈ evenSubspace := by
  rw [mem_evenSubspace_iff]
  apply Lp.ext
  have hneg := (continuousEvenBandL2_coeFn psi hpsi).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae (continuousEvenBandL2 psi hpsi), hneg,
    continuousEvenBandL2_coeFn psi hpsi] with x href hleft hright
  rw [href]
  have hleft' : (continuousEvenBandL2 psi hpsi : ℝ → ℂ) (-x) = bandTrunc psi (-x) := by
    simpa only [Function.comp_apply] using hleft
  rw [hleft', hright, bandTrunc_even_of_even heven]

/-- A continuous even normalized trial in the actual even carrier. -/
def continuousEvenBandTrial
    (psi : ℝ → ℝ) (hpsi : Continuous psi) (heven : Function.Even psi) : evenSubspace :=
  ⟨continuousEvenBandL2 psi hpsi,
    continuousEvenBandL2_mem_evenSubspace psi hpsi heven⟩

@[simp] theorem coe_continuousEvenBandTrial
    (psi : ℝ → ℝ) (hpsi : Continuous psi) (heven : Function.Even psi) :
    ((continuousEvenBandTrial psi hpsi heven : evenSubspace) : SoninL2) =
      continuousEvenBandL2 psi hpsi := rfl

theorem evenIndicatorCutoff_one_continuousEvenBandTrial
    (psi : ℝ → ℝ) (hpsi : Continuous psi) (heven : Function.Even psi) :
    evenIndicatorCutoff 1 (continuousEvenBandTrial psi hpsi heven) =
      continuousEvenBandTrial psi hpsi heven := by
  apply Subtype.ext
  apply Lp.ext
  change
    ((indicatorCutoff (centralInterval 1) (measurableSet_centralInterval 1)
      (continuousEvenBandL2 psi hpsi) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
        (continuousEvenBandL2 psi hpsi : ℝ → ℂ)
  filter_upwards [indicatorCutoff_ae (centralInterval 1)
      (measurableSet_centralInterval 1) (continuousEvenBandL2 psi hpsi),
    continuousEvenBandL2_coeFn psi hpsi] with x hcut hcoe
  rw [hcut]
  change (centralInterval 1).indicator
      (fun y => (continuousEvenBandL2 psi hpsi : ℝ → ℂ) y) x =
    (continuousEvenBandL2 psi hpsi : ℝ → ℂ) x
  rw [hcoe]
  change (Icc (-1 : ℝ) 1).indicator
      (fun y => (continuousEvenBandL2 psi hpsi : ℝ → ℂ) y) x = bandTrunc psi x
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hx, hcoe]
  · rw [Set.indicator_of_notMem hx]
    simp [bandTrunc, hx]

theorem norm_sq_continuousEvenBandTrial
    (psi : ℝ → ℝ) (hpsi : Continuous psi) (heven : Function.Even psi) :
    ‖continuousEvenBandTrial psi hpsi heven‖ ^ (2 : ℕ) = ∫ x in (-1 : ℝ)..1, psi x ^ (2 : ℕ) := by
  change ‖continuousEvenBandL2 psi hpsi‖ ^ (2 : ℕ) = _
  rw [GaloisForLFunctions.RHTower.lp_norm_sq_eq_integral]
  calc
    (∫ x : ℝ, ‖(continuousEvenBandL2 psi hpsi : ℝ → ℂ) x‖ ^ (2 : ℕ)) =
        ∫ x : ℝ, ‖bandTrunc psi x‖ ^ (2 : ℕ) := by
      apply integral_congr_ae
      filter_upwards [continuousEvenBandL2_coeFn psi hpsi] with x hx
      exact congrArg (fun z : ℂ => ‖z‖ ^ (2 : ℕ)) hx
    _ = _ := integral_norm_sq_bandTrunc psi

theorem fourierUnitary_continuousEvenBandL2_coeFn
    (psi : ℝ → ℝ) (hpsi : Continuous psi) :
    (fourierUnitary (continuousEvenBandL2 psi hpsi) : ℝ → ℂ) =ᵐ[volume]
      FourierTransform.fourier (bandTrunc psi) := by
  change (((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
      (continuousEvenBandL2 psi hpsi) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
    FourierTransform.fourier (bandTrunc psi)
  let f : SoninL2 := continuousEvenBandL2 psi hpsi
  have hfcoe := continuousEvenBandL2_coeFn psi hpsi
  have hfint : Integrable (f : ℝ → ℂ) := (integrable_bandTrunc hpsi).congr hfcoe.symm
  have hcoe1 : (((memLp_one_iff_integrable.mpr hfint).toLp f :
      Lp ℂ 1 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] (f : ℝ → ℂ) :=
    MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hfint)
  have hclassical : ∀ xi : ℝ,
      (Real.Lp.fourierTransform ((memLp_one_iff_integrable.mpr hfint).toLp f) :
          ℝ → ℂ) xi = FourierTransform.fourier (f : ℝ → ℂ) xi := by
    intro xi
    rw [Real.Lp.fourierTransform_apply]
    exact Real.fourier_congr_ae hcoe1 xi
  have hbridge := (_root_.RHTower.l2_fourier_coeFn_eq_l1_fourier_of_integrable
    f hfint).trans (Filter.Eventually.of_forall hclassical)
  change (((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) f : SoninL2) : ℝ → ℂ) =ᵐ[volume]
    FourierTransform.fourier (f : ℝ → ℂ) at hbridge
  have hrepresentative : FourierTransform.fourier (f : ℝ → ℂ) =
      FourierTransform.fourier (bandTrunc psi) := by
    funext xi
    exact Real.fourier_congr_ae hfcoe xi
  simpa only [f, hrepresentative] using hbridge

theorem norm_sq_evenIndicatorCutoff_fourier_continuousEvenBandTrial
    (psi : ℝ → ℝ) (hpsi : Continuous psi) (heven : Function.Even psi) (r : ℝ) :
    ‖evenIndicatorCutoff r (evenFourierTransform
        (continuousEvenBandTrial psi hpsi heven))‖ ^ (2 : ℕ) =
      ∫ xi in Icc (-r) r, ‖FourierTransform.fourier (bandTrunc psi) xi‖ ^ (2 : ℕ) := by
  change ‖indicatorCutoff (centralInterval r) (measurableSet_centralInterval r)
      (fourierUnitary (continuousEvenBandL2 psi hpsi))‖ ^ (2 : ℕ) = _
  rw [GaloisForLFunctions.RHTower.lp_norm_sq_eq_integral]
  have hae :
      ((indicatorCutoff (centralInterval r) (measurableSet_centralInterval r)
          (fourierUnitary (continuousEvenBandL2 psi hpsi)) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
        (Icc (-r) r).indicator (fun xi => FourierTransform.fourier (bandTrunc psi) xi) := by
    filter_upwards [indicatorCutoff_ae (centralInterval r)
        (measurableSet_centralInterval r) (fourierUnitary (continuousEvenBandL2 psi hpsi)),
      fourierUnitary_continuousEvenBandL2_coeFn psi hpsi] with xi hcut hfourier
    rw [hcut]
    by_cases hxi : xi ∈ Icc (-r) r
    · rw [Set.indicator_of_mem hxi, Set.indicator_of_mem, hfourier]
      simpa [centralInterval] using hxi
    · rw [Set.indicator_of_notMem hxi, Set.indicator_of_notMem]
      simpa [centralInterval] using hxi
  calc
    (∫ xi : ℝ, ‖((indicatorCutoff (centralInterval r)
        (measurableSet_centralInterval r) (fourierUnitary
          (continuousEvenBandL2 psi hpsi)) : SoninL2) : ℝ → ℂ) xi‖ ^ (2 : ℕ)) =
        ∫ xi : ℝ, ‖(Icc (-r) r).indicator
          (fun eta => FourierTransform.fourier (bandTrunc psi) eta) xi‖ ^ (2 : ℕ) := by
      apply integral_congr_ae
      filter_upwards [hae] with xi hxi
      exact congrArg (fun z : ℂ => ‖z‖ ^ (2 : ℕ)) hxi
    _ = ∫ xi : ℝ, (Icc (-r) r).indicator
          (fun eta => ‖FourierTransform.fourier (bandTrunc psi) eta‖ ^ (2 : ℕ)) xi := by
      apply integral_congr_ae
      filter_upwards with xi
      by_cases hxi : xi ∈ Icc (-r) r <;> simp [hxi]
    _ = _ := by rw [MeasureTheory.integral_indicator measurableSet_Icc]

/-- Exact normalized leakage identity for every continuous even trial. -/
theorem norm_sq_sub_norm_sq_fourierCutoff_continuousEvenBandTrial
    (psi : ℝ → ℝ) (hpsi : Continuous psi) (heven : Function.Even psi)
    {r : ℝ} (hr : 0 ≤ r) :
    ‖continuousEvenBandTrial psi hpsi heven‖ ^ (2 : ℕ) -
        ‖evenIndicatorCutoff r (evenFourierTransform
          (continuousEvenBandTrial psi hpsi heven))‖ ^ (2 : ℕ) =
      ∫ xi in (Icc (-r) r)ᶜ, ‖FourierTransform.fourier (bandTrunc psi) xi‖ ^ (2 : ℕ) := by
  let rho : ℝ → ℝ := fun xi => ‖FourierTransform.fourier (bandTrunc psi) xi‖ ^ (2 : ℕ)
  have hrho : Integrable rho := integrable_norm_sq_fourier_bandTrunc hpsi
  have hsplit := MeasureTheory.integral_add_compl
    (measurableSet_Icc (a := -r) (b := r)) hrho
  rw [norm_sq_continuousEvenBandTrial,
    norm_sq_evenIndicatorCutoff_fourier_continuousEvenBandTrial]
  have htotal : (∫ xi : ℝ, rho xi) = ∫ x in (-1 : ℝ)..1, psi x ^ (2 : ℕ) :=
    (integral_norm_sq_fourier_bandTrunc hpsi).trans (integral_norm_sq_bandTrunc psi)
  change (∫ x in (-1 : ℝ)..1, psi x ^ (2 : ℕ)) - ∫ xi in Icc (-r) r, rho xi =
      ∫ xi in (Icc (-r) r)ᶜ, rho xi
  rw [← htotal, ← hsplit]
  ring

/-- Physical dilation of a normalized continuous even trial. -/
def continuousEvenPhysicalTrial
    (a : ℝ) (ha : 0 < a) (psi : ℝ → ℝ)
    (hpsi : Continuous psi) (heven : Function.Even psi) : evenSubspace :=
  evenDilationUnitary a⁻¹ (inv_pos.mpr ha) (continuousEvenBandTrial psi hpsi heven)

theorem norm_sq_continuousEvenPhysicalTrial
    {a : ℝ} (ha : 0 < a) (psi : ℝ → ℝ)
    (hpsi : Continuous psi) (heven : Function.Even psi) :
    ‖continuousEvenPhysicalTrial a ha psi hpsi heven‖ ^ (2 : ℕ) =
      ∫ x in (-1 : ℝ)..1, psi x ^ (2 : ℕ) := by
  rw [continuousEvenPhysicalTrial,
    (evenDilationUnitary a⁻¹ (inv_pos.mpr ha)).norm_map,
    norm_sq_continuousEvenBandTrial]

/-- Exact physical Fourier-concentration conjugation for every normalized even trial. -/
theorem evenTimeBandFourier_continuousEvenPhysicalTrial
    {a : ℝ} (ha : 0 < a) (psi : ℝ → ℝ)
    (hpsi : Continuous psi) (heven : Function.Even psi) :
    evenTimeBandFourier a (continuousEvenPhysicalTrial a ha psi hpsi heven) =
      evenDilationUnitary a ha
        (evenIndicatorCutoff (a ^ (2 : ℕ))
          (evenFourierTransform (continuousEvenBandTrial psi hpsi heven))) := by
  apply Subtype.ext
  rw [continuousEvenPhysicalTrial, evenTimeBandFourier_eq_mul]
  change
    indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
        (fourierUnitary
          (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
            (dilation a⁻¹ (inv_pos.mpr ha) (continuousEvenBandL2 psi hpsi)))) =
      dilation a ha
        (indicatorCutoff (centralInterval (a ^ (2 : ℕ)))
          (measurableSet_centralInterval (a ^ (2 : ℕ)))
          (fourierUnitary (continuousEvenBandL2 psi hpsi)))
  rw [indicatorCutoff_dilation a a⁻¹ (inv_pos.mpr ha)]
  have hmul : a⁻¹ * a = 1 := inv_mul_cancel₀ ha.ne'
  rw [hmul]
  have hsupport :
      indicatorCutoff (centralInterval 1) (measurableSet_centralInterval 1)
          (continuousEvenBandL2 psi hpsi) = continuousEvenBandL2 psi hpsi := by
    exact congrArg Subtype.val (evenIndicatorCutoff_one_continuousEvenBandTrial psi hpsi heven)
  rw [hsupport, fourierUnitary_dilation]
  simp only [inv_inv]
  rw [indicatorCutoff_dilation a a ha]
  congr 3
  ring

/-- Exact physical leakage identity after dilation. -/
theorem norm_sq_sub_norm_sq_timeBand_continuousEvenPhysicalTrial
    {a : ℝ} (ha : 0 < a) (psi : ℝ → ℝ)
    (hpsi : Continuous psi) (heven : Function.Even psi) :
    ‖continuousEvenPhysicalTrial a ha psi hpsi heven‖ ^ (2 : ℕ) -
        ‖evenTimeBandFourier a (continuousEvenPhysicalTrial a ha psi hpsi heven)‖ ^ (2 : ℕ) =
      ∫ xi in (Icc (-(a ^ (2 : ℕ))) (a ^ (2 : ℕ)))ᶜ,
        ‖FourierTransform.fourier (bandTrunc psi) xi‖ ^ (2 : ℕ) := by
  rw [evenTimeBandFourier_continuousEvenPhysicalTrial ha psi hpsi heven,
    (evenDilationUnitary a ha).norm_map,
    continuousEvenPhysicalTrial,
    (evenDilationUnitary a⁻¹ (inv_pos.mpr ha)).norm_map,
    norm_sq_sub_norm_sq_fourierCutoff_continuousEvenBandTrial psi hpsi heven
      (sq_nonneg a)]

end RHTower

end
