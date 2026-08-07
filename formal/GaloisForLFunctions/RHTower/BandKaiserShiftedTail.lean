import GaloisForLFunctions.RHTower.BandKaiserModulatedTrial
import GaloisForLFunctions.RHTower.BandLeakageEnvelope

/-!
# Shifted Kaiser tail envelope

A modulation by frequency `w` translates the base Kaiser spectrum.  When
`|w| ≤ 1/(2*pi*c)`, a point outside the original band either remains outside after translation,
where the global Cauchy envelope applies, or lands in a strip whose squared angular depth is at
most two, where `kaiserEdgeTransformBound` applies.  This is the pointwise decomposition needed
for an integrable fixed-depth tail bound.
-/

open MeasureTheory Set FourierTransform

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Fourier radius of the prolate band in mathlib's frequency normalization. -/
def kaiserBandRadius (c : ℝ) : ℝ := c / (2 * Real.pi)

/-- Shift radius small enough that translated inner-band points stay in a uniformly bounded edge
strip. -/
def kaiserAllowedShift (c : ℝ) : ℝ := 1 / (2 * Real.pi * c)

/-- A convenient measurable window containing every translated edge strip. -/
def kaiserShiftedEdgeWindow (c : ℝ) : Set ℝ :=
  Icc (-(kaiserBandRadius c + kaiserAllowedShift c))
    (kaiserBandRadius c + kaiserAllowedShift c)

theorem measurableSet_kaiserShiftedEdgeWindow (c : ℝ) :
    MeasurableSet (kaiserShiftedEdgeWindow c) :=
  measurableSet_Icc

/-- Pointwise shifted-tail decomposition into the translated global Cauchy envelope and a bounded
inner-edge contribution. -/
theorem norm_sq_fourier_bandTrunc_kaiser_shift_le_envelope
    {c w ξ : ℝ} (hc : 1 ≤ c) (hw : |w| ≤ kaiserAllowedShift c)
    (hξ : ξ ∈ (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ) :
    ‖𝓕 (bandTrunc (kaiserTrial c)) (ξ - w)‖ ^ 2 ≤
      cauchyPair c (ξ - w) +
        (kaiserShiftedEdgeWindow c).indicator
          (fun _ => kaiserEdgeTransformBound ^ 2) ξ := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hcpos : 0 < c := one_pos.trans_le hc
  have hCpos : 0 < kaiserBandRadius c := by
    rw [kaiserBandRadius]
    positivity
  have hdpos : 0 < kaiserAllowedShift c := by
    rw [kaiserAllowedShift]
    positivity
  have hξoutside : kaiserBandRadius c < |ξ| := by
    rw [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hξ
    rcases hξ with hξ | hξ
    · rw [abs_of_neg (hξ.trans (neg_lt_zero.mpr hCpos))]
      linarith
    · have hξ' : kaiserBandRadius c < ξ := lt_of_not_ge hξ
      rw [abs_of_pos (hCpos.trans hξ')]
      exact hξ'
  have hangularξ : c < |2 * Real.pi * ξ| := by
    rw [abs_mul, abs_of_pos hpi]
    rw [kaiserBandRadius] at hξoutside
    have := mul_lt_mul_of_pos_left hξoutside hpi
    field_simp at this ⊢
    linarith
  by_cases houter : c < |2 * Real.pi * (ξ - w)|
  · have hbase := norm_sq_fourier_bandTrunc_kaiser_le hcpos.le houter
    have hpair := folded_cauchy_le_pair c (ξ - w)
    have hedge : 0 ≤ (kaiserShiftedEdgeWindow c).indicator
        (fun _ => kaiserEdgeTransformBound ^ 2) ξ := by
      by_cases hmem : ξ ∈ kaiserShiftedEdgeWindow c <;> simp [hmem]
      exact sq_nonneg kaiserEdgeTransformBound
    exact hbase.trans (hpair.trans (le_add_of_nonneg_right hedge))
  · have hangular : |2 * Real.pi * (ξ - w)| ≤ c := le_of_not_gt houter
    have hwAngular : |2 * Real.pi * w| ≤ c⁻¹ := by
      rw [abs_mul, abs_of_pos hpi]
      rw [kaiserAllowedShift] at hw
      have hmul := mul_le_mul_of_nonneg_left hw hpi.le
      have hcne : c ≠ 0 := hcpos.ne'
      field_simp [hcne] at hmul ⊢
      exact hmul
    have htriangle : |2 * Real.pi * ξ| ≤
        |2 * Real.pi * (ξ - w)| + |2 * Real.pi * w| := by
      calc
        |2 * Real.pi * ξ| = |2 * Real.pi * (ξ - w) + 2 * Real.pi * w| := by ring_nf
        _ ≤ |2 * Real.pi * (ξ - w)| + |2 * Real.pi * w| := abs_add_le _ _
    have hlow : c - c⁻¹ < |2 * Real.pi * (ξ - w)| := by
      linarith
    have hcinv : c * c⁻¹ = 1 := mul_inv_cancel₀ hcpos.ne'
    have hinvle : c⁻¹ ≤ c :=
      (inv_le_one_of_one_le₀ hc).trans hc
    have hlow0 : 0 ≤ c - c⁻¹ := sub_nonneg.mpr hinvle
    have hsquare : (c - c⁻¹) ^ 2 ≤ |2 * Real.pi * (ξ - w)| ^ 2 :=
      pow_le_pow_left₀ hlow0 hlow.le 2
    have hedge : c ^ 2 - (2 * Real.pi * (ξ - w)) ^ 2 ≤ 2 := by
      have habssq : |2 * Real.pi * (ξ - w)| ^ 2 =
          (2 * Real.pi * (ξ - w)) ^ 2 := sq_abs _
      calc
        c ^ 2 - (2 * Real.pi * (ξ - w)) ^ 2
            ≤ c ^ 2 - (c - c⁻¹) ^ 2 := by nlinarith
        _ = 2 - c⁻¹ ^ 2 := by nlinarith
        _ ≤ 2 := by nlinarith [sq_nonneg c⁻¹]
    have hinner : 0 ≤ c ^ 2 - (2 * Real.pi * (ξ - w)) ^ 2 := by
      have hsquare' := pow_le_pow_left₀ (abs_nonneg _) hangular 2
      rw [sq_abs] at hsquare'
      linarith
    have huabs : |ξ - w| ≤ kaiserBandRadius c := by
      rw [abs_mul, abs_of_pos hpi] at hangular
      rw [kaiserBandRadius]
      apply (le_div_iff₀ hpi).2
      simpa [mul_comm] using hangular
    have hξabs : |ξ| ≤ kaiserBandRadius c + kaiserAllowedShift c := by
      have htri : |ξ| ≤ |ξ - w| + |w| := by
        calc
          |ξ| = |(ξ - w) + w| := by ring_nf
          _ ≤ |ξ - w| + |w| := abs_add_le _ _
      linarith
    have hmem : ξ ∈ kaiserShiftedEdgeWindow c := by
      rw [kaiserShiftedEdgeWindow, Set.mem_Icc]
      exact ⟨(neg_le_of_abs_le hξabs), le_of_abs_le hξabs⟩
    rw [Set.indicator_of_mem hmem]
    have hbase := norm_sq_fourier_bandTrunc_kaiser_le_edgeBound hinner hedge
    exact hbase.trans (le_add_of_nonneg_left (cauchyPair_nonneg c (ξ - w)))

/-- A sufficiently small frequency translate of the Kaiser spectrum has only polynomial tail
mass.  The first term is the translated global Cauchy mass; the second deliberately integrates the
edge constant over a larger window than necessary, keeping the proof robust while preserving the
required subexponential scale. -/
theorem integral_compl_band_norm_sq_fourier_kaiser_shift_le
    {c w : ℝ} (hc : 1 ≤ c) (hw : |w| ≤ kaiserAllowedShift c) :
    (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
        ‖𝓕 (bandTrunc (kaiserTrial c)) (ξ - w)‖ ^ 2) ≤
      8 + 2 * (kaiserBandRadius c + kaiserAllowedShift c) *
        kaiserEdgeTransformBound ^ 2 := by
  let density : ℝ → ℝ := fun ξ => ‖𝓕 (bandTrunc (kaiserTrial c)) ξ‖ ^ 2
  let edge : ℝ → ℝ := (kaiserShiftedEdgeWindow c).indicator
    (fun _ => kaiserEdgeTransformBound ^ 2)
  have hdensity : Integrable density :=
    integrable_norm_sq_fourier_bandTrunc (continuous_kaiserTrial c)
  have hshift : Integrable (fun ξ => density (ξ - w)) := hdensity.comp_sub_right w
  have hedge : Integrable edge := by
    exact (integrableOn_const (C := kaiserEdgeTransformBound ^ 2) (by
      simp [kaiserShiftedEdgeWindow])).integrable_indicator
        (measurableSet_kaiserShiftedEdgeWindow c)
  have hcauchy : Integrable (fun ξ => cauchyPair c (ξ - w)) :=
    (integrable_cauchyPair c).comp_sub_right w
  have henvelope : Integrable (fun ξ => cauchyPair c (ξ - w) + edge ξ) :=
    hcauchy.add hedge
  have hpoint : ∀ᵐ ξ : ℝ ∂(volume.restrict
      (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ),
      density (ξ - w) ≤ cauchyPair c (ξ - w) + edge ξ := by
    filter_upwards [ae_restrict_mem
      (measurableSet_Icc.compl : MeasurableSet
        (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ)] with ξ hξ
    exact norm_sq_fourier_bandTrunc_kaiser_shift_le_envelope hc hw hξ
  have hmono :
      (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
          density (ξ - w)) ≤
        ∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
          (cauchyPair c (ξ - w) + edge ξ) :=
    integral_mono_ae hshift.integrableOn henvelope.integrableOn hpoint
  have hcauchyRestrict :
      (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
          cauchyPair c (ξ - w)) ≤ ∫ ξ : ℝ, cauchyPair c (ξ - w) :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun ξ => cauchyPair_nonneg c (ξ - w)) hcauchy
  have hedgeRestrict :
      (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ, edge ξ) ≤
        ∫ ξ : ℝ, edge ξ :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun ξ => by
        change 0 ≤ (kaiserShiftedEdgeWindow c).indicator
          (fun _ => kaiserEdgeTransformBound ^ 2) ξ
        by_cases hmem : ξ ∈ kaiserShiftedEdgeWindow c <;> simp [hmem]
        exact sq_nonneg kaiserEdgeTransformBound) hedge
  have hcauchyIntegral : (∫ ξ : ℝ, cauchyPair c (ξ - w)) = 8 := by
    rw [MeasureTheory.integral_sub_right_eq_self, integral_cauchyPair]
  have hwidth : 0 ≤ kaiserBandRadius c + kaiserAllowedShift c := by
    have hcpos : 0 < c := one_pos.trans_le hc
    simp only [kaiserBandRadius, kaiserAllowedShift]
    positivity
  have hedgeIntegral : (∫ ξ : ℝ, edge ξ) =
      2 * (kaiserBandRadius c + kaiserAllowedShift c) *
        kaiserEdgeTransformBound ^ 2 := by
    change (∫ ξ : ℝ, (kaiserShiftedEdgeWindow c).indicator
      (fun _ => kaiserEdgeTransformBound ^ 2) ξ) = _
    rw [MeasureTheory.integral_indicator (measurableSet_kaiserShiftedEdgeWindow c),
      MeasureTheory.setIntegral_const]
    rw [kaiserShiftedEdgeWindow, Real.volume_real_Icc_of_le (by linarith)]
    simp only [smul_eq_mul]
    ring
  calc
    (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
        ‖𝓕 (bandTrunc (kaiserTrial c)) (ξ - w)‖ ^ 2)
      = ∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
          density (ξ - w) := rfl
    _ ≤ ∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
          (cauchyPair c (ξ - w) + edge ξ) := hmono
    _ = (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
          cauchyPair c (ξ - w)) +
        ∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ, edge ξ := by
          exact integral_add hcauchy.integrableOn hedge.integrableOn
    _ ≤ (∫ ξ : ℝ, cauchyPair c (ξ - w)) + ∫ ξ : ℝ, edge ξ :=
      add_le_add hcauchyRestrict hedgeRestrict
    _ = 8 + 2 * (kaiserBandRadius c + kaiserAllowedShift c) *
        kaiserEdgeTransformBound ^ 2 := by rw [hcauchyIntegral, hedgeIntegral]

/-- Every small cosine-modulated Kaiser packet has the same polynomial spectral-tail envelope as
its two translated components. -/
theorem integral_compl_band_norm_sq_fourier_kaiserCosTrial_le
    {c w : ℝ} (hc : 1 ≤ c) (hw : |w| ≤ kaiserAllowedShift c) :
    (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
        ‖𝓕 (bandTrunc (kaiserCosTrial c w)) ξ‖ ^ 2) ≤
      8 + 2 * (kaiserBandRadius c + kaiserAllowedShift c) *
        kaiserEdgeTransformBound ^ 2 := by
  let baseDensity : ℝ → ℝ := fun ξ => ‖𝓕 (bandTrunc (kaiserTrial c)) ξ‖ ^ 2
  let packetDensity : ℝ → ℝ := fun ξ => ‖𝓕 (bandTrunc (kaiserCosTrial c w)) ξ‖ ^ 2
  have hbase : Integrable baseDensity :=
    integrable_norm_sq_fourier_bandTrunc (continuous_kaiserTrial c)
  have hminus : Integrable (fun ξ => baseDensity (ξ - w)) := hbase.comp_sub_right w
  have hplus : Integrable (fun ξ => baseDensity (ξ + w)) := hbase.comp_add_right w
  have hpacket : Integrable packetDensity :=
    integrable_norm_sq_fourier_bandTrunc (continuous_kaiserCosTrial c w)
  have hpoint : ∀ᵐ ξ : ℝ ∂(volume.restrict
      (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ),
      packetDensity ξ ≤ (baseDensity (ξ - w) + baseDensity (ξ + w)) / 2 := by
    exact Filter.Eventually.of_forall fun ξ =>
      norm_sq_fourier_bandTrunc_kaiserCosTrial_le c w ξ
  have hmono :
      (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
          packetDensity ξ) ≤
        ∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
          (baseDensity (ξ - w) + baseDensity (ξ + w)) / 2 := by
    apply integral_mono_ae hpacket.integrableOn
      ((hminus.add hplus).div_const 2).integrableOn hpoint
  have hminusBound := integral_compl_band_norm_sq_fourier_kaiser_shift_le hc hw
  have hwneg : |-w| ≤ kaiserAllowedShift c := by simpa using hw
  have hplusBound := integral_compl_band_norm_sq_fourier_kaiser_shift_le hc hwneg
  have hrewrite :
      (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
          (baseDensity (ξ - w) + baseDensity (ξ + w)) / 2) =
        ((∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
            baseDensity (ξ - w)) +
          ∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
            baseDensity (ξ + w)) / 2 := by
    rw [integral_div, integral_add hminus.integrableOn hplus.integrableOn]
  rw [hrewrite] at hmono
  change (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
      packetDensity ξ) ≤ _
  refine hmono.trans ?_
  change
    ((∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
        ‖𝓕 (bandTrunc (kaiserTrial c)) (ξ - w)‖ ^ 2) +
      ∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
        ‖𝓕 (bandTrunc (kaiserTrial c)) (ξ + w)‖ ^ 2) / 2 ≤ _
  have hplusBound' :
      (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
        ‖𝓕 (bandTrunc (kaiserTrial c)) (ξ + w)‖ ^ 2) ≤
      8 + 2 * (kaiserBandRadius c + kaiserAllowedShift c) *
        kaiserEdgeTransformBound ^ 2 := by
    simpa only [sub_neg_eq_add] using hplusBound
  linarith

end GaloisForLFunctions.RHTower

end
