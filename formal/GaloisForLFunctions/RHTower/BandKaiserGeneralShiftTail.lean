import GaloisForLFunctions.RHTower.BandKaiserShiftedTail

/-!
# General shifted Kaiser tail envelope

The thin-shift estimate is extended to every frequency translation whose angular size is at most
the aperture.  If `q = 2*pi*w`, a translated point which crosses from outside the band to inside
can penetrate to squared depth at most `2*c*|q|`.  The exact positive odd-factorial series therefore
controls the crossed edge strip.

Unlike the earlier `O(c⁻¹)` window, this form permits any `o(c)` angular shift.  Its edge cost is
explicit and grows like `exp(O(sqrt(c*|q|)))`, hence remains subexponential for such shifts.
-/

open MeasureTheory Set FourierTransform

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Positive odd-factorial Kaiser transform envelope at squared inner-band depth `D`. -/
def kaiserEdgeTransformBoundAt (D : ℝ) : ℝ :=
  ∑' m : ℕ, 2 * D ^ m / (Nat.factorial (2 * m + 1) : ℝ)

theorem kaiserEdgeTransformBoundAt_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ kaiserEdgeTransformBoundAt D := by
  rw [kaiserEdgeTransformBoundAt]
  exact tsum_nonneg fun _ => by positivity

theorem kaiserEdgeTransformBoundAt_zero : kaiserEdgeTransformBoundAt 0 = 2 := by
  rw [kaiserEdgeTransformBoundAt, tsum_eq_single 0]
  · norm_num
  · intro m hm
    have hzero : (0 : ℝ) ^ m = 0 := zero_pow hm
    rw [hzero]
    simp

theorem kaiserEdgeTransformBoundAt_eq_sinh {D : ℝ} (hD : 0 < D) :
    kaiserEdgeTransformBoundAt D =
      2 * Real.sinh (Real.sqrt D) / Real.sqrt D := by
  have hsqrt : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD.le
  rw [kaiserEdgeTransformBoundAt]
  have hterm : ∀ m : ℕ,
      2 * D ^ m / (Nat.factorial (2 * m + 1) : ℝ) =
        2 * (Real.sqrt D ^ 2) ^ m / (Nat.factorial (2 * m + 1) : ℝ) := by
    intro m
    rw [hsq]
  rw [tsum_congr hterm, tsum_oddFactorial_sinh hsqrt.ne']

/-- A convenient global exponential majorant for the depth-dependent edge series. -/
theorem kaiserEdgeTransformBoundAt_le_exp {D : ℝ} (hD : 0 ≤ D) :
    kaiserEdgeTransformBoundAt D ≤ 2 * Real.exp (1 + Real.sqrt D) := by
  rcases hD.eq_or_lt with rfl | hDpos
  · rw [kaiserEdgeTransformBoundAt_zero, Real.sqrt_zero]
    have : (1 : ℝ) ≤ Real.exp 1 := by
      simpa using Real.add_one_le_exp 1
    simpa only [add_zero, mul_one] using
      mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ 2 by norm_num)
  have hv : 0 < Real.sqrt D := Real.sqrt_pos.mpr hDpos
  by_cases hv1 : 1 ≤ Real.sqrt D
  · have hsinh : Real.sinh (Real.sqrt D) ≤ Real.exp (Real.sqrt D) := by
      rw [Real.sinh_eq]
      have hexpneg : 0 < Real.exp (-Real.sqrt D) := Real.exp_pos _
      have hexppos : 0 < Real.exp (Real.sqrt D) := Real.exp_pos _
      linarith
    have hdiv : Real.sinh (Real.sqrt D) / Real.sqrt D ≤
        Real.exp (Real.sqrt D) := by
      rw [div_le_iff₀ hv]
      have hmul : Real.exp (Real.sqrt D) ≤
          Real.exp (Real.sqrt D) * Real.sqrt D := by
        exact le_mul_of_one_le_right (Real.exp_pos _).le hv1
      exact hsinh.trans hmul
    have hexp : Real.exp (Real.sqrt D) ≤ Real.exp (1 + Real.sqrt D) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [kaiserEdgeTransformBoundAt_eq_sinh hDpos]
    calc
      2 * Real.sinh (Real.sqrt D) / Real.sqrt D =
          2 * (Real.sinh (Real.sqrt D) / Real.sqrt D) := by ring
      _ ≤ 2 * Real.exp (Real.sqrt D) :=
        mul_le_mul_of_nonneg_left hdiv (show (0 : ℝ) ≤ 2 by norm_num)
      _ ≤ 2 * Real.exp (1 + Real.sqrt D) :=
        mul_le_mul_of_nonneg_left hexp (show (0 : ℝ) ≤ 2 by norm_num)
  · have hvle : Real.sqrt D ≤ 1 := le_of_not_ge hv1
    have hDle : D ≤ 1 := by
      have hsq := Real.sq_sqrt hDpos.le
      nlinarith
    have hmono := tsum_oddFactorial_mono hD hDle
    have hone : kaiserEdgeTransformBoundAt 1 = 2 * Real.sinh 1 := by
      rw [kaiserEdgeTransformBoundAt_eq_sinh (by norm_num)]
      norm_num
    have hsinh : Real.sinh 1 ≤ Real.exp 1 := by
      rw [Real.sinh_eq]
      have hexpneg : 0 < Real.exp (-1) := Real.exp_pos _
      have hexppos : 0 < Real.exp 1 := Real.exp_pos _
      linarith
    have hexpmono : Real.exp 1 ≤ Real.exp (1 + Real.sqrt D) :=
      Real.exp_le_exp.mpr (by have := Real.sqrt_nonneg D; linarith)
    change kaiserEdgeTransformBoundAt D ≤ kaiserEdgeTransformBoundAt 1 at hmono
    calc
      kaiserEdgeTransformBoundAt D ≤ kaiserEdgeTransformBoundAt 1 := hmono
      _ = 2 * Real.sinh 1 := hone
      _ ≤ 2 * Real.exp 1 := mul_le_mul_of_nonneg_left hsinh (by norm_num)
      _ ≤ 2 * Real.exp (1 + Real.sqrt D) :=
        mul_le_mul_of_nonneg_left hexpmono (by norm_num)

/-- Exact shifted inner-edge window for a general frequency translation. -/
def kaiserGeneralShiftedEdgeWindow (c w : ℝ) : Set ℝ :=
  Icc (-(kaiserBandRadius c + |w|)) (kaiserBandRadius c + |w|)

theorem measurableSet_kaiserGeneralShiftedEdgeWindow (c w : ℝ) :
    MeasurableSet (kaiserGeneralShiftedEdgeWindow c w) :=
  measurableSet_Icc

/-- Pointwise decomposition for every shift whose angular magnitude is at most the aperture. -/
theorem norm_sq_fourier_bandTrunc_kaiser_general_shift_le_envelope
    {c w ξ : ℝ} (hc : 0 < c) (hw : |2 * Real.pi * w| ≤ c)
    (hξ : ξ ∈ (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ) :
    ‖𝓕 (bandTrunc (kaiserTrial c)) (ξ - w)‖ ^ 2 ≤
      cauchyPair c (ξ - w) +
        (kaiserGeneralShiftedEdgeWindow c w).indicator
          (fun _ => kaiserEdgeTransformBoundAt
            (2 * c * |2 * Real.pi * w|) ^ 2) ξ := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hCpos : 0 < kaiserBandRadius c := by
    rw [kaiserBandRadius]
    positivity
  have hq0 : 0 ≤ |2 * Real.pi * w| := abs_nonneg _
  have hD0 : 0 ≤ 2 * c * |2 * Real.pi * w| := by positivity
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
  · have hbase := norm_sq_fourier_bandTrunc_kaiser_le hc.le houter
    have hpair := folded_cauchy_le_pair c (ξ - w)
    have hedge : 0 ≤ (kaiserGeneralShiftedEdgeWindow c w).indicator
        (fun _ => kaiserEdgeTransformBoundAt (2 * c * |2 * Real.pi * w|) ^ 2) ξ := by
      by_cases hmem : ξ ∈ kaiserGeneralShiftedEdgeWindow c w <;> simp [hmem]
      exact sq_nonneg _
    exact hbase.trans (hpair.trans (le_add_of_nonneg_right hedge))
  · have hangular : |2 * Real.pi * (ξ - w)| ≤ c := le_of_not_gt houter
    have htriangle : |2 * Real.pi * ξ| ≤
        |2 * Real.pi * (ξ - w)| + |2 * Real.pi * w| := by
      calc
        |2 * Real.pi * ξ| = |2 * Real.pi * (ξ - w) + 2 * Real.pi * w| := by ring_nf
        _ ≤ |2 * Real.pi * (ξ - w)| + |2 * Real.pi * w| := abs_add_le _ _
    have hlow : c - |2 * Real.pi * w| < |2 * Real.pi * (ξ - w)| := by
      linarith
    have hlow0 : 0 ≤ c - |2 * Real.pi * w| := sub_nonneg.mpr hw
    have hsquare : (c - |2 * Real.pi * w|) ^ 2 ≤
        |2 * Real.pi * (ξ - w)| ^ 2 :=
      pow_le_pow_left₀ hlow0 hlow.le 2
    have hedge : c ^ 2 - (2 * Real.pi * (ξ - w)) ^ 2 ≤
        2 * c * |2 * Real.pi * w| := by
      rw [← sq_abs (2 * Real.pi * (ξ - w))]
      calc
        c ^ 2 - |2 * Real.pi * (ξ - w)| ^ 2
            ≤ c ^ 2 - (c - |2 * Real.pi * w|) ^ 2 := by linarith
        _ ≤ 2 * c * |2 * Real.pi * w| := by nlinarith [sq_nonneg |2 * Real.pi * w|]
    have hinner : 0 ≤ c ^ 2 - (2 * Real.pi * (ξ - w)) ^ 2 := by
      have hsquare' := pow_le_pow_left₀ (abs_nonneg _) hangular 2
      rw [sq_abs] at hsquare'
      linarith
    have huabs : |ξ - w| ≤ kaiserBandRadius c := by
      rw [abs_mul, abs_of_pos hpi] at hangular
      rw [kaiserBandRadius]
      apply (le_div_iff₀ hpi).2
      simpa [mul_comm] using hangular
    have hξabs : |ξ| ≤ kaiserBandRadius c + |w| := by
      have htri : |ξ| ≤ |ξ - w| + |w| := by
        calc
          |ξ| = |(ξ - w) + w| := by ring_nf
          _ ≤ |ξ - w| + |w| := abs_add_le _ _
      linarith
    have hmem : ξ ∈ kaiserGeneralShiftedEdgeWindow c w := by
      rw [kaiserGeneralShiftedEdgeWindow, Set.mem_Icc]
      exact ⟨neg_le_of_abs_le hξabs, le_of_abs_le hξabs⟩
    rw [Set.indicator_of_mem hmem]
    have hdepth := tsum_oddFactorial_mono hinner hedge
    change
      (∑' m : ℕ, 2 * (c ^ 2 - (2 * Real.pi * (ξ - w)) ^ 2) ^ m /
        (Nat.factorial (2 * m + 1) : ℝ)) ≤
          kaiserEdgeTransformBoundAt (2 * c * |2 * Real.pi * w|) at hdepth
    have htransform :
        ‖𝓕 (bandTrunc (kaiserTrial c)) (ξ - w)‖ ^ 2 ≤
          kaiserEdgeTransformBoundAt (2 * c * |2 * Real.pi * w|) ^ 2 := by
      rw [norm_sq_fourier_bandTrunc_of_even
        (continuous_kaiserTrial c) (kaiserTrial_even c) (ξ - w)]
      rw [integral_kaiserTrial_cos]
      rw [← sq_abs]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      rw [abs_of_nonneg]
      · exact hdepth
      · exact tsum_nonneg fun _ => by positivity
    exact htransform.trans (le_add_of_nonneg_left (cauchyPair_nonneg c (ξ - w)))

/-- General shifted spectral tail.  The first term is the translated Cauchy mass; the second is
the depth-dependent constant over the exact enlarged edge window. -/
theorem integral_compl_band_norm_sq_fourier_kaiser_general_shift_le
    {c w : ℝ} (hc : 0 < c) (hw : |2 * Real.pi * w| ≤ c) :
    (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
        ‖𝓕 (bandTrunc (kaiserTrial c)) (ξ - w)‖ ^ 2) ≤
      8 + 2 * (kaiserBandRadius c + |w|) *
        kaiserEdgeTransformBoundAt (2 * c * |2 * Real.pi * w|) ^ 2 := by
  let density : ℝ → ℝ := fun ξ => ‖𝓕 (bandTrunc (kaiserTrial c)) ξ‖ ^ 2
  let edge : ℝ → ℝ := (kaiserGeneralShiftedEdgeWindow c w).indicator
    (fun _ => kaiserEdgeTransformBoundAt (2 * c * |2 * Real.pi * w|) ^ 2)
  have hdensity : Integrable density :=
    integrable_norm_sq_fourier_bandTrunc (continuous_kaiserTrial c)
  have hshift : Integrable (fun ξ => density (ξ - w)) := hdensity.comp_sub_right w
  have hedge : Integrable edge := by
    exact (integrableOn_const (C :=
      kaiserEdgeTransformBoundAt (2 * c * |2 * Real.pi * w|) ^ 2) (by
        simp [kaiserGeneralShiftedEdgeWindow])).integrable_indicator
          (measurableSet_kaiserGeneralShiftedEdgeWindow c w)
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
    exact norm_sq_fourier_bandTrunc_kaiser_general_shift_le_envelope hc hw hξ
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
        change 0 ≤ (kaiserGeneralShiftedEdgeWindow c w).indicator
          (fun _ => kaiserEdgeTransformBoundAt (2 * c * |2 * Real.pi * w|) ^ 2) ξ
        by_cases hmem : ξ ∈ kaiserGeneralShiftedEdgeWindow c w <;> simp [hmem]
        exact sq_nonneg _) hedge
  have hcauchyIntegral : (∫ ξ : ℝ, cauchyPair c (ξ - w)) = 8 := by
    rw [MeasureTheory.integral_sub_right_eq_self, integral_cauchyPair]
  have hwidth : 0 ≤ kaiserBandRadius c + |w| := by
    rw [kaiserBandRadius]
    positivity
  have hedgeIntegral : (∫ ξ : ℝ, edge ξ) =
      2 * (kaiserBandRadius c + |w|) *
        kaiserEdgeTransformBoundAt (2 * c * |2 * Real.pi * w|) ^ 2 := by
    change (∫ ξ : ℝ, (kaiserGeneralShiftedEdgeWindow c w).indicator
      (fun _ => kaiserEdgeTransformBoundAt (2 * c * |2 * Real.pi * w|) ^ 2) ξ) = _
    rw [MeasureTheory.integral_indicator (measurableSet_kaiserGeneralShiftedEdgeWindow c w),
      MeasureTheory.setIntegral_const]
    rw [kaiserGeneralShiftedEdgeWindow, Real.volume_real_Icc_of_le (by linarith)]
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
    _ = 8 + 2 * (kaiserBandRadius c + |w|) *
        kaiserEdgeTransformBoundAt (2 * c * |2 * Real.pi * w|) ^ 2 := by
      rw [hcauchyIntegral, hedgeIntegral]

/-- General cosine-packet tail bound obtained by averaging the two translated components. -/
theorem integral_compl_band_norm_sq_fourier_kaiserCosTrial_general_shift_le
    {c w : ℝ} (hc : 0 < c) (hw : |2 * Real.pi * w| ≤ c) :
    (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
        ‖𝓕 (bandTrunc (kaiserCosTrial c w)) ξ‖ ^ 2) ≤
      8 + 2 * (kaiserBandRadius c + |w|) *
        kaiserEdgeTransformBoundAt (2 * c * |2 * Real.pi * w|) ^ 2 := by
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
      packetDensity ξ ≤ (baseDensity (ξ - w) + baseDensity (ξ + w)) / 2 :=
    Filter.Eventually.of_forall fun ξ =>
      norm_sq_fourier_bandTrunc_kaiserCosTrial_le c w ξ
  have hmono :
      (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
          packetDensity ξ) ≤
        ∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
          (baseDensity (ξ - w) + baseDensity (ξ + w)) / 2 := by
    exact integral_mono_ae hpacket.integrableOn
      ((hminus.add hplus).div_const 2).integrableOn hpoint
  have hminusBound := integral_compl_band_norm_sq_fourier_kaiser_general_shift_le hc hw
  have hwneg : |2 * Real.pi * -w| ≤ c := by simpa [abs_neg] using hw
  have hplusBound := integral_compl_band_norm_sq_fourier_kaiser_general_shift_le hc hwneg
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
  have hplusBound' :
      (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
        ‖𝓕 (bandTrunc (kaiserTrial c)) (ξ + w)‖ ^ 2) ≤
      8 + 2 * (kaiserBandRadius c + |w|) *
        kaiserEdgeTransformBoundAt (2 * c * |2 * Real.pi * w|) ^ 2 := by
    simpa only [sub_neg_eq_add, abs_neg, mul_neg] using hplusBound
  change
    ((∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
        ‖𝓕 (bandTrunc (kaiserTrial c)) (ξ - w)‖ ^ 2) +
      ∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
        ‖𝓕 (bandTrunc (kaiserTrial c)) (ξ + w)‖ ^ 2) / 2 ≤ _
  linarith

end GaloisForLFunctions.RHTower

end
