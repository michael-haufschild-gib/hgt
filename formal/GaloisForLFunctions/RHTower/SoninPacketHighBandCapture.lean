import GaloisForLFunctions.RHTower.SoninPacketLowBandEscape

/-!
# The wavepacket is captured by the bands above its carrier

The energy the packet leaves outside a central Fourier band is controlled by the energy of the
profile's spectrum beyond the gap between the band edge and the carrier.  With the band edge on the
same clock as the carrier but at a strictly larger rate, that gap grows and the packet is
asymptotically captured.

Together with the low-band escape this is the frequency concentration `(13)`: the packet's spectrum
sits between the two apertures of the flag once the clock is large.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology FourierTransform

/-- The energy outside a central band, bounded by the outer band integral of the density. -/
theorem norm_sq_sub_evenFourierCutoff_soninPacketEven_le_outer
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (t κ : ℝ) :
    ‖soninPacketEven b c hb hbc κ -
        evenFourierCutoff t (soninPacketEven b c hb hbc κ)‖ ^ 2 ≤
      ∫ ξ : ℝ, {ξ : ℝ | t ≤ |ξ|}.indicator (soninPacketSpectralDensity b c hbc κ) ξ := by
  set F := fourierUnitary (soninPacketL2 b c hb hbc κ) with hF
  have hcoeDiff : ((soninPacketEven b c hb hbc κ -
      evenFourierCutoff t (soninPacketEven b c hb hbc κ) : evenSubspace) : SoninL2) =
      fourierUnitary.symm (F - indicatorCutoff (centralInterval t)
        (measurableSet_centralInterval t) F) := by
    have h1 : ((soninPacketEven b c hb hbc κ : evenSubspace) : SoninL2) =
        fourierUnitary.symm F := by
      rw [hF, LinearIsometryEquiv.symm_apply_apply]
      exact coe_soninPacketEven b c hb hbc κ
    have h2 : ((evenFourierCutoff t (soninPacketEven b c hb hbc κ) : evenSubspace) : SoninL2) =
        fourierUnitary.symm (indicatorCutoff (centralInterval t)
          (measurableSet_centralInterval t) F) := rfl
    rw [Submodule.coe_sub, h1, h2, ← map_sub]
  have hnorm : ‖soninPacketEven b c hb hbc κ -
      evenFourierCutoff t (soninPacketEven b c hb hbc κ)‖ =
      ‖F - indicatorCutoff (centralInterval t) (measurableSet_centralInterval t) F‖ := by
    rw [show ‖soninPacketEven b c hb hbc κ -
        evenFourierCutoff t (soninPacketEven b c hb hbc κ)‖ =
      ‖((soninPacketEven b c hb hbc κ -
        evenFourierCutoff t (soninPacketEven b c hb hbc κ) : evenSubspace) : SoninL2)‖ from rfl,
      hcoeDiff]
    exact fourierUnitary.symm.norm_map _
  rw [hnorm, norm_sq_eq_integral]
  have hLint : Integrable (fun ξ : ℝ =>
      ‖((F - indicatorCutoff (centralInterval t)
        (measurableSet_centralInterval t) F : SoninL2) : ℝ → ℂ) ξ‖ ^ 2) volume := by
    have := (Lp.memLp (F - indicatorCutoff (centralInterval t)
      (measurableSet_centralInterval t) F)).integrable_norm_rpow (by norm_num) (by norm_num)
    simpa using this
  have hRint : Integrable ({ξ : ℝ | t ≤ |ξ|}.indicator
      (soninPacketSpectralDensity b c hbc κ)) volume :=
    (integrable_soninPacketSpectralDensity b c hb hbc κ).indicator (measurableSet_outer t)
  refine integral_mono_ae hLint hRint ?_
  filter_upwards [Lp.coeFn_sub F (indicatorCutoff (centralInterval t)
      (measurableSet_centralInterval t) F),
    indicatorCutoff_ae (centralInterval t) (measurableSet_centralInterval t) F,
    fourierUnitary_soninPacketL2_coeFn b c hb hbc κ] with ξ hsub hind hFval
  rw [hsub]
  simp only [Pi.sub_apply, hind]
  by_cases hmem : ξ ∈ centralInterval t
  · rw [Set.indicator_of_mem hmem, sub_self, norm_zero]
    have : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [this]
    exact Set.indicator_nonneg
      (fun x _ => soninPacketSpectralDensity_nonneg b c hbc κ x) ξ
  · rw [Set.indicator_of_notMem hmem, sub_zero]
    have hout : ξ ∈ {ξ : ℝ | t ≤ |ξ|} := by
      simp only [Set.mem_setOf_eq]
      by_contra hlt
      push Not at hlt
      exact hmem (abs_le.mp hlt.le)
    rw [Set.indicator_of_mem hout]
    unfold soninPacketSpectralDensity
    rw [hFval]

/-- **The three-term bound over an arbitrary band.**  On any measurable set, the packet's spectral
energy is controlled by the two translates of the profile's spectral energy plus the squared
mean. -/
theorem integral_indicator_soninPacketSpectralDensity_le
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (a : ℝ) (S : Set ℝ) (hS : MeasurableSet S) :
    ∫ ξ : ℝ, S.indicator (soninPacketSpectralDensity b c hbc (2 * Real.pi * a)) ξ ≤
      3 * ((4 : ℝ)⁻¹ * (∫ ξ : ℝ, S.indicator
              (fun η : ℝ => soninBumpSpectralDensity b c hbc (η + (-a))) ξ) +
        (4 : ℝ)⁻¹ * (∫ ξ : ℝ, S.indicator
              (fun η : ℝ => soninBumpSpectralDensity b c hbc (η + a)) ξ) +
        (soninPacketMean b c hbc (2 * Real.pi * a)) ^ 2 *
          ∫ ξ : ℝ, S.indicator (soninBumpSpectralDensity b c hbc) ξ) := by
  set μ : ℝ := soninPacketMean b c hbc (2 * Real.pi * a) with hμ
  set D : ℝ → ℝ := soninBumpSpectralDensity b c hbc with hD
  have hDnn : ∀ η, 0 ≤ D η := soninBumpSpectralDensity_nonneg b c hbc
  have hDint : Integrable D volume := integrable_soninBumpSpectralDensity b c hb hbc
  have hpt : ∀ ξ : ℝ, soninPacketSpectralDensity b c hbc (2 * Real.pi * a) ξ ≤
      3 * ((4 : ℝ)⁻¹ * D (ξ + (-a)) + (4 : ℝ)⁻¹ * D (ξ + a) + μ ^ 2 * D ξ) := by
    intro ξ
    have hshift := fourier_soninPacket_eq_shift b c hb hbc a ξ
    have hsub : ξ - a = ξ + (-a) := by ring
    unfold soninPacketSpectralDensity
    rw [hshift]
    set X : ℂ := (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) (ξ - a) with hX
    set Y : ℂ := (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) (ξ + a) with hY
    set Z : ℂ := (μ : ℂ) * 𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) ξ with hZ
    have hXn : ‖X‖ ^ 2 = (4 : ℝ)⁻¹ * D (ξ + (-a)) := by
      rw [hX, norm_mul, hD]
      unfold soninBumpSpectralDensity
      rw [← hsub]
      simp only [norm_inv, Complex.norm_ofNat]
      ring
    have hYn : ‖Y‖ ^ 2 = (4 : ℝ)⁻¹ * D (ξ + a) := by
      rw [hY, norm_mul, hD]
      unfold soninBumpSpectralDensity
      simp only [norm_inv, Complex.norm_ofNat]
      ring
    have hZn : ‖Z‖ ^ 2 = μ ^ 2 * D ξ := by
      rw [hZ, norm_mul, hD]
      unfold soninBumpSpectralDensity
      rw [Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    calc ‖X + Y - Z‖ ^ 2 ≤ (‖X‖ + ‖Y‖ + ‖Z‖) ^ 2 := by
          have htri : ‖X + Y - Z‖ ≤ ‖X‖ + ‖Y‖ + ‖Z‖ := by
            calc ‖X + Y - Z‖ ≤ ‖X + Y‖ + ‖Z‖ := norm_sub_le _ _
              _ ≤ (‖X‖ + ‖Y‖) + ‖Z‖ := by gcongr; exact norm_add_le _ _
          nlinarith [norm_nonneg (X + Y - Z), norm_nonneg X, norm_nonneg Y, norm_nonneg Z]
      _ ≤ 3 * (‖X‖ ^ 2 + ‖Y‖ ^ 2 + ‖Z‖ ^ 2) := by
          nlinarith [sq_nonneg (‖X‖ - ‖Y‖), sq_nonneg (‖X‖ - ‖Z‖), sq_nonneg (‖Y‖ - ‖Z‖)]
      _ = 3 * ((4 : ℝ)⁻¹ * D (ξ + (-a)) + (4 : ℝ)⁻¹ * D (ξ + a) + μ ^ 2 * D ξ) := by
          rw [hXn, hYn, hZn]
  have hLint : Integrable (S.indicator
      (soninPacketSpectralDensity b c hbc (2 * Real.pi * a))) volume :=
    (integrable_soninPacketSpectralDensity b c hb hbc (2 * Real.pi * a)).indicator hS
  have hR1 : Integrable (S.indicator (fun ξ : ℝ => D (ξ + (-a)))) volume :=
    (hDint.comp_add_right (-a)).indicator hS
  have hR2 : Integrable (S.indicator (fun ξ : ℝ => D (ξ + a))) volume :=
    (hDint.comp_add_right a).indicator hS
  have hR3 : Integrable (S.indicator D) volume := hDint.indicator hS
  have hA : Integrable (fun ξ : ℝ =>
      (4 : ℝ)⁻¹ * S.indicator (fun η : ℝ => D (η + (-a))) ξ) volume := hR1.const_mul _
  have hB : Integrable (fun ξ : ℝ =>
      (4 : ℝ)⁻¹ * S.indicator (fun η : ℝ => D (η + a)) ξ) volume := hR2.const_mul _
  have hAB : Integrable (fun ξ : ℝ =>
      (4 : ℝ)⁻¹ * S.indicator (fun η : ℝ => D (η + (-a))) ξ +
        (4 : ℝ)⁻¹ * S.indicator (fun η : ℝ => D (η + a)) ξ) volume := hA.add hB
  have hC : Integrable (fun ξ : ℝ => μ ^ 2 * S.indicator D ξ) volume := hR3.const_mul _
  have hRint : Integrable (fun ξ : ℝ => 3 * ((4 : ℝ)⁻¹ *
      S.indicator (fun η : ℝ => D (η + (-a))) ξ +
      (4 : ℝ)⁻¹ * S.indicator (fun η : ℝ => D (η + a)) ξ +
      μ ^ 2 * S.indicator D ξ)) volume := (hAB.add hC).const_mul _
  have hmono : ∫ ξ : ℝ, S.indicator (soninPacketSpectralDensity b c hbc (2 * Real.pi * a)) ξ ≤
      ∫ ξ : ℝ, 3 * ((4 : ℝ)⁻¹ * S.indicator (fun η : ℝ => D (η + (-a))) ξ +
        (4 : ℝ)⁻¹ * S.indicator (fun η : ℝ => D (η + a)) ξ +
        μ ^ 2 * S.indicator D ξ) := by
    refine integral_mono hLint hRint fun ξ => ?_
    by_cases hmem : ξ ∈ S
    · simp only [Set.indicator_of_mem hmem]
      exact hpt ξ
    · simp only [Set.indicator_of_notMem hmem]
      norm_num
  refine hmono.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_add hAB hC, integral_add hA hB,
    integral_const_mul, integral_const_mul, integral_const_mul]

end RHTower
