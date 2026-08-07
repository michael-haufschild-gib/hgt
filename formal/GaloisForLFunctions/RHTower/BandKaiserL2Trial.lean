import GaloisForLFunctions.RHTower.BandKaiserPacketEnvelope
import GaloisForLFunctions.RHTower.ConstrainedProlateTrueLeakage
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry

/-!
# Conditioned Kaiser packets in the actual even `L²` carrier

The packet estimates are first proved on the normalized aperture `[-1,1]`.  This module places
their truncations in the project's complex even `L²(ℝ)` carrier and records the exact norm and
Fourier-window identities needed for transport to the physical aperture.
-/

open MeasureTheory Set Filter
open scoped BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions.RHTower

/-- The normalized, compactly supported Kaiser grid combination as an `L²(ℝ)` class. -/
def kaiserGridL2 {m : ℕ} (c : ℝ) (b : Fin m → ℝ) : SoninL2 :=
  (memLp_bandTrunc (continuous_kaiserGridCombination c b) 2).toLp
    (bandTrunc (kaiserGridCombination c b))

theorem kaiserGridL2_coeFn {m : ℕ} (c : ℝ) (b : Fin m → ℝ) :
    (kaiserGridL2 c b : ℝ → ℂ) =ᵐ[volume]
      bandTrunc (kaiserGridCombination c b) :=
  (memLp_bandTrunc (continuous_kaiserGridCombination c b) 2).coeFn_toLp

theorem bandTrunc_kaiserGridCombination_even {m : ℕ}
    (c : ℝ) (b : Fin m → ℝ) (x : ℝ) :
    bandTrunc (kaiserGridCombination c b) (-x) =
      bandTrunc (kaiserGridCombination c b) x := by
  simp only [bandTrunc]
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · have hneg : -x ∈ Icc (-1 : ℝ) 1 := by
      constructor <;> linarith [hx.1, hx.2]
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hneg]
    exact_mod_cast kaiserCosCombination_even c (kaiserPacketFrequency c) b x
  · have hneg : -x ∉ Icc (-1 : ℝ) 1 := by
      intro h
      apply hx
      constructor <;> linarith [h.1, h.2]
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hneg]

/-- The normalized Kaiser combination belongs to the even carrier. -/
theorem kaiserGridL2_mem_evenSubspace {m : ℕ} (c : ℝ) (b : Fin m → ℝ) :
    kaiserGridL2 c b ∈ evenSubspace := by
  rw [mem_evenSubspace_iff]
  apply Lp.ext
  have hneg := (kaiserGridL2_coeFn c b).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae (kaiserGridL2 c b), hneg,
    kaiserGridL2_coeFn c b] with x href hleft hright
  rw [href]
  have hleft' : (kaiserGridL2 c b : ℝ → ℂ) (-x) =
      bandTrunc (kaiserGridCombination c b) (-x) := by
    simpa only [Function.comp_apply] using hleft
  rw [hleft', hright, bandTrunc_kaiserGridCombination_even]

/-- The normalized Kaiser combination as a vector in `L²(ℝ)^ev`. -/
def kaiserGridEven {m : ℕ} (c : ℝ) (b : Fin m → ℝ) : evenSubspace :=
  ⟨kaiserGridL2 c b, kaiserGridL2_mem_evenSubspace c b⟩

@[simp] theorem coe_kaiserGridEven {m : ℕ} (c : ℝ) (b : Fin m → ℝ) :
    ((kaiserGridEven c b : evenSubspace) : SoninL2) = kaiserGridL2 c b := rfl

/-- The normalized vector is already supported in `[-1,1]`. -/
theorem evenIndicatorCutoff_one_kaiserGridEven {m : ℕ}
    (c : ℝ) (b : Fin m → ℝ) :
    evenIndicatorCutoff 1 (kaiserGridEven c b) = kaiserGridEven c b := by
  apply Subtype.ext
  apply Lp.ext
  change
    ((indicatorCutoff (centralInterval 1) (measurableSet_centralInterval 1)
      (kaiserGridL2 c b) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
        (kaiserGridL2 c b : ℝ → ℂ)
  filter_upwards [indicatorCutoff_ae (centralInterval 1)
      (measurableSet_centralInterval 1) (kaiserGridL2 c b),
    kaiserGridL2_coeFn c b] with x hcut hcoe
  rw [hcut]
  change (centralInterval 1).indicator
      (fun y => (kaiserGridL2 c b : ℝ → ℂ) y) x =
    (kaiserGridL2 c b : ℝ → ℂ) x
  rw [hcoe]
  change (Icc (-1 : ℝ) 1).indicator
      (fun y => (kaiserGridL2 c b : ℝ → ℂ) y) x =
    bandTrunc (kaiserGridCombination c b) x
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hx, hcoe]
  · rw [Set.indicator_of_notMem hx]
    simp [bandTrunc, hx]

/-- The carrier norm is exactly the physical energy computed on the normalized aperture. -/
theorem norm_sq_kaiserGridEven {m : ℕ} (c : ℝ) (b : Fin m → ℝ) :
    ‖kaiserGridEven c b‖ ^ 2 =
      ∫ x in (-1 : ℝ)..1, kaiserGridCombination c b x ^ 2 := by
  change ‖kaiserGridL2 c b‖ ^ 2 = _
  rw [GaloisForLFunctions.RHTower.lp_norm_sq_eq_integral]
  calc
    (∫ x : ℝ, ‖(kaiserGridL2 c b : ℝ → ℂ) x‖ ^ 2) =
        ∫ x : ℝ, ‖bandTrunc (kaiserGridCombination c b) x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [kaiserGridL2_coeFn c b] with x hx
      exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hx
    _ = _ := integral_norm_sq_bandTrunc (kaiserGridCombination c b)

/-- The `L²` Fourier representative of a normalized Kaiser combination is its classical Fourier
integral. -/
theorem fourierUnitary_kaiserGridL2_coeFn {m : ℕ} (c : ℝ) (b : Fin m → ℝ) :
    (fourierUnitary (kaiserGridL2 c b) : ℝ → ℂ) =ᵐ[volume]
      FourierTransform.fourier (bandTrunc (kaiserGridCombination c b)) := by
  change (((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) (kaiserGridL2 c b) :
      SoninL2) : ℝ → ℂ) =ᵐ[volume]
    FourierTransform.fourier (bandTrunc (kaiserGridCombination c b))
  let f : SoninL2 := kaiserGridL2 c b
  have hfcoe := kaiserGridL2_coeFn c b
  have hfint : Integrable (f : ℝ → ℂ) :=
    (integrable_bandTrunc (continuous_kaiserGridCombination c b)).congr hfcoe.symm
  have hcoe1 : (((memLp_one_iff_integrable.mpr hfint).toLp f :
      Lp ℂ 1 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] (f : ℝ → ℂ) :=
    MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hfint)
  have hclassical : ∀ ξ : ℝ,
      (Real.Lp.fourierTransform ((memLp_one_iff_integrable.mpr hfint).toLp f) :
          ℝ → ℂ) ξ =
        FourierTransform.fourier (f : ℝ → ℂ) ξ := by
    intro ξ
    rw [Real.Lp.fourierTransform_apply]
    exact Real.fourier_congr_ae hcoe1 ξ
  have hbridge := (_root_.RHTower.l2_fourier_coeFn_eq_l1_fourier_of_integrable
    f hfint).trans (Filter.Eventually.of_forall hclassical)
  change (((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) f : SoninL2) : ℝ → ℂ) =ᵐ[volume]
    FourierTransform.fourier (f : ℝ → ℂ) at hbridge
  have hrepresentative :
      FourierTransform.fourier (f : ℝ → ℂ) =
        FourierTransform.fourier (bandTrunc (kaiserGridCombination c b)) := by
    funext ξ
    exact Real.fourier_congr_ae hfcoe ξ
  simpa only [f, hrepresentative] using hbridge

/-- Exact retained Fourier energy after applying a symmetric frequency cutoff. -/
theorem norm_sq_evenIndicatorCutoff_fourier_kaiserGridEven {m : ℕ}
    (c r : ℝ) (b : Fin m → ℝ) :
    ‖evenIndicatorCutoff r (evenFourierTransform (kaiserGridEven c b))‖ ^ 2 =
      ∫ ξ in Icc (-r) r,
        ‖FourierTransform.fourier (bandTrunc (kaiserGridCombination c b)) ξ‖ ^ 2 := by
  change ‖indicatorCutoff (centralInterval r) (measurableSet_centralInterval r)
      (fourierUnitary (kaiserGridL2 c b))‖ ^ 2 = _
  rw [GaloisForLFunctions.RHTower.lp_norm_sq_eq_integral]
  have hae :
      ((indicatorCutoff (centralInterval r) (measurableSet_centralInterval r)
          (fourierUnitary (kaiserGridL2 c b)) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
        (Icc (-r) r).indicator
          (fun ξ => FourierTransform.fourier
            (bandTrunc (kaiserGridCombination c b)) ξ) := by
    filter_upwards [indicatorCutoff_ae (centralInterval r)
        (measurableSet_centralInterval r) (fourierUnitary (kaiserGridL2 c b)),
      fourierUnitary_kaiserGridL2_coeFn c b] with ξ hcut hfourier
    rw [hcut]
    by_cases hξ : ξ ∈ Icc (-r) r
    · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem, hfourier]
      simpa [centralInterval] using hξ
    · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem]
      simpa [centralInterval] using hξ
  calc
    (∫ ξ : ℝ, ‖((indicatorCutoff (centralInterval r)
        (measurableSet_centralInterval r) (fourierUnitary (kaiserGridL2 c b)) : SoninL2) :
          ℝ → ℂ) ξ‖ ^ 2) =
        ∫ ξ : ℝ, ‖(Icc (-r) r).indicator
          (fun η => FourierTransform.fourier
            (bandTrunc (kaiserGridCombination c b)) η) ξ‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hae] with ξ hξ
      exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hξ
    _ = ∫ ξ : ℝ, (Icc (-r) r).indicator
          (fun η => ‖FourierTransform.fourier
            (bandTrunc (kaiserGridCombination c b)) η‖ ^ 2) ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      by_cases hξ : ξ ∈ Icc (-r) r <;> simp [hξ]
    _ = _ := by rw [MeasureTheory.integral_indicator measurableSet_Icc]

/-- Exact normalized leakage identity: lost carrier energy is the classical spectral tail. -/
theorem norm_sq_sub_norm_sq_fourierCutoff_kaiserGridEven {m : ℕ}
    {c r : ℝ} (hr : 0 ≤ r) (b : Fin m → ℝ) :
    ‖kaiserGridEven c b‖ ^ 2 -
        ‖evenIndicatorCutoff r (evenFourierTransform (kaiserGridEven c b))‖ ^ 2 =
      ∫ ξ in (Icc (-r) r)ᶜ,
        ‖FourierTransform.fourier
          (bandTrunc (kaiserGridCombination c b)) ξ‖ ^ 2 := by
  let ρ : ℝ → ℝ := fun ξ =>
    ‖FourierTransform.fourier
      (bandTrunc (kaiserGridCombination c b)) ξ‖ ^ 2
  have hρ : Integrable ρ :=
    integrable_norm_sq_fourier_bandTrunc (continuous_kaiserGridCombination c b)
  have hsplit := MeasureTheory.integral_add_compl (measurableSet_Icc (a := -r) (b := r)) hρ
  rw [norm_sq_kaiserGridEven,
    norm_sq_evenIndicatorCutoff_fourier_kaiserGridEven]
  have htotal : (∫ ξ : ℝ, ρ ξ) =
      ∫ x in (-1 : ℝ)..1, kaiserGridCombination c b x ^ 2 := by
    exact (integral_norm_sq_fourier_bandTrunc
      (continuous_kaiserGridCombination c b)).trans
        (integral_norm_sq_bandTrunc (kaiserGridCombination c b))
  change (∫ x in (-1 : ℝ)..1, kaiserGridCombination c b x ^ 2) -
      (∫ ξ in Icc (-r) r, ρ ξ) = ∫ ξ in (Icc (-r) r)ᶜ, ρ ξ
  rw [← htotal, ← hsplit]
  ring

/-! ## Transport to the physical aperture -/

/-- Exact conjugation formula for a normalized Kaiser vector widened from `[-1,1]` to
`[-a,a]`.  The input dilation is by `a⁻¹`; Fourier inversion changes it to the output dilation
by `a`, and the physical frequency cutoff becomes the normalized cutoff at radius `a²`. -/
theorem evenTimeBandFourier_evenDilation_inv_kaiserGridEven {m : ℕ}
    {a : ℝ} (ha : 0 < a) (c : ℝ) (b : Fin m → ℝ) :
    evenTimeBandFourier a
        (evenDilationUnitary a⁻¹ (inv_pos.mpr ha) (kaiserGridEven c b)) =
      evenDilationUnitary a ha
        (evenIndicatorCutoff (a ^ 2) (evenFourierTransform (kaiserGridEven c b))) := by
  apply Subtype.ext
  rw [evenTimeBandFourier_eq_mul]
  change
    indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
        (fourierUnitary
          (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
            (dilation a⁻¹ (inv_pos.mpr ha) (kaiserGridL2 c b)))) =
      dilation a ha
        (indicatorCutoff (centralInterval (a ^ 2))
          (measurableSet_centralInterval (a ^ 2))
          (fourierUnitary (kaiserGridL2 c b)))
  rw [indicatorCutoff_dilation a a⁻¹ (inv_pos.mpr ha)]
  have hmul : a⁻¹ * a = 1 := inv_mul_cancel₀ ha.ne'
  rw [hmul]
  have hsupport :
      indicatorCutoff (centralInterval 1) (measurableSet_centralInterval 1)
          (kaiserGridL2 c b) = kaiserGridL2 c b := by
    exact congrArg Subtype.val (evenIndicatorCutoff_one_kaiserGridEven c b)
  rw [hsupport, fourierUnitary_dilation]
  simp only [inv_inv]
  rw [indicatorCutoff_dilation a a ha]
  congr 3
  ring

/-- The physical Kaiser grid vector at aperture `a`, with normalized bandwidth
`c = 2πa²`. -/
def kaiserPhysicalGridEven {m : ℕ} (a : ℝ) (ha : 0 < a)
    (b : Fin m → ℝ) : evenSubspace :=
  evenDilationUnitary a⁻¹ (inv_pos.mpr ha)
    (kaiserGridEven (2 * Real.pi * a ^ 2) b)

theorem norm_sq_kaiserPhysicalGridEven {m : ℕ} {a : ℝ} (ha : 0 < a)
    (b : Fin m → ℝ) :
    ‖kaiserPhysicalGridEven a ha b‖ ^ 2 =
      ∫ x in (-1 : ℝ)..1,
        kaiserGridCombination (2 * Real.pi * a ^ 2) b x ^ 2 := by
  rw [kaiserPhysicalGridEven, (evenDilationUnitary a⁻¹ (inv_pos.mpr ha)).norm_map,
    norm_sq_kaiserGridEven]

theorem kaiserBandRadius_two_pi_mul_sq (a : ℝ) :
    kaiserBandRadius (2 * Real.pi * a ^ 2) = a ^ 2 := by
  rw [kaiserBandRadius]
  field_simp [Real.pi_ne_zero]

/-- Exact physical leakage identity for a real conditioned packet combination. -/
theorem norm_sq_sub_norm_sq_timeBand_kaiserPhysicalGridEven {m : ℕ}
    {a : ℝ} (ha : 0 < a) (b : Fin m → ℝ) :
    ‖kaiserPhysicalGridEven a ha b‖ ^ 2 -
        ‖evenTimeBandFourier a (kaiserPhysicalGridEven a ha b)‖ ^ 2 =
      ∫ ξ in
          (Icc (-(kaiserBandRadius (2 * Real.pi * a ^ 2)))
            (kaiserBandRadius (2 * Real.pi * a ^ 2)))ᶜ,
        ‖FourierTransform.fourier
          (bandTrunc (kaiserGridCombination (2 * Real.pi * a ^ 2) b)) ξ‖ ^ 2 := by
  let c : ℝ := 2 * Real.pi * a ^ 2
  have htransport := evenTimeBandFourier_evenDilation_inv_kaiserGridEven ha c b
  have hnormInput :
      ‖kaiserPhysicalGridEven a ha b‖ = ‖kaiserGridEven c b‖ := by
    exact (evenDilationUnitary a⁻¹ (inv_pos.mpr ha)).norm_map (kaiserGridEven c b)
  have hnormOutput :
      ‖evenTimeBandFourier a (kaiserPhysicalGridEven a ha b)‖ =
        ‖evenIndicatorCutoff (a ^ 2) (evenFourierTransform (kaiserGridEven c b))‖ := by
    rw [kaiserPhysicalGridEven, show 2 * Real.pi * a ^ 2 = c from rfl, htransport,
      (evenDilationUnitary a ha).norm_map]
  rw [hnormInput, hnormOutput]
  have htail := norm_sq_sub_norm_sq_fourierCutoff_kaiserGridEven
    (c := c) (r := a ^ 2) (sq_nonneg a) b
  rw [htail]
  change (∫ ξ in (Icc (-(a ^ 2)) (a ^ 2))ᶜ,
      ‖FourierTransform.fourier (bandTrunc (kaiserGridCombination c b)) ξ‖ ^ 2) = _
  rw [kaiserBandRadius_two_pi_mul_sq]

/-- The normalized Kaiser bandwidth tends to infinity with the physical aperture. -/
theorem tendsto_two_pi_mul_sq_atTop :
    Tendsto (fun a : ℝ => 2 * Real.pi * a ^ 2) atTop atTop := by
  have hsq : Tendsto (fun a : ℝ => a ^ 2) atTop atTop :=
    Filter.tendsto_pow_atTop (by norm_num)
  exact hsq.const_mul_atTop (by positivity : 0 < 2 * Real.pi)

/-- Every real vector in the physical fixed-depth Kaiser span satisfies the correct exponential
time-band defect estimate, uniformly in its coefficients. -/
theorem eventually_exp_mul_timeBand_defect_kaiserPhysicalGridEven_le {m : ℕ}
    (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ (ha : 0 < a) (b : Fin m → ℝ),
      Real.exp ((2 - ε) * (2 * Real.pi * a ^ 2)) *
          (‖kaiserPhysicalGridEven a ha b‖ ^ 2 -
            ‖evenTimeBandFourier a (kaiserPhysicalGridEven a ha b)‖ ^ 2) ≤
        ‖kaiserPhysicalGridEven a ha b‖ ^ 2 := by
  have hpacket := tendsto_two_pi_mul_sq_atTop.eventually
    (eventually_exp_mul_kaiserGridSpectralTail_le_energy hm hε)
  filter_upwards [hpacket] with a haPacket
  intro ha b
  rw [norm_sq_sub_norm_sq_timeBand_kaiserPhysicalGridEven ha,
    norm_sq_kaiserPhysicalGridEven ha]
  exact haPacket b

end RHTower

end
