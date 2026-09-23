import GaloisForLFunctions.RHTower.SoninPacketFourierPointwise
import GaloisForLFunctions.RHTower.GaussianEvenCarrier
import GaloisForLFunctions.RHTower.L2FourierUncertainty

/-!
# The wavepacket leaves every central Fourier band

The `L²` Fourier transform of the wavepacket agrees almost everywhere with the classical Fourier
integral, which vanishes pointwise and is bounded uniformly in the frequency.  Dominated
convergence on the bounded band then sends the whole Fourier cutoff to zero.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter Set
open scoped Topology FourierTransform

/-- The `L²` Fourier transform of the wavepacket is the classical Fourier integral. -/
theorem fourierUnitary_soninPacketL2_coeFn (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) :
    ((fourierUnitary (soninPacketL2 b c hb hbc κ) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun ξ : ℝ => 𝓕 (fun x : ℝ => (soninPacket b c hbc κ x : ℂ)) ξ := by
  set f : SoninL2 := soninPacketL2 b c hb hbc κ with hfdef
  have hcoe := soninPacketL2_coeFn b c hb hbc κ
  have hint : Integrable (f : ℝ → ℂ) :=
    ((integrable_soninPacket b c hb hbc κ).ofReal).congr hcoe.symm
  have hcoe1 : (((memLp_one_iff_integrable.mpr hint).toLp f : Lp ℂ 1 (volume : Measure ℝ)) :
      ℝ → ℂ) =ᵐ[volume] (f : ℝ → ℂ) :=
    MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hint)
  have hclassical : ∀ w : ℝ,
      (Real.Lp.fourierTransform ((memLp_one_iff_integrable.mpr hint).toLp f) : ℝ → ℂ) w =
        FourierTransform.fourier (f : ℝ → ℂ) w := by
    intro w
    rw [Real.Lp.fourierTransform_apply]
    exact Real.fourier_congr_ae hcoe1 w
  have h1 := (l2_fourier_coeFn_eq_l1_fourier_of_integrable f hint).trans
    (Filter.Eventually.of_forall hclassical)
  refine h1.trans (Filter.Eventually.of_forall fun w => ?_)
  exact Real.fourier_congr_ae hcoe w

/-- The squared Fourier-band energy of the wavepacket as an explicit integral. -/
theorem norm_sq_evenFourierCutoff_soninPacketEven
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (t κ : ℝ) :
    ‖evenFourierCutoff t (soninPacketEven b c hb hbc κ)‖ ^ (2 : ℕ) =
      ∫ ξ : ℝ, ‖(centralInterval t).indicator
        (fun η : ℝ => ((fourierUnitary (soninPacketL2 b c hb hbc κ) : SoninL2) : ℝ → ℂ) η)
        ξ‖ ^ (2 : ℕ) := by
  have hcoe : ((evenFourierCutoff t (soninPacketEven b c hb hbc κ) : evenSubspace) : SoninL2) =
      fourierUnitary.symm (indicatorCutoff (centralInterval t)
        (measurableSet_centralInterval t) (fourierUnitary (soninPacketL2 b c hb hbc κ))) := rfl
  have hnorm : ‖evenFourierCutoff t (soninPacketEven b c hb hbc κ)‖ =
      ‖indicatorCutoff (centralInterval t) (measurableSet_centralInterval t)
        (fourierUnitary (soninPacketL2 b c hb hbc κ))‖ := by
    rw [show ‖evenFourierCutoff t (soninPacketEven b c hb hbc κ)‖ =
        ‖((evenFourierCutoff t (soninPacketEven b c hb hbc κ) : evenSubspace) : SoninL2)‖ from rfl,
      hcoe]
    exact fourierUnitary.symm.norm_map _
  rw [hnorm, norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [indicatorCutoff_ae (centralInterval t) (measurableSet_centralInterval t)
    (fourierUnitary (soninPacketL2 b c hb hbc κ))] with ξ hξ
  rw [hξ]

/-- **Fourier escape `(10)`.**  The wavepacket eventually carries no energy in any fixed central
Fourier band. -/
theorem tendsto_norm_evenFourierCutoff_soninPacketEven
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (t : ℝ)
    (κ : ℕ → ℝ) (hκ : Tendsto κ atTop atTop) :
    Tendsto (fun n : ℕ => ‖evenFourierCutoff t (soninPacketEven b c hb hbc (κ n))‖)
      atTop (𝓝 0) := by
  set M : ℝ := 2 * ∫ x : ℝ, soninAnnulusBump b c hbc x with hM
  set G : ℕ → ℝ → ℂ := fun n ξ =>
    ((fourierUnitary (soninPacketL2 b c hb hbc (κ n)) : SoninL2) : ℝ → ℂ) ξ with hG
  set F : ℕ → ℝ → ℝ := fun n ξ =>
    ‖(centralInterval t).indicator (fun η : ℝ => G n η) ξ‖ ^ (2 : ℕ) with hF
  have hae : ∀ᵐ ξ : ℝ, ∀ n : ℕ,
      G n ξ = 𝓕 (fun x : ℝ => (soninPacket b c hbc (κ n) x : ℂ)) ξ := by
    rw [MeasureTheory.ae_all_iff]
    intro n
    exact fourierUnitary_soninPacketL2_coeFn b c hb hbc (κ n)
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (F n) volume := by
    intro n
    refine ((Lp.aestronglyMeasurable
      (fourierUnitary (soninPacketL2 b c hb hbc (κ n)))).indicator
        (measurableSet_centralInterval t)).norm.pow 2
  have hbound : ∀ n : ℕ, ∀ᵐ ξ : ℝ,
      ‖F n ξ‖ ≤ (centralInterval t).indicator (fun _ : ℝ => M ^ (2 : ℕ)) ξ := by
    intro n
    filter_upwards [fourierUnitary_soninPacketL2_coeFn b c hb hbc (κ n)] with ξ hξ
    by_cases hmem : ξ ∈ centralInterval t
    · have hle : ‖G n ξ‖ ≤ M := by
        simp only [hG]
        rw [hξ]
        exact norm_fourier_soninPacket_le b c hb hbc (κ n) ξ
      have hMnn : 0 ≤ M := by
        rw [hM]
        have := (integral_soninAnnulusBump_pos b c hb hbc).le
        positivity
      simp only [hF, Set.indicator_of_mem hmem, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (‖G n ξ‖))]
      nlinarith [norm_nonneg (G n ξ)]
    · simp [hF, Set.indicator_of_notMem hmem]
  have hlim : ∀ᵐ ξ : ℝ, Tendsto (fun n : ℕ => F n ξ) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hae] with ξ hξ
    by_cases hmem : ξ ∈ centralInterval t
    · have hptw : Tendsto (fun n : ℕ =>
          𝓕 (fun x : ℝ => (soninPacket b c hbc (κ n) x : ℂ)) ξ) atTop (𝓝 0) :=
        (tendsto_fourier_soninPacket_atTop b c hb hbc ξ).comp hκ
      have hGtend : Tendsto (fun n : ℕ => G n ξ) atTop (𝓝 0) :=
        hptw.congr fun n => (hξ n).symm
      have := (hGtend.norm).pow 2
      simpa [hF, Set.indicator_of_mem hmem] using this
    · simp [hF, Set.indicator_of_notMem hmem]
  have hboundInt : Integrable ((centralInterval t).indicator (fun _ : ℝ => M ^ (2 : ℕ))) volume := by
    refine (integrable_indicator_iff (measurableSet_centralInterval t)).mpr ?_
    have hfin : volume (centralInterval t) ≠ ⊤ := by
      rw [centralInterval]
      exact measure_Icc_lt_top.ne
    exact integrableOn_const hfin
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    ((centralInterval t).indicator (fun _ : ℝ => M ^ (2 : ℕ))) hmeas hboundInt hbound hlim
  have hsq : Tendsto (fun n : ℕ =>
      ‖evenFourierCutoff t (soninPacketEven b c hb hbc (κ n))‖ ^ (2 : ℕ)) atTop (𝓝 0) := by
    have hzero : ∫ _ : ℝ, (0 : ℝ) = 0 := integral_zero _ _
    rw [hzero] at hdct
    refine hdct.congr fun n => ?_
    exact (norm_sq_evenFourierCutoff_soninPacketEven b c hb hbc t (κ n)).symm
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun n => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

end RHTower
