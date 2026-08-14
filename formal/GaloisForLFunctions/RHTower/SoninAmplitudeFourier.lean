import GaloisForLFunctions.RHTower.SoninAmplitudePacket
import GaloisForLFunctions.RHTower.SoninPacketFourierConcentration
import GaloisForLFunctions.RHTower.SoninPacketCompactVanishing

/-!
# Weak escape and Fourier escape for an arbitrary annulus amplitude

Everything the coupling needs from the packet's spectrum survives the loss of smoothness: the
packet pairs to zero with every fixed weight, so every fixed compact operator kills it; its Fourier
transform vanishes pointwise and is uniformly bounded, so it leaves every fixed central band; and
its spectral density is a fixed integrable function translated by the carrier, so the packet is
captured by the bands above the carrier.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology InnerProductSpace FourierTransform

namespace AnnulusAmplitude

variable {b c : ℝ} (A : AnnulusAmplitude b c)

/-! ### Weak escape -/

/-- **Weak escape.**  Every fixed weight integrable against the amplitude pairs to zero with the
packet at high frequency. -/
theorem tendsto_integral_mul_ampPacket_atTop {g : ℝ → ℂ}
    (hg : Integrable (fun x : ℝ => g x * (A.toFun x : ℂ))) :
    Tendsto (fun κ : ℝ => ∫ x : ℝ, g x * (A.ampPacket κ x : ℂ)) atTop (𝓝 0) := by
  have hosc := tendsto_integral_complex_mul_cos_freq_atTop hg
  have hmean := A.tendsto_ampPacketMean_atTop
  have hsplit : ∀ κ : ℝ, (∫ x : ℝ, g x * (A.ampPacket κ x : ℂ)) =
      (∫ x : ℝ, (g x * (A.toFun x : ℂ)) * (Real.cos (κ * x) : ℂ)) -
        ((A.ampPacketMean κ : ℝ) : ℂ) * ∫ x : ℝ, g x * (A.toFun x : ℂ) := by
    intro κ
    have hI1 := integrable_complex_mul_cos hg κ
    have hI2 : Integrable (fun x : ℝ =>
        ((A.ampPacketMean κ : ℝ) : ℂ) * (g x * (A.toFun x : ℂ))) := hg.const_mul _
    have hpt : ∀ x : ℝ, g x * (A.ampPacket κ x : ℂ) =
        (g x * (A.toFun x : ℂ)) * (Real.cos (κ * x) : ℂ) -
          ((A.ampPacketMean κ : ℝ) : ℂ) * (g x * (A.toFun x : ℂ)) := by
      intro x
      simp only [ampPacket]
      push_cast
      ring
    rw [show (∫ x : ℝ, g x * (A.ampPacket κ x : ℂ)) =
        ∫ x : ℝ, ((g x * (A.toFun x : ℂ)) * (Real.cos (κ * x) : ℂ) -
          ((A.ampPacketMean κ : ℝ) : ℂ) * (g x * (A.toFun x : ℂ))) from
      integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_sub hI1 hI2, integral_const_mul]
  have hmeanC : Tendsto (fun κ : ℝ => ((A.ampPacketMean κ : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hmean
  have hlim : Tendsto (fun κ : ℝ =>
      (∫ x : ℝ, (g x * (A.toFun x : ℂ)) * (Real.cos (κ * x) : ℂ)) -
        ((A.ampPacketMean κ : ℝ) : ℂ) * ∫ x : ℝ, g x * (A.toFun x : ℂ)) atTop (𝓝 0) := by
    simpa using hosc.sub (hmeanC.mul_const (∫ x : ℝ, g x * (A.toFun x : ℂ)))
  exact hlim.congr fun κ => (hsplit κ).symm

/-- **Weak escape in `L²`.** -/
theorem tendsto_inner_ampPacketL2_atTop (g : SoninL2) :
    Tendsto (fun κ : ℝ => ⟪g, A.ampPacketL2 κ⟫_ℂ) atTop (𝓝 0) := by
  have hgphi : Integrable (fun x : ℝ =>
      (starRingEnd ℂ) ((g : ℝ → ℂ) x) * (A.toFun x : ℂ)) := by
    refine MemLp.integrable_mul (p := 2) (q := 2) ?_ A.memLp_ofReal
    exact memLp_conj (Lp.memLp g)
  have hpair := A.tendsto_integral_mul_ampPacket_atTop hgphi
  refine hpair.congr fun κ => ?_
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [A.ampPacketL2_coeFn κ] with x hx
  rw [hx, RCLike.inner_apply]
  ring

/-- **Compact operators annihilate the packet family.** -/
theorem tendsto_norm_compactOperator_apply_ampPacketEven
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (K : evenSubspace →L[ℂ] F) (hK : IsCompactOperator K)
    (κ : ℕ → ℝ) (hκ : Tendsto κ atTop atTop) :
    Tendsto (fun n : ℕ => ‖K (A.ampPacketEven (κ n))‖) atTop (𝓝 0) := by
  refine IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null K hK
    (fun n => A.ampPacketEven (κ n)) (2 * ‖A.ampL2‖) (fun n => ?_) (fun ℓ => ?_)
  · exact A.norm_ampPacketL2_le (κ n)
  · have hv := A.tendsto_inner_ampPacketL2_atTop
      (((InnerProductSpace.toDual ℂ evenSubspace).symm ℓ : evenSubspace) : SoninL2)
    refine (hv.comp hκ).congr fun n => ?_
    exact InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := evenSubspace)
      (x := A.ampPacketEven (κ n)) (y := ℓ)

/-- The exact Sonin projection correction vanishes along the packet family. -/
theorem tendsto_norm_evenSoninProjectionCorrection_apply_ampPacketEven
    (t : ℝ) (ht : 0 < t) (κ : ℕ → ℝ) (hκ : Tendsto κ atTop atTop) :
    Tendsto (fun n : ℕ => ‖evenSoninProjectionCorrection t (A.ampPacketEven (κ n))‖)
      atTop (𝓝 0) :=
  A.tendsto_norm_compactOperator_apply_ampPacketEven (evenSoninProjectionCorrection t)
    (IsSoninPrincipalRelativeIdeal.isCompactOperator
      (IsSoninPrincipalRelativeIdeal.projectionCorrection t ht)) κ hκ

/-! ### The Fourier transform of the packet -/

theorem integrable_ampPacketL2 (κ : ℝ) : Integrable (A.ampPacketL2 κ : ℝ → ℂ) :=
  ((A.integrable_ampPacket κ).ofReal).congr (A.ampPacketL2_coeFn κ).symm

/-- The `L²` Fourier transform of the packet is the classical Fourier integral. -/
theorem fourierUnitary_ampPacketL2_coeFn (κ : ℝ) :
    ((fourierUnitary (A.ampPacketL2 κ) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun ξ : ℝ => 𝓕 (fun x : ℝ => (A.ampPacket κ x : ℂ)) ξ := by
  set f : SoninL2 := A.ampPacketL2 κ with hfdef
  have hcoe := A.ampPacketL2_coeFn κ
  have hint : Integrable (f : ℝ → ℂ) := A.integrable_ampPacketL2 κ
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

/-- The amplitude as an `L¹` function. -/
theorem integrable_ampL2 : Integrable (A.ampL2 : ℝ → ℂ) :=
  (A.integrable.ofReal).congr A.ampL2_coeFn.symm

/-- The `L²` Fourier transform of the amplitude is the classical Fourier integral. -/
theorem fourierUnitary_ampL2_coeFn :
    ((fourierUnitary A.ampL2 : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun ξ : ℝ => 𝓕 (fun x : ℝ => (A.toFun x : ℂ)) ξ := by
  set f : SoninL2 := A.ampL2 with hfdef
  have hcoe := A.ampL2_coeFn
  have hint : Integrable (f : ℝ → ℂ) := A.integrable_ampL2
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

/-- The Fourier transform of the packet, written as an explicit pairing. -/
theorem fourier_ampPacket_eq (κ ξ : ℝ) :
    𝓕 (fun x : ℝ => (A.ampPacket κ x : ℂ)) ξ =
      ∫ x : ℝ, Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) *
        (A.ampPacket κ x : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  rfl

/-- The amplitude times a bounded measurable weight is integrable. -/
theorem integrable_char_mul_amp {f : ℝ → ℂ} (hf : Measurable f) {K : ℝ}
    (hK : ∀ x, ‖f x‖ ≤ K) : Integrable (fun x : ℝ => f x * (A.toFun x : ℂ)) := by
  refine A.integrable_complex_of_bound
    ((hf.mul (Complex.continuous_ofReal.measurable.comp A.measurable')).aestronglyMeasurable)
    (K := K * A.bound) (fun x => ?_) (fun x hx => by simp [hx])
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, A.abs_eq]
  have hKnn : (0 : ℝ) ≤ K := le_trans (norm_nonneg _) (hK 0)
  exact mul_le_mul (hK x) (A.le_bound' x) (A.nonneg' x) hKnn

/-- **Pointwise Fourier escape.** -/
theorem tendsto_fourier_ampPacket_atTop (ξ : ℝ) :
    Tendsto (fun κ : ℝ => 𝓕 (fun x : ℝ => (A.ampPacket κ x : ℂ)) ξ) atTop (𝓝 0) := by
  have hmeas : Measurable fun x : ℝ =>
      Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) := by
    exact (Complex.measurable_exp.comp
      (((Complex.continuous_ofReal.measurable.comp (by fun_prop)).mul measurable_const)))
  have hbd : ∀ x : ℝ, ‖Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I)‖ ≤ 1 := by
    intro x
    rw [Complex.norm_exp_ofReal_mul_I]
  have hint := A.integrable_char_mul_amp hmeas hbd
  have hpair := A.tendsto_integral_mul_ampPacket_atTop hint
  exact hpair.congr fun κ => (A.fourier_ampPacket_eq κ ξ).symm

/-- **Uniform bound on the transform.** -/
theorem norm_fourier_ampPacket_le (κ ξ : ℝ) :
    ‖𝓕 (fun x : ℝ => (A.ampPacket κ x : ℂ)) ξ‖ ≤ 2 * ∫ x : ℝ, A.toFun x := by
  rw [A.fourier_ampPacket_eq κ ξ]
  have hbound : ∀ x : ℝ,
      ‖Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) * (A.ampPacket κ x : ℂ)‖ ≤
        2 * A.toFun x := by
    intro x
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact A.abs_ampPacket_le κ x
  calc ‖∫ x : ℝ, Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) *
          (A.ampPacket κ x : ℂ)‖
      ≤ ∫ x : ℝ, 2 * A.toFun x := by
        refine norm_integral_le_of_norm_le ?_ (Filter.Eventually.of_forall hbound)
        exact A.integrable.const_mul 2
    _ = 2 * ∫ x : ℝ, A.toFun x := integral_const_mul _ _

/-! ### Escape from a fixed central band -/

/-- The squared Fourier-band energy of the packet as an explicit integral. -/
theorem norm_sq_evenFourierCutoff_ampPacketEven (t κ : ℝ) :
    ‖evenFourierCutoff t (A.ampPacketEven κ)‖ ^ 2 =
      ∫ ξ : ℝ, ‖(centralInterval t).indicator
        (fun η : ℝ => ((fourierUnitary (A.ampPacketL2 κ) : SoninL2) : ℝ → ℂ) η) ξ‖ ^ 2 := by
  have hcoe : ((evenFourierCutoff t (A.ampPacketEven κ) : evenSubspace) : SoninL2) =
      fourierUnitary.symm (indicatorCutoff (centralInterval t)
        (measurableSet_centralInterval t) (fourierUnitary (A.ampPacketL2 κ))) := rfl
  have hnorm : ‖evenFourierCutoff t (A.ampPacketEven κ)‖ =
      ‖indicatorCutoff (centralInterval t) (measurableSet_centralInterval t)
        (fourierUnitary (A.ampPacketL2 κ))‖ := by
    rw [show ‖evenFourierCutoff t (A.ampPacketEven κ)‖ =
        ‖((evenFourierCutoff t (A.ampPacketEven κ) : evenSubspace) : SoninL2)‖ from rfl, hcoe]
    exact fourierUnitary.symm.norm_map _
  rw [hnorm, norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [indicatorCutoff_ae (centralInterval t) (measurableSet_centralInterval t)
    (fourierUnitary (A.ampPacketL2 κ))] with ξ hξ
  rw [hξ]

/-- **Fourier escape.**  The packet eventually carries no energy in any fixed central band. -/
theorem tendsto_norm_evenFourierCutoff_ampPacketEven (t : ℝ)
    (κ : ℕ → ℝ) (hκ : Tendsto κ atTop atTop) :
    Tendsto (fun n : ℕ => ‖evenFourierCutoff t (A.ampPacketEven (κ n))‖) atTop (𝓝 0) := by
  set M : ℝ := 2 * ∫ x : ℝ, A.toFun x with hM
  set G : ℕ → ℝ → ℂ := fun n ξ =>
    ((fourierUnitary (A.ampPacketL2 (κ n)) : SoninL2) : ℝ → ℂ) ξ with hG
  set F : ℕ → ℝ → ℝ := fun n ξ =>
    ‖(centralInterval t).indicator (fun η : ℝ => G n η) ξ‖ ^ 2 with hF
  have hae : ∀ᵐ ξ : ℝ, ∀ n : ℕ,
      G n ξ = 𝓕 (fun x : ℝ => (A.ampPacket (κ n) x : ℂ)) ξ := by
    rw [MeasureTheory.ae_all_iff]
    intro n
    exact A.fourierUnitary_ampPacketL2_coeFn (κ n)
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (F n) volume := by
    intro n
    refine ((Lp.aestronglyMeasurable
      (fourierUnitary (A.ampPacketL2 (κ n)))).indicator
        (measurableSet_centralInterval t)).norm.pow 2
  have hbound : ∀ n : ℕ, ∀ᵐ ξ : ℝ,
      ‖F n ξ‖ ≤ (centralInterval t).indicator (fun _ : ℝ => M ^ 2) ξ := by
    intro n
    filter_upwards [A.fourierUnitary_ampPacketL2_coeFn (κ n)] with ξ hξ
    by_cases hmem : ξ ∈ centralInterval t
    · have hle : ‖G n ξ‖ ≤ M := by
        simp only [hG]
        rw [hξ]
        exact A.norm_fourier_ampPacket_le (κ n) ξ
      have hMnn : 0 ≤ M := by
        rw [hM]
        have := A.mass_pos'.le
        positivity
      simp only [hF, Set.indicator_of_mem hmem, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (‖G n ξ‖))]
      nlinarith [norm_nonneg (G n ξ)]
    · simp [hF, Set.indicator_of_notMem hmem]
  have hlim : ∀ᵐ ξ : ℝ, Tendsto (fun n : ℕ => F n ξ) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hae] with ξ hξ
    by_cases hmem : ξ ∈ centralInterval t
    · have hptw : Tendsto (fun n : ℕ =>
          𝓕 (fun x : ℝ => (A.ampPacket (κ n) x : ℂ)) ξ) atTop (𝓝 0) :=
        (A.tendsto_fourier_ampPacket_atTop ξ).comp hκ
      have hGtend : Tendsto (fun n : ℕ => G n ξ) atTop (𝓝 0) :=
        hptw.congr fun n => (hξ n).symm
      have := (hGtend.norm).pow 2
      simpa [hF, Set.indicator_of_mem hmem] using this
    · simp [hF, Set.indicator_of_notMem hmem]
  have hboundInt : Integrable ((centralInterval t).indicator (fun _ : ℝ => M ^ 2)) volume := by
    refine (integrable_indicator_iff (measurableSet_centralInterval t)).mpr ?_
    have hfin : volume (centralInterval t) ≠ ⊤ := by
      rw [centralInterval]
      exact measure_Icc_lt_top.ne
    exact integrableOn_const hfin
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    ((centralInterval t).indicator (fun _ : ℝ => M ^ 2)) hmeas hboundInt hbound hlim
  have hsq : Tendsto (fun n : ℕ => ‖evenFourierCutoff t (A.ampPacketEven (κ n))‖ ^ 2)
      atTop (𝓝 0) := by
    have hzero : ∫ _ : ℝ, (0 : ℝ) = 0 := integral_zero _ _
    rw [hzero] at hdct
    refine hdct.congr fun n => ?_
    exact (A.norm_sq_evenFourierCutoff_ampPacketEven t (κ n)).symm
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun n => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

/-! ### Spectral densities -/

/-- The amplitude's spectral energy density. -/
def ampSpectralDensity : ℝ → ℝ := fun η => ‖𝓕 (fun x : ℝ => (A.toFun x : ℂ)) η‖ ^ 2

theorem ampSpectralDensity_nonneg (η : ℝ) : 0 ≤ A.ampSpectralDensity η := by
  unfold ampSpectralDensity
  positivity

/-- **Plancherel for the amplitude.** -/
theorem integrable_ampSpectralDensity : Integrable A.ampSpectralDensity volume := by
  have hLp : Integrable (fun η : ℝ =>
      ‖((fourierUnitary A.ampL2 : SoninL2) : ℝ → ℂ) η‖ ^ 2) volume := by
    have := (Lp.memLp (fourierUnitary A.ampL2)).integrable_norm_rpow (by norm_num) (by norm_num)
    simpa using this
  refine hLp.congr ?_
  filter_upwards [A.fourierUnitary_ampL2_coeFn] with η hη
  unfold ampSpectralDensity
  rw [hη]

theorem integral_ampSpectralDensity_nonneg : 0 ≤ ∫ η : ℝ, A.ampSpectralDensity η :=
  integral_nonneg A.ampSpectralDensity_nonneg

/-- **The amplitude's spectral tails vanish.** -/
theorem tendsto_integral_indicator_outer_ampSpectralDensity (R : ℕ → ℝ)
    (hR : Tendsto R atTop atTop) :
    Tendsto (fun n : ℕ => ∫ η : ℝ, {η : ℝ | R n ≤ |η|}.indicator A.ampSpectralDensity η)
      atTop (𝓝 0) :=
  tendsto_integral_indicator_outer_atTop A.ampSpectralDensity_nonneg
    A.integrable_ampSpectralDensity R hR

/-- The packet's spectral energy density. -/
def ampPacketSpectralDensity (κ : ℝ) : ℝ → ℝ := fun η =>
  ‖𝓕 (fun x : ℝ => (A.ampPacket κ x : ℂ)) η‖ ^ 2

theorem ampPacketSpectralDensity_nonneg (κ η : ℝ) : 0 ≤ A.ampPacketSpectralDensity κ η := by
  unfold ampPacketSpectralDensity
  positivity

theorem integrable_ampPacketSpectralDensity (κ : ℝ) :
    Integrable (A.ampPacketSpectralDensity κ) volume := by
  have hLp : Integrable (fun η : ℝ =>
      ‖((fourierUnitary (A.ampPacketL2 κ) : SoninL2) : ℝ → ℂ) η‖ ^ 2) volume := by
    have := (Lp.memLp (fourierUnitary (A.ampPacketL2 κ))).integrable_norm_rpow
      (by norm_num) (by norm_num)
    simpa using this
  refine hLp.congr ?_
  filter_upwards [A.fourierUnitary_ampPacketL2_coeFn κ] with η hη
  unfold ampPacketSpectralDensity
  rw [hη]

/-- The band energy of the packet is the band integral of its spectral density. -/
theorem norm_sq_evenFourierCutoff_ampPacketEven_eq_density (t κ : ℝ) :
    ‖evenFourierCutoff t (A.ampPacketEven κ)‖ ^ 2 =
      ∫ ξ : ℝ, (centralInterval t).indicator (A.ampPacketSpectralDensity κ) ξ := by
  rw [A.norm_sq_evenFourierCutoff_ampPacketEven t κ]
  refine integral_congr_ae ?_
  filter_upwards [A.fourierUnitary_ampPacketL2_coeFn κ] with ξ hξ
  rw [norm_sq_indicator]
  by_cases hmem : ξ ∈ centralInterval t
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    unfold ampPacketSpectralDensity
    rw [hξ]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]

/-! ### Modulation shifts the amplitude's spectrum -/

/-- Two bounded measurable weights times the amplitude stay integrable. -/
theorem integrable_char_char_mul_amp {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hf1 : ∀ x, ‖f x‖ ≤ 1) (hg1 : ∀ x, ‖g x‖ ≤ 1) :
    Integrable (fun x : ℝ => f x * (g x * (A.toFun x : ℂ))) := by
  have hprod : ∀ x : ℝ, ‖f x * g x‖ ≤ 1 := by
    intro x
    rw [norm_mul]
    calc ‖f x‖ * ‖g x‖ ≤ 1 * 1 :=
          mul_le_mul (hf1 x) (hg1 x) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have h := A.integrable_char_mul_amp (hf.mul hg) hprod
  exact h.congr (Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)

theorem measurable_char (a : ℝ) :
    Measurable fun x : ℝ => Complex.exp ((↑(2 * Real.pi * a * x) : ℂ) * Complex.I) :=
  Complex.measurable_exp.comp
    ((Complex.continuous_ofReal.measurable.comp (by fun_prop)).mul measurable_const)

theorem measurable_char' (ξ : ℝ) :
    Measurable fun x : ℝ => Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) :=
  Complex.measurable_exp.comp
    ((Complex.continuous_ofReal.measurable.comp (by fun_prop)).mul measurable_const)

theorem norm_char_le (a : ℝ) (x : ℝ) :
    ‖Complex.exp ((↑(2 * Real.pi * a * x) : ℂ) * Complex.I)‖ ≤ 1 := by
  rw [Complex.norm_exp_ofReal_mul_I]

theorem norm_char'_le (ξ : ℝ) (x : ℝ) :
    ‖Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I)‖ ≤ 1 := by
  rw [Complex.norm_exp_ofReal_mul_I]

/-- **Shifted form of the packet's transform.** -/
theorem fourier_ampPacket_eq_shift (a ξ : ℝ) :
    𝓕 (fun x : ℝ => (A.ampPacket (2 * Real.pi * a) x : ℂ)) ξ =
      (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => (A.toFun x : ℂ)) (ξ - a) +
        (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => (A.toFun x : ℂ)) (ξ + a) -
        ((A.ampPacketMean (2 * Real.pi * a) : ℝ) : ℂ) *
          𝓕 (fun x : ℝ => (A.toFun x : ℂ)) ξ := by
  have hpt : ∀ x : ℝ, (A.ampPacket (2 * Real.pi * a) x : ℂ) =
      (2 : ℂ)⁻¹ * (Complex.exp ((↑(2 * Real.pi * a * x) : ℂ) * Complex.I) *
          (A.toFun x : ℂ)) +
        (2 : ℂ)⁻¹ * (Complex.exp ((↑(2 * Real.pi * (-a) * x) : ℂ) * Complex.I) *
          (A.toFun x : ℂ)) -
        ((A.ampPacketMean (2 * Real.pi * a) : ℝ) : ℂ) * (A.toFun x : ℂ) := by
    intro x
    have key : ∀ z : ℂ, (2 : ℂ)⁻¹ * Complex.exp (z * Complex.I) +
        (2 : ℂ)⁻¹ * Complex.exp (-z * Complex.I) = Complex.cos z := by
      intro z
      rw [Complex.cos]
      ring
    have hneg : ((2 * Real.pi * (-a) * x : ℝ) : ℂ) = -((2 * Real.pi * a * x : ℝ) : ℂ) := by
      push_cast
      ring
    have hcos : ((Real.cos ((2 * Real.pi * a) * x) : ℝ) : ℂ) =
        (2 : ℂ)⁻¹ * Complex.exp ((↑(2 * Real.pi * a * x) : ℂ) * Complex.I) +
          (2 : ℂ)⁻¹ * Complex.exp ((↑(2 * Real.pi * (-a) * x) : ℂ) * Complex.I) := by
      rw [show (2 * Real.pi * a) * x = 2 * Real.pi * a * x by ring, Complex.ofReal_cos,
        hneg, ← key ((↑(2 * Real.pi * a * x) : ℂ))]
    show ((A.toFun x * (Real.cos ((2 * Real.pi * a) * x) -
        A.ampPacketMean (2 * Real.pi * a)) : ℝ) : ℂ) = _
    rw [Complex.ofReal_mul, Complex.ofReal_sub, hcos]
    ring
  have hI1 : Integrable (fun x : ℝ =>
      Complex.exp ((↑(2 * Real.pi * a * x) : ℂ) * Complex.I) * (A.toFun x : ℂ)) :=
    A.integrable_char_mul_amp (measurable_char a) (norm_char_le a)
  have hI2 : Integrable (fun x : ℝ =>
      Complex.exp ((↑(2 * Real.pi * (-a) * x) : ℂ) * Complex.I) * (A.toFun x : ℂ)) :=
    A.integrable_char_mul_amp (measurable_char (-a)) (norm_char_le (-a))
  have hI3 : Integrable (fun x : ℝ => (A.toFun x : ℂ)) := A.integrable.ofReal
  have hJ1 : Integrable (fun x : ℝ =>
      Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) *
        (Complex.exp ((↑(2 * Real.pi * a * x) : ℂ) * Complex.I) * (A.toFun x : ℂ))) :=
    A.integrable_char_char_mul_amp (measurable_char' ξ) (measurable_char a)
      (norm_char'_le ξ) (norm_char_le a)
  have hJ2 : Integrable (fun x : ℝ =>
      Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) *
        (Complex.exp ((↑(2 * Real.pi * (-a) * x) : ℂ) * Complex.I) * (A.toFun x : ℂ))) :=
    A.integrable_char_char_mul_amp (measurable_char' ξ) (measurable_char (-a))
      (norm_char'_le ξ) (norm_char_le (-a))
  have hJ3 : Integrable (fun x : ℝ =>
      Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) * (A.toFun x : ℂ)) :=
    A.integrable_char_mul_amp (measurable_char' ξ) (norm_char'_le ξ)
  have hsum : 𝓕 (fun x : ℝ => (A.ampPacket (2 * Real.pi * a) x : ℂ)) ξ =
      (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ =>
          Complex.exp ((↑(2 * Real.pi * a * x) : ℂ) * Complex.I) * (A.toFun x : ℂ)) ξ +
        (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ =>
          Complex.exp ((↑(2 * Real.pi * (-a) * x) : ℂ) * Complex.I) * (A.toFun x : ℂ)) ξ -
        ((A.ampPacketMean (2 * Real.pi * a) : ℝ) : ℂ) *
          𝓕 (fun x : ℝ => (A.toFun x : ℂ)) ξ := by
    rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
      Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
    simp only [smul_eq_mul]
    have hA : Integrable (fun v : ℝ => (2 : ℂ)⁻¹ *
        (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
          (Complex.exp ((↑(2 * Real.pi * a * v) : ℂ) * Complex.I) *
            (A.toFun v : ℂ)))) := hJ1.const_mul _
    have hB : Integrable (fun v : ℝ => (2 : ℂ)⁻¹ *
        (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
          (Complex.exp ((↑(2 * Real.pi * (-a) * v) : ℂ) * Complex.I) *
            (A.toFun v : ℂ)))) := hJ2.const_mul _
    have hAB : Integrable (fun v : ℝ => (2 : ℂ)⁻¹ *
        (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
          (Complex.exp ((↑(2 * Real.pi * a * v) : ℂ) * Complex.I) *
            (A.toFun v : ℂ))) +
        (2 : ℂ)⁻¹ *
        (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
          (Complex.exp ((↑(2 * Real.pi * (-a) * v) : ℂ) * Complex.I) *
            (A.toFun v : ℂ)))) := hA.add hB
    have hC : Integrable (fun v : ℝ =>
        ((A.ampPacketMean (2 * Real.pi * a) : ℝ) : ℂ) *
          (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
            (A.toFun v : ℂ))) := hJ3.const_mul _
    calc ∫ v : ℝ, Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
            (A.ampPacket (2 * Real.pi * a) v : ℂ)
        = ∫ v : ℝ, ((2 : ℂ)⁻¹ * (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
              (Complex.exp ((↑(2 * Real.pi * a * v) : ℂ) * Complex.I) * (A.toFun v : ℂ))) +
            (2 : ℂ)⁻¹ * (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
              (Complex.exp ((↑(2 * Real.pi * (-a) * v) : ℂ) * Complex.I) * (A.toFun v : ℂ))) -
            ((A.ampPacketMean (2 * Real.pi * a) : ℝ) : ℂ) *
              (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
                (A.toFun v : ℂ))) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
          show Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
              (A.ampPacket (2 * Real.pi * a) v : ℂ) = _
          rw [hpt v]
          ring
      _ = ((∫ v : ℝ, (2 : ℂ)⁻¹ * (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
              (Complex.exp ((↑(2 * Real.pi * a * v) : ℂ) * Complex.I) * (A.toFun v : ℂ)))) +
            ∫ v : ℝ, (2 : ℂ)⁻¹ * (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
              (Complex.exp ((↑(2 * Real.pi * (-a) * v) : ℂ) * Complex.I) * (A.toFun v : ℂ)))) -
            ∫ v : ℝ, ((A.ampPacketMean (2 * Real.pi * a) : ℝ) : ℂ) *
              (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
                (A.toFun v : ℂ)) := by
          rw [integral_sub hAB hC, integral_add hA hB]
      _ = _ := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hsum, fourier_exp_mul, fourier_exp_mul]
  congr 2
  rw [sub_neg_eq_add]

/-! ### The band energy bound -/

/-- The pointwise three-term bound for the packet's spectral density. -/
theorem ampPacketSpectralDensity_le (a ξ : ℝ) :
    A.ampPacketSpectralDensity (2 * Real.pi * a) ξ ≤
      3 * ((4 : ℝ)⁻¹ * A.ampSpectralDensity (ξ + (-a)) +
        (4 : ℝ)⁻¹ * A.ampSpectralDensity (ξ + a) +
        (A.ampPacketMean (2 * Real.pi * a)) ^ 2 * A.ampSpectralDensity ξ) := by
  set μ : ℝ := A.ampPacketMean (2 * Real.pi * a) with hμ
  have hsub : ξ - a = ξ + (-a) := by ring
  unfold ampPacketSpectralDensity
  rw [A.fourier_ampPacket_eq_shift a ξ]
  set X : ℂ := (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => (A.toFun x : ℂ)) (ξ - a) with hX
  set Y : ℂ := (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => (A.toFun x : ℂ)) (ξ + a) with hY
  set Z : ℂ := (μ : ℂ) * 𝓕 (fun x : ℝ => (A.toFun x : ℂ)) ξ with hZ
  have hXn : ‖X‖ ^ 2 = (4 : ℝ)⁻¹ * A.ampSpectralDensity (ξ + (-a)) := by
    rw [hX, norm_mul]
    unfold ampSpectralDensity
    rw [← hsub]
    simp only [norm_inv, Complex.norm_ofNat]
    ring
  have hYn : ‖Y‖ ^ 2 = (4 : ℝ)⁻¹ * A.ampSpectralDensity (ξ + a) := by
    rw [hY, norm_mul]
    unfold ampSpectralDensity
    simp only [norm_inv, Complex.norm_ofNat]
    ring
  have hZn : ‖Z‖ ^ 2 = μ ^ 2 * A.ampSpectralDensity ξ := by
    rw [hZ, norm_mul]
    unfold ampSpectralDensity
    rw [Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have htri : ‖X + Y - Z‖ ≤ ‖X‖ + ‖Y‖ + ‖Z‖ := by
    calc ‖X + Y - Z‖ ≤ ‖X + Y‖ + ‖Z‖ := norm_sub_le _ _
      _ ≤ (‖X‖ + ‖Y‖) + ‖Z‖ := by gcongr; exact norm_add_le _ _
  calc ‖X + Y - Z‖ ^ 2 ≤ (‖X‖ + ‖Y‖ + ‖Z‖) ^ 2 := by
        have h0 : (0 : ℝ) ≤ ‖X + Y - Z‖ := norm_nonneg _
        nlinarith [norm_nonneg X, norm_nonneg Y, norm_nonneg Z]
    _ ≤ 3 * (‖X‖ ^ 2 + ‖Y‖ ^ 2 + ‖Z‖ ^ 2) := by
        nlinarith [sq_nonneg (‖X‖ - ‖Y‖), sq_nonneg (‖X‖ - ‖Z‖), sq_nonneg (‖Y‖ - ‖Z‖)]
    _ = _ := by rw [hXn, hYn, hZn]

/-- The three-term bound integrated over an arbitrary measurable band. -/
theorem integral_indicator_ampPacketSpectralDensity_le (a : ℝ) (S : Set ℝ)
    (hS : MeasurableSet S) :
    ∫ ξ : ℝ, S.indicator (A.ampPacketSpectralDensity (2 * Real.pi * a)) ξ ≤
      3 * ((4 : ℝ)⁻¹ * (∫ ξ : ℝ, S.indicator
              (fun η : ℝ => A.ampSpectralDensity (η + (-a))) ξ) +
        (4 : ℝ)⁻¹ * (∫ ξ : ℝ, S.indicator (fun η : ℝ => A.ampSpectralDensity (η + a)) ξ) +
        (A.ampPacketMean (2 * Real.pi * a)) ^ 2 *
          ∫ ξ : ℝ, S.indicator A.ampSpectralDensity ξ) := by
  set μ : ℝ := A.ampPacketMean (2 * Real.pi * a) with hμ
  set D : ℝ → ℝ := A.ampSpectralDensity with hD
  have hDnn : ∀ η, 0 ≤ D η := A.ampSpectralDensity_nonneg
  have hDint : Integrable D volume := A.integrable_ampSpectralDensity
  have hLint : Integrable (S.indicator (A.ampPacketSpectralDensity (2 * Real.pi * a))) volume :=
    (A.integrable_ampPacketSpectralDensity (2 * Real.pi * a)).indicator hS
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
  have hmono : ∫ ξ : ℝ, S.indicator (A.ampPacketSpectralDensity (2 * Real.pi * a)) ξ ≤
      ∫ ξ : ℝ, 3 * ((4 : ℝ)⁻¹ * S.indicator (fun η : ℝ => D (η + (-a))) ξ +
        (4 : ℝ)⁻¹ * S.indicator (fun η : ℝ => D (η + a)) ξ +
        μ ^ 2 * S.indicator D ξ) := by
    refine integral_mono hLint hRint fun ξ => ?_
    by_cases hmem : ξ ∈ S
    · simp only [Set.indicator_of_mem hmem]
      exact A.ampPacketSpectralDensity_le a ξ
    · simp only [Set.indicator_of_notMem hmem]
      norm_num
  refine hmono.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_add hAB hC, integral_add hA hB,
    integral_const_mul, integral_const_mul, integral_const_mul]

/-- **Band energy bound.** -/
theorem norm_sq_evenFourierCutoff_ampPacketEven_le (t a : ℝ) :
    ‖evenFourierCutoff t (A.ampPacketEven (2 * Real.pi * a))‖ ^ 2 ≤
      3 * ((2 : ℝ)⁻¹ * (∫ η : ℝ, {η : ℝ | |a| - t ≤ |η|}.indicator A.ampSpectralDensity η) +
        (A.ampPacketMean (2 * Real.pi * a)) ^ 2 * ∫ η : ℝ, A.ampSpectralDensity η) := by
  set μ : ℝ := A.ampPacketMean (2 * Real.pi * a) with hμ
  set D : ℝ → ℝ := A.ampSpectralDensity with hD
  have hDnn : ∀ η, 0 ≤ D η := A.ampSpectralDensity_nonneg
  have hDint : Integrable D volume := A.integrable_ampSpectralDensity
  have hstart := A.integral_indicator_ampPacketSpectralDensity_le a (centralInterval t)
    (measurableSet_centralInterval t)
  have hT1 := integral_indicator_centralInterval_comp_add_le hDint hDnn t (-a)
  have hT2 := integral_indicator_centralInterval_comp_add_le hDint hDnn t a
  have hR3 : Integrable ((centralInterval t).indicator D) volume :=
    hDint.indicator (measurableSet_centralInterval t)
  have hT3 : ∫ ξ : ℝ, (centralInterval t).indicator D ξ ≤ ∫ η : ℝ, D η := by
    refine integral_mono hR3 hDint fun ξ => ?_
    by_cases hmem : ξ ∈ centralInterval t
    · rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem]
      exact hDnn ξ
  have hμsq : (0 : ℝ) ≤ μ ^ 2 := sq_nonneg μ
  rw [A.norm_sq_evenFourierCutoff_ampPacketEven_eq_density t (2 * Real.pi * a)]
  refine hstart.trans ?_
  rw [abs_neg] at hT1
  nlinarith [hT1, hT2, hT3, hμsq, mul_le_mul_of_nonneg_left hT3 hμsq]

/-- The energy outside a central band, in terms of the spectral density. -/
theorem norm_sq_sub_evenFourierCutoff_ampPacketEven_le_outer (t κ : ℝ) :
    ‖A.ampPacketEven κ - evenFourierCutoff t (A.ampPacketEven κ)‖ ^ 2 ≤
      ∫ ξ : ℝ, {ξ : ℝ | t ≤ |ξ|}.indicator (A.ampPacketSpectralDensity κ) ξ := by
  set F := fourierUnitary (A.ampPacketL2 κ) with hF
  have hcoeDiff : ((A.ampPacketEven κ - evenFourierCutoff t (A.ampPacketEven κ) :
      evenSubspace) : SoninL2) =
      fourierUnitary.symm (F - indicatorCutoff (centralInterval t)
        (measurableSet_centralInterval t) F) := by
    have h1 : ((A.ampPacketEven κ : evenSubspace) : SoninL2) = fourierUnitary.symm F := by
      rw [hF, LinearIsometryEquiv.symm_apply_apply]
      exact A.coe_ampPacketEven κ
    have h2 : ((evenFourierCutoff t (A.ampPacketEven κ) : evenSubspace) : SoninL2) =
        fourierUnitary.symm (indicatorCutoff (centralInterval t)
          (measurableSet_centralInterval t) F) := rfl
    rw [Submodule.coe_sub, h1, h2, ← map_sub]
  have hnorm : ‖A.ampPacketEven κ - evenFourierCutoff t (A.ampPacketEven κ)‖ =
      ‖F - indicatorCutoff (centralInterval t) (measurableSet_centralInterval t) F‖ := by
    rw [show ‖A.ampPacketEven κ - evenFourierCutoff t (A.ampPacketEven κ)‖ =
      ‖((A.ampPacketEven κ - evenFourierCutoff t (A.ampPacketEven κ) :
        evenSubspace) : SoninL2)‖ from rfl, hcoeDiff]
    exact fourierUnitary.symm.norm_map _
  rw [hnorm, norm_sq_eq_integral]
  have hLint : Integrable (fun ξ : ℝ =>
      ‖((F - indicatorCutoff (centralInterval t)
        (measurableSet_centralInterval t) F : SoninL2) : ℝ → ℂ) ξ‖ ^ 2) volume := by
    have := (Lp.memLp (F - indicatorCutoff (centralInterval t)
      (measurableSet_centralInterval t) F)).integrable_norm_rpow (by norm_num) (by norm_num)
    simpa using this
  have hRint : Integrable ({ξ : ℝ | t ≤ |ξ|}.indicator (A.ampPacketSpectralDensity κ)) volume :=
    (A.integrable_ampPacketSpectralDensity κ).indicator (measurableSet_outer t)
  refine integral_mono_ae hLint hRint ?_
  filter_upwards [Lp.coeFn_sub F (indicatorCutoff (centralInterval t)
      (measurableSet_centralInterval t) F),
    indicatorCutoff_ae (centralInterval t) (measurableSet_centralInterval t) F,
    A.fourierUnitary_ampPacketL2_coeFn κ] with ξ hsub hind hFval
  rw [hsub]
  simp only [Pi.sub_apply, hind]
  by_cases hmem : ξ ∈ centralInterval t
  · rw [Set.indicator_of_mem hmem, sub_self, norm_zero]
    have hz : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [hz]
    exact Set.indicator_nonneg (fun x _ => A.ampPacketSpectralDensity_nonneg κ x) ξ
  · rw [Set.indicator_of_notMem hmem, sub_zero]
    have hout : ξ ∈ {ξ : ℝ | t ≤ |ξ|} := by
      simp only [Set.mem_setOf_eq]
      by_contra hlt
      push Not at hlt
      exact hmem (abs_le.mp hlt.le)
    rw [Set.indicator_of_mem hout]
    unfold ampPacketSpectralDensity
    rw [hFval]

/-- **Outer band energy bound.** -/
theorem norm_sq_sub_evenFourierCutoff_ampPacketEven_le (t a : ℝ) :
    ‖A.ampPacketEven (2 * Real.pi * a) -
        evenFourierCutoff t (A.ampPacketEven (2 * Real.pi * a))‖ ^ 2 ≤
      3 * ((2 : ℝ)⁻¹ * (∫ η : ℝ, {η : ℝ | t - |a| ≤ |η|}.indicator A.ampSpectralDensity η) +
        (A.ampPacketMean (2 * Real.pi * a)) ^ 2 * ∫ η : ℝ, A.ampSpectralDensity η) := by
  set μ : ℝ := A.ampPacketMean (2 * Real.pi * a) with hμ
  set D : ℝ → ℝ := A.ampSpectralDensity with hD
  have hDnn : ∀ η, 0 ≤ D η := A.ampSpectralDensity_nonneg
  have hDint : Integrable D volume := A.integrable_ampSpectralDensity
  have hstart := A.norm_sq_sub_evenFourierCutoff_ampPacketEven_le_outer t (2 * Real.pi * a)
  have hband := A.integral_indicator_ampPacketSpectralDensity_le a {ξ : ℝ | t ≤ |ξ|}
    (measurableSet_outer t)
  have hT1 := integral_indicator_outer_comp_add_le hDint hDnn t (-a)
  have hT2 := integral_indicator_outer_comp_add_le hDint hDnn t a
  rw [abs_neg] at hT1
  have hT3 : ∫ ξ : ℝ, {ξ : ℝ | t ≤ |ξ|}.indicator D ξ ≤ ∫ η : ℝ, D η := by
    refine integral_mono (hDint.indicator (measurableSet_outer t)) hDint fun ξ => ?_
    by_cases hmem : ξ ∈ {ξ : ℝ | t ≤ |ξ|}
    · rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem]
      exact hDnn ξ
  have hμsq : (0 : ℝ) ≤ μ ^ 2 := sq_nonneg μ
  refine hstart.trans (hband.trans ?_)
  nlinarith [hT1, hT2, hT3, hμsq, mul_le_mul_of_nonneg_left hT3 hμsq]

/-! ### Frequency concentration along a clock -/

/-- **Low band escape.**  With aperture and carrier on a common clock and the aperture rate
strictly smaller, the packet's energy below the aperture vanishes. -/
theorem tendsto_norm_evenFourierCutoff_ampPacketEven_scaled
    (q a₀ : ℝ) (ha₀ : 0 < a₀) (hq : a₀ < q)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ => ‖evenFourierCutoff (r n * a₀)
        (A.ampPacketEven (2 * Real.pi * (r n * q)))‖) atTop (𝓝 0) := by
  have hqpos : 0 < q := ha₀.trans hq
  have hgap : ∀ n : ℕ, |r n * q| - r n * a₀ = r n * (q - a₀) := by
    intro n
    rw [abs_of_pos (mul_pos (hrpos n) hqpos)]
    ring
  have hgapTendsto : Tendsto (fun n : ℕ => r n * (q - a₀)) atTop atTop :=
    Filter.Tendsto.atTop_mul_const (by linarith : (0 : ℝ) < q - a₀) hr
  have hTail := A.tendsto_integral_indicator_outer_ampSpectralDensity
    (fun n : ℕ => r n * (q - a₀)) hgapTendsto
  have hfreq : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => r n * q) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hqpos hr
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi) h1
  have hMean : Tendsto (fun n : ℕ => A.ampPacketMean (2 * Real.pi * (r n * q)))
      atTop (𝓝 0) := A.tendsto_ampPacketMean_atTop.comp hfreq
  have hmaj : Tendsto (fun n : ℕ =>
      3 * ((2 : ℝ)⁻¹ * (∫ η : ℝ, {η : ℝ | r n * (q - a₀) ≤ |η|}.indicator
              A.ampSpectralDensity η) +
        (A.ampPacketMean (2 * Real.pi * (r n * q))) ^ 2 *
          ∫ η : ℝ, A.ampSpectralDensity η)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ *
        ∫ η : ℝ, {η : ℝ | r n * (q - a₀) ≤ |η|}.indicator A.ampSpectralDensity η)
        atTop (𝓝 0) := by
      simpa using hTail.const_mul ((2 : ℝ)⁻¹)
    have h2 : Tendsto (fun n : ℕ =>
        (A.ampPacketMean (2 * Real.pi * (r n * q))) ^ 2 *
          ∫ η : ℝ, A.ampSpectralDensity η) atTop (𝓝 0) := by
      simpa using (hMean.pow 2).mul_const (∫ η : ℝ, A.ampSpectralDensity η)
    simpa using (h1.add h2).const_mul (3 : ℝ)
  have hsq : Tendsto (fun n : ℕ => ‖evenFourierCutoff (r n * a₀)
      (A.ampPacketEven (2 * Real.pi * (r n * q)))‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hmaj
    have hbnd := A.norm_sq_evenFourierCutoff_ampPacketEven_le (r n * a₀) (r n * q)
    rw [hgap n] at hbnd
    exact hbnd
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun n => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

/-- **High band capture.**  With the aperture on the same clock as the carrier but at a strictly
larger rate, the packet loses no energy above the aperture. -/
theorem tendsto_norm_sub_evenFourierCutoff_ampPacketEven_scaled
    (q b₀ : ℝ) (hq : 0 < q) (hqb : q < b₀)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ => ‖A.ampPacketEven (2 * Real.pi * (r n * q)) -
        evenFourierCutoff (r n * b₀) (A.ampPacketEven (2 * Real.pi * (r n * q)))‖)
      atTop (𝓝 0) := by
  have hgap : ∀ n : ℕ, r n * b₀ - |r n * q| = r n * (b₀ - q) := by
    intro n
    rw [abs_of_pos (mul_pos (hrpos n) hq)]
    ring
  have hgapTendsto : Tendsto (fun n : ℕ => r n * (b₀ - q)) atTop atTop :=
    Filter.Tendsto.atTop_mul_const (by linarith : (0 : ℝ) < b₀ - q) hr
  have hTail := A.tendsto_integral_indicator_outer_ampSpectralDensity
    (fun n : ℕ => r n * (b₀ - q)) hgapTendsto
  have hfreq : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => r n * q) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hq hr
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi) h1
  have hMean : Tendsto (fun n : ℕ => A.ampPacketMean (2 * Real.pi * (r n * q)))
      atTop (𝓝 0) := A.tendsto_ampPacketMean_atTop.comp hfreq
  have hmaj : Tendsto (fun n : ℕ =>
      3 * ((2 : ℝ)⁻¹ * (∫ η : ℝ, {η : ℝ | r n * (b₀ - q) ≤ |η|}.indicator
              A.ampSpectralDensity η) +
        (A.ampPacketMean (2 * Real.pi * (r n * q))) ^ 2 *
          ∫ η : ℝ, A.ampSpectralDensity η)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ *
        ∫ η : ℝ, {η : ℝ | r n * (b₀ - q) ≤ |η|}.indicator A.ampSpectralDensity η)
        atTop (𝓝 0) := by
      simpa using hTail.const_mul ((2 : ℝ)⁻¹)
    have h2 : Tendsto (fun n : ℕ =>
        (A.ampPacketMean (2 * Real.pi * (r n * q))) ^ 2 *
          ∫ η : ℝ, A.ampSpectralDensity η) atTop (𝓝 0) := by
      simpa using (hMean.pow 2).mul_const (∫ η : ℝ, A.ampSpectralDensity η)
    simpa using (h1.add h2).const_mul (3 : ℝ)
  have hsq : Tendsto (fun n : ℕ => ‖A.ampPacketEven (2 * Real.pi * (r n * q)) -
      evenFourierCutoff (r n * b₀) (A.ampPacketEven (2 * Real.pi * (r n * q)))‖ ^ 2)
      atTop (𝓝 0) := by
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hmaj
    have hbnd := A.norm_sq_sub_evenFourierCutoff_ampPacketEven_le (r n * b₀) (r n * q)
    rw [hgap n] at hbnd
    exact hbnd
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun n => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

end AnnulusAmplitude

end RHTower


