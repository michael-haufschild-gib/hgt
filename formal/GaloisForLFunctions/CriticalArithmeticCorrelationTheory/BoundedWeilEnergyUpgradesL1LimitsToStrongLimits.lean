import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheGammaFormPaysEveryFrequencyAboveAThreshold
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ThePrimeAndPoleFormsAreContinuousInTheWeightedNorm
import GaloisForLFunctions.HTGeometry.L2GridApproximation
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.WeilsFormIsContinuousInTheLevyNorm
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Bounded Weil energy upgrades `L¹` limits to strong limits

A sequence of smooth compactly supported tests with bounded Weil form, bounded `L²` mass and bounded
eighth exponential mass has uniformly small high frequencies, because the Gamma weight grows like
`log |r|` and the prime and pole parts are bounded by the weighted mass.

Small high frequencies and an `L¹` limit `F` give `‖U_N − F‖₂ → 0`: the low frequencies converge
uniformly, and Fatou passes from the Cauchy bound to the limit, so no Plancherel theorem for `F` is
needed (`tendsto_integral_sq_sub_of_high_tails`). The strong limit carries the prime sum and the pole
moments with it (`tendsto_prime_and_pole_of_strong_limit`), while the truncated Gamma form converges
along every `L¹` limit (`tendsto_lowGammaForm`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Zeta23 RHTower
open scoped ENNReal
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticCastelnuovoSeveri ArithmeticPositivityTheory SpacingScaleHarmonicAnalysis

/-! ### The transform of an integrable real function -/

private theorem norm_exp_kernel (r u : ℝ) :
    ‖Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))‖ = 1 := by
  have h : Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private theorem norm_cx_kernel (f : ℝ → ℝ) (r u : ℝ) :
    ‖cx f u * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))‖ = ‖f u‖ := by
  rw [norm_mul, norm_exp_kernel, mul_one]
  simp only [cx, Complex.norm_real]

private theorem integrable_cx_kernel {f : ℝ → ℝ} (hf : Integrable f) (r : ℝ) :
    Integrable (fun u => cx f u * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) := by
  refine hf.norm.mono' ?_ (Eventually.of_forall fun u => (norm_cx_kernel f r u).le)
  have hm : AEStronglyMeasurable (cx f) volume := (hf.ofReal (𝕜 := ℂ)).aestronglyMeasurable
  exact hm.mul (Continuous.aestronglyMeasurable (by fun_prop))

/-- The transform of an integrable real function is bounded by its `L¹` norm. -/
theorem norm_paperFT_le (f : ℝ → ℝ) (r : ℝ) :
    ‖paperFT (cx f) r‖ ≤ ∫ u, ‖f u‖ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  exact integral_congr_ae (Eventually.of_forall fun u => norm_cx_kernel f r u)

/-- The transform is additive on integrable real functions. -/
theorem paperFT_cx_sub {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) (r : ℝ) :
    paperFT (cx fun u => f u - g u) r = paperFT (cx f) r - paperFT (cx g) r := by
  change (∫ u, cx (fun u => f u - g u) u * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) =
    (∫ u, cx f u * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) -
      ∫ u, cx g u * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))
  rw [← integral_sub (integrable_cx_kernel hf r) (integrable_cx_kernel hg r)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [cx]
  push_cast
  ring

/-- Real frequencies see an `L¹` perturbation uniformly. -/
theorem norm_paperFT_sub_le {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) (r : ℝ) :
    ‖paperFT (cx f) r - paperFT (cx g) r‖ ≤ ∫ u, ‖f u - g u‖ := by
  rw [← paperFT_cx_sub hf hg]
  exact norm_paperFT_le _ r

/-- The transform of an integrable real function is continuous on real frequencies. -/
theorem continuous_paperFT_cx {f : ℝ → ℝ} (hf : Integrable f) :
    Continuous fun r : ℝ => paperFT (cx f) r := by
  refine continuous_of_dominated (bound := fun u => ‖f u‖)
    (fun r => (integrable_cx_kernel hf r).aestronglyMeasurable)
    (fun r => Eventually.of_forall fun u => (norm_cx_kernel f r u).le) hf.norm
    (Eventually.of_forall fun u => ?_)
  fun_prop

/-! ### The truncated Gamma form -/

/-- The Gamma form truncated to the frequencies `|r| < T`. -/
def lowGammaForm (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  1 / (2 * Real.pi) * ∫ r in (highFrequencies T)ᶜ, ‖paperFT (cx f) r‖ ^ 2 * EF.gammaBracket r

theorem compl_highFrequencies_subset (T : ℝ) : (highFrequencies T)ᶜ ⊆ Set.Icc (-T) T := by
  intro r hr
  have h : |r| < T := not_le.mp hr
  exact abs_le.mp h.le

private theorem volume_compl_highFrequencies_ne_top (T : ℝ) :
    volume (highFrequencies T)ᶜ ≠ ⊤ :=
  ((measure_mono (compl_highFrequencies_subset T)).trans_lt isCompact_Icc.measure_lt_top).ne

/-- **The truncated Gamma form passes to every `L¹` limit.** -/
theorem tendsto_lowGammaForm {l : Filter ℕ} [IsCountablyGenerated l] {U : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hU : ∀ N, Integrable (U N)) (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y, ‖U N y - F y‖) l (𝓝 0)) (T : ℝ) :
    Tendsto (fun N => lowGammaForm (U N) T) l (𝓝 (lowGammaForm F T)) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    WeilHerglotz.continuous_gammaBracket.continuousOn
  have hHm := measurableSet_highFrequencies T
  let C : ℝ := (∫ y, ‖F y‖) + 1
  have hC : 0 ≤ C := by
    have : 0 ≤ ∫ y, ‖F y‖ := integral_nonneg fun _ => norm_nonneg _
    dsimp only [C]; linarith only [this]
  have hsmall : ∀ᶠ N in l, (∫ y, ‖U N y - F y‖) < 1 := hL1.eventually (gt_mem_nhds one_pos)
  have hbdd : ∀ᶠ N in l, (∫ y, ‖U N y‖) ≤ C := by
    filter_upwards [hsmall] with N hN
    have hn : Integrable fun y => ‖U N y - F y‖ := ((hU N).sub hF).norm
    have hi : Integrable fun y => ‖F y‖ + ‖U N y - F y‖ := hF.norm.add hn
    have hle : (∫ y, ‖U N y‖) ≤ ∫ y, (‖F y‖ + ‖U N y - F y‖) := by
      refine integral_mono (hU N).norm hi fun y => ?_
      have h := norm_add_le (F y) (U N y - F y)
      simp only [add_sub_cancel] at h
      exact h
    rw [integral_add hF.norm hn] at hle
    dsimp only [C]
    linarith only [hle, hN]
  have hlim : Tendsto (fun N => ∫ r in (highFrequencies T)ᶜ,
      ‖paperFT (cx (U N)) r‖ ^ 2 * EF.gammaBracket r) l
      (𝓝 (∫ r in (highFrequencies T)ᶜ, ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => C ^ 2 * |B|) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun N => ?_
      exact (((continuous_paperFT_cx (hU N)).norm.pow 2).mul
        WeilHerglotz.continuous_gammaBracket).aestronglyMeasurable
    · filter_upwards [hbdd] with N hN
      refine (ae_restrict_iff' hHm.compl).mpr (Eventually.of_forall fun r hr => ?_)
      have hG := hB r (compl_highFrequencies_subset T hr)
      have hn := (norm_paperFT_le (U N) r).trans hN
      rw [norm_mul, norm_pow, norm_norm]
      refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hn 2) ?_ (norm_nonneg _) (by positivity)
      exact hG.trans (le_abs_self B)
    · exact integrableOn_const (volume_compl_highFrequencies_ne_top T)
    · refine Eventually.of_forall fun r => ?_
      have hpt : Tendsto (fun N => paperFT (cx (U N)) r) l (𝓝 (paperFT (cx F) r)) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        exact squeeze_zero (fun _ => norm_nonneg _)
          (fun N => norm_paperFT_sub_le (hU N) hF r) hL1
      exact (hpt.norm.pow 2).mul_const _
  exact hlim.const_mul _

/-- **The Gamma form keeps its low part and pays the far frequencies.** Above the threshold
`e^{G₀}` the Gamma weight is nonnegative, so the band `T ≤ |r| < T'` can be dropped. -/
theorem lowGammaForm_add_high_le_archForm {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {T T' : ℝ}
    (hT : Real.exp factorialSpanGammaOffset ≤ T) (hTT' : T ≤ T') :
    lowGammaForm f T + (Real.log T' - factorialSpanGammaOffset) * highFourierMass f T' ≤
      archForm f := by
  let F : ℝ → ℝ := fun r => ‖paperFT (cx f) r‖ ^ 2
  let k : ℝ → ℝ := fun r => F r * EF.gammaBracket r
  have hFi : Integrable F := integrable_normSq_paperFT_ofReal hf hfc
  have hki : Integrable k := integrable_normSq_paperFT_mul_gammaBracket hf hfc
  have hT0 : 0 < T := (Real.exp_pos _).trans_le hT
  have hT'0 : 0 < T' := hT0.trans_le hTT'
  have hlogT : 0 ≤ Real.log T - factorialSpanGammaOffset := by
    have h := Real.log_le_log (Real.exp_pos _) hT
    rw [Real.log_exp] at h
    linarith only [h]
  have hH := measurableSet_highFrequencies T
  have hH' := measurableSet_highFrequencies T'
  have hsplit := integral_add_compl hH hki
  have hpos : 0 ≤ᵐ[volume.restrict (highFrequencies T)] k :=
    (ae_restrict_iff' hH).mpr (Eventually.of_forall fun r hr =>
      mul_nonneg (sq_nonneg _) (hlogT.trans (gammaBracket_ge_log_of_le_abs hT0 hr)))
  have hsub : highFrequencies T' ≤ᵐ[volume] highFrequencies T :=
    (show highFrequencies T' ≤ highFrequencies T from fun r hr => hTT'.trans hr).eventuallyLE
  have hmono := setIntegral_mono_set hki.integrableOn hpos hsub
  have hlow : (∫ r in highFrequencies T', (Real.log T' - factorialSpanGammaOffset) * F r) ≤
      ∫ r in highFrequencies T', k r :=
    setIntegral_mono_on (hFi.integrableOn.const_mul _) hki.integrableOn hH' fun r hr => by
      have h := mul_le_mul_of_nonneg_left (gammaBracket_ge_log_of_le_abs hT'0 hr)
        (sq_nonneg ‖paperFT (cx f) r‖)
      dsimp only [k, F]
      nlinarith only [h]
  rw [integral_const_mul] at hlow
  have harch : archForm f = 1 / (2 * Real.pi) * ∫ r, k r := rfl
  have hhigh : highFourierMass f T' = 1 / (2 * Real.pi) * ∫ r in highFrequencies T', F r := rfl
  have hlowdef : lowGammaForm f T = 1 / (2 * Real.pi) * ∫ r in (highFrequencies T)ᶜ, k r := rfl
  rw [harch, hhigh, hlowdef, ← hsplit]
  have hpi : 0 < 1 / (2 * Real.pi) := by positivity
  have h := mul_le_mul_of_nonneg_left (hlow.trans hmono) hpi.le
  nlinarith only [h]

/-- Bounded arch energy keeps the mass above `T` of order `1 / log T`. -/
theorem highFourierMass_le_of_archForm {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {T : ℝ} (hT : Real.exp (factorialSpanGammaOffset + 1) ≤ T) :
    (Real.log T - factorialSpanGammaOffset) * highFourierMass f T ≤
      archForm f + (factorialSpanGammaOffset + Real.log 2) * ∫ u, f u ^ 2 := by
  have hT0 : 0 < T := (Real.exp_pos _).trans_le hT
  have hb := archForm_ge_high_band hf hfc hT0 le_rfl
  rw [sub_self, zero_mul, add_zero] at hb
  have hsplit := lowFourierMass_add_highFourierMass hf hfc T
  have hhigh := highFourierMass_nonneg f T
  have hlowle : lowFourierMass f T ≤ ∫ u, f u ^ 2 := by linarith only [hsplit, hhigh]
  have hd : 0 ≤ factorialSpanGammaOffset + Real.log 2 :=
    add_nonneg factorialSpanGammaOffset_nonneg (Real.log_nonneg one_le_two)
  have h := mul_le_mul_of_nonneg_left hlowle hd
  linarith only [hb, h]

/-- The Euclidean distance of two tests splits into `L¹` at low frequency and high mass. -/
theorem integral_sq_sub_le {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {T : ℝ} (hT : 0 < T) :
    (∫ u, (f u - g u) ^ 2) ≤ T / Real.pi * (∫ u, ‖f u - g u‖) ^ 2 +
      2 * highFourierMass f T + 2 * highFourierMass g T := by
  let d : ℝ → ℝ := fun u => f u - g u
  have hd : ContDiff ℝ 2 d := hf.sub hg
  have hdc : HasCompactSupport d := hfc.sub hgc
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfc
  have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hsplit := lowFourierMass_add_highFourierMass hd hdc T
  let A : ℝ := ∫ u, ‖f u - g u‖
  have hA0 : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hDi : Integrable (fun r : ℝ => ‖paperFT (cx d) r‖ ^ 2) :=
    integrable_normSq_paperFT_ofReal hd hdc
  have hHm := measurableSet_highFrequencies T
  -- low frequencies are controlled by the `L¹` norm
  have hlow : lowFourierMass d T ≤ T / Real.pi * A ^ 2 := by
    have h1 : (∫ r in (highFrequencies T)ᶜ, ‖paperFT (cx d) r‖ ^ 2) ≤
        ∫ r in Set.Icc (-T) T, ‖paperFT (cx d) r‖ ^ 2 :=
      setIntegral_mono_set hDi.integrableOn (Eventually.of_forall fun _ => sq_nonneg _)
        (show (highFrequencies T)ᶜ ≤ Set.Icc (-T) T from
          compl_highFrequencies_subset T).eventuallyLE
    have h2 : (∫ r in Set.Icc (-T) T, ‖paperFT (cx d) r‖ ^ 2) ≤
        ∫ _r in Set.Icc (-T) T, A ^ 2 :=
      setIntegral_mono_on hDi.integrableOn (integrableOn_const (by simp))
        measurableSet_Icc fun r _ =>
          pow_le_pow_left₀ (norm_nonneg _) (norm_paperFT_le d r) 2
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith only [hT])] at h2
    have hpi : 0 < 1 / (2 * Real.pi) := by positivity
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hpi.le
    refine h3.trans_eq ?_
    field_simp
    ring
  -- high frequencies split by the triangle inequality
  have hhigh : highFourierMass d T ≤ 2 * highFourierMass f T + 2 * highFourierMass g T := by
    have hFi : Integrable (fun r : ℝ => ‖paperFT (cx f) r‖ ^ 2) :=
      integrable_normSq_paperFT_ofReal hf hfc
    have hGi : Integrable (fun r : ℝ => ‖paperFT (cx g) r‖ ^ 2) :=
      integrable_normSq_paperFT_ofReal hg hgc
    have h1 : (∫ r in highFrequencies T, ‖paperFT (cx d) r‖ ^ 2) ≤
        ∫ r in highFrequencies T, (2 * ‖paperFT (cx f) r‖ ^ 2 + 2 * ‖paperFT (cx g) r‖ ^ 2) :=
      setIntegral_mono_on hDi.integrableOn
        ((hFi.integrableOn.const_mul 2).add (hGi.integrableOn.const_mul 2)) hHm fun r _ => by
          have h := paperFT_cx_sub hfi hgi r
          change ‖paperFT (cx (fun u => f u - g u)) r‖ ^ 2 ≤ _
          rw [h]
          have hn := norm_sub_le (paperFT (cx f) r) (paperFT (cx g) r)
          have hp := pow_le_pow_left₀ (norm_nonneg _) hn 2
          nlinarith only [hp, sq_nonneg (‖paperFT (cx f) r‖ - ‖paperFT (cx g) r‖)]
    rw [integral_add (hFi.integrableOn.const_mul 2) (hGi.integrableOn.const_mul 2),
      integral_const_mul, integral_const_mul] at h1
    have hpi : 0 < 1 / (2 * Real.pi) := by positivity
    have h := mul_le_mul_of_nonneg_left h1 hpi.le
    unfold highFourierMass
    nlinarith only [h]
  change (∫ u, d u ^ 2) ≤ _
  linarith only [hsplit, hlow, hhigh]

/-! ### From `L¹` limits to `L²` limits -/

/-- An `L¹` limit along a filter is an almost everywhere limit along a subsequence. -/
theorem exists_seq_ae_tendsto_of_L1 {l : Filter ℕ} [NeBot l] [IsCountablyGenerated l]
    {U : ℕ → ℝ → ℝ} {F : ℝ → ℝ} (hU : ∀ N, Integrable (U N)) (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y, ‖U N y - F y‖) l (𝓝 0)) :
    ∃ s : ℕ → ℕ, Tendsto s atTop l ∧
      ∀ᵐ y, Tendsto (fun k => U (s k) y) atTop (𝓝 (F y)) := by
  have hlp : Tendsto (fun n => eLpNorm (U n - F) 1) l (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.tendsto 0 |>.comp hL1
    simp only [ENNReal.ofReal_zero] at h
    refine h.congr fun n => ?_
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hU n).sub hF)]
    simp only [Pi.sub_apply, Function.comp_def]
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    (fun n => (hU n).aestronglyMeasurable) hF.aestronglyMeasurable hlp
  exact hmeasure.exists_seq_tendsto_ae'

/-- The real integral bound as an `eLpNorm` bound. -/
theorem eLpNorm_two_le_of_integral_sq_le {h : ℝ → ℝ} (hm : MemLp h 2 (volume : Measure ℝ)) {ε : ℝ}
    (hle : (∫ y, h y ^ 2) ≤ ε) : eLpNorm h 2 volume ≤ ENNReal.ofReal (Real.sqrt ε) := by
  have he : eLpNorm h 2 volume = ENNReal.ofReal ‖hm.toLp h‖ := by
    rw [Lp.norm_toLp, ENNReal.ofReal_toReal hm.eLpNorm_ne_top]
  rw [he]
  refine ENNReal.ofReal_le_ofReal (Real.le_sqrt_of_sq_le ?_)
  rw [HTGeometry.norm_toLp_sq]
  exact hle

/-- An `eLpNorm` bound as a real integral bound. -/
theorem integral_sq_le_of_eLpNorm_two_le {g : ℝ → ℝ} (hm : AEStronglyMeasurable g volume) {ε : ℝ}
    (hε : 0 ≤ ε) (hle : eLpNorm g 2 volume ≤ ENNReal.ofReal (Real.sqrt ε)) :
    MemLp g 2 (volume : Measure ℝ) ∧ (∫ y, g y ^ 2) ≤ ε := by
  have hmem : MemLp g 2 (volume : Measure ℝ) := ⟨hm, hle.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hmem, ?_⟩
  rw [← HTGeometry.norm_toLp_sq hmem, Lp.norm_toLp]
  have h := ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg ε) hle
  calc (eLpNorm g 2 volume).toReal ^ 2 ≤ Real.sqrt ε ^ 2 :=
        pow_le_pow_left₀ ENNReal.toReal_nonneg h 2
    _ = ε := Real.sq_sqrt hε

/-- **Small high frequencies upgrade an `L¹` limit to an `L²` limit.** -/
theorem eventually_integral_sq_sub_le_of_high_tails {l : Filter ℕ} [NeBot l]
    [IsCountablyGenerated l] {U : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hU : ∀ N, ContDiff ℝ 2 (U N)) (hUc : ∀ N, HasCompactSupport (U N)) (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y, ‖U N y - F y‖) l (𝓝 0))
    (htail : ∀ ε > 0, ∃ T > 0, ∀ᶠ N in l, highFourierMass (U N) T ≤ ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in l, MemLp (fun y => U N y - F y) 2 (volume : Measure ℝ) ∧
      (∫ y, (U N y - F y) ^ 2) ≤ ε := by
  have hUi : ∀ N, Integrable (U N) := fun N =>
    (hU N).continuous.integrable_of_hasCompactSupport (hUc N)
  obtain ⟨T, hT, hHM⟩ := htail (ε / 8) (by positivity)
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = Real.sqrt (ε * Real.pi / (8 * T)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact Real.sqrt_pos.mpr (by positivity)
  have hδsq : T / Real.pi * (2 * δ) ^ 2 = ε / 2 := by
    rw [mul_pow, hδ, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have hclose : ∀ᶠ N in l, (∫ y, ‖U N y - F y‖) < δ := hL1.eventually (gt_mem_nhds hδ0)
  obtain ⟨s, hsl, hs⟩ := exists_seq_ae_tendsto_of_L1 hUi hF hL1
  filter_upwards [hHM, hclose] with N hN1 hN2
  have hbound : ∀ᶠ k in atTop, eLpNorm (fun y => U N y - U (s k) y) 2 volume ≤
      ENNReal.ofReal (Real.sqrt ε) := by
    filter_upwards [hsl.eventually hHM, hsl.eventually hclose] with k hk1 hk2
    have hM : MemLp (fun y => U N y - U (s k) y) 2 (volume : Measure ℝ) :=
      ((hU N).sub (hU (s k))).continuous.memLp_of_hasCompactSupport ((hUc N).sub (hUc (s k)))
    refine eLpNorm_two_le_of_integral_sq_le hM ?_
    have h := integral_sq_sub_le (hU N) (hUc N) (hU (s k)) (hUc (s k)) hT
    have htri : (∫ y, ‖U N y - U (s k) y‖) ≤ 2 * δ := by
      have hn1 : Integrable fun y => ‖U N y - F y‖ := ((hUi N).sub hF).norm
      have hn2 : Integrable fun y => ‖U (s k) y - F y‖ := ((hUi (s k)).sub hF).norm
      have hi : Integrable fun y => ‖U N y - F y‖ + ‖U (s k) y - F y‖ := hn1.add hn2
      have hle : (∫ y, ‖U N y - U (s k) y‖) ≤ ∫ y, (‖U N y - F y‖ + ‖U (s k) y - F y‖) := by
        refine integral_mono ((hUi N).sub (hUi (s k))).norm hi fun y => ?_
        have hn := norm_sub_le (U N y - F y) (U (s k) y - F y)
        simp only [sub_sub_sub_cancel_right] at hn
        exact hn
      rw [integral_add hn1 hn2] at hle
      linarith only [hle, hN2, hk2]
    have hpow : (∫ y, ‖U N y - U (s k) y‖) ^ 2 ≤ (2 * δ) ^ 2 :=
      pow_le_pow_left₀ (integral_nonneg fun _ => norm_nonneg _) htri 2
    have hmul := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ T / Real.pi)
    linarith only [h, hmul, hδsq, hN1, hk1]
  have hae : ∀ᵐ y, Tendsto (fun k => U N y - U (s k) y) atTop (𝓝 (U N y - F y)) := by
    filter_upwards [hs] with y hy
    exact hy.const_sub _
  have hmeas : AEStronglyMeasurable (fun y => U N y - F y) volume :=
    (hUi N).aestronglyMeasurable.sub hF.aestronglyMeasurable
  exact integral_sq_le_of_eLpNorm_two_le hmeas hε.le
    (Lp.eLpNorm_le_of_ae_tendsto hbound
      (fun k => ((hUi N).sub (hUi (s k))).aestronglyMeasurable) hae)

/-- A weighted square bound passes to every `L¹` limit. -/
theorem weighted_sq_of_L1_limit {l : Filter ℕ} [NeBot l] [IsCountablyGenerated l]
    {U : ℕ → ℝ → ℝ} {F : ℝ → ℝ} (hU : ∀ N, Integrable (U N)) (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y, ‖U N y - F y‖) l (𝓝 0))
    {w : ℝ → ℝ} (hw : Continuous w) (hUw : ∀ N, MemLp (fun y => w y * U N y) 2 (volume : Measure ℝ))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ N, (∫ y, (w y * U N y) ^ 2) ≤ M) :
    MemLp (fun y => w y * F y) 2 (volume : Measure ℝ) ∧ (∫ y, (w y * F y) ^ 2) ≤ M := by
  obtain ⟨s, -, hs⟩ := exists_seq_ae_tendsto_of_L1 hU hF hL1
  have hae : ∀ᵐ y, Tendsto (fun k => w y * U (s k) y) atTop (𝓝 (w y * F y)) := by
    filter_upwards [hs] with y hy
    exact hy.const_mul _
  have hmeas : AEStronglyMeasurable (fun y => w y * F y) volume :=
    hw.aestronglyMeasurable.mul hF.aestronglyMeasurable
  exact integral_sq_le_of_eLpNorm_two_le hmeas hM0
    (Lp.eLpNorm_le_of_ae_tendsto
      (Eventually.of_forall fun k => eLpNorm_two_le_of_integral_sq_le (hUw (s k)) (hM (s k)))
      (fun k => (hUw (s k)).aestronglyMeasurable) hae)

/-- An `L¹` limit of functions vanishing above `Y` vanishes above `Y`. -/
theorem ae_eq_zero_above_of_L1_limit {l : Filter ℕ} [NeBot l] {U : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hU : ∀ N, Integrable (U N)) (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y, ‖U N y - F y‖) l (𝓝 0)) {Y : ℝ}
    (hs : ∀ᶠ N in l, ∀ y, Y < y → U N y = 0) : ∀ᵐ y, Y < y → F y = 0 := by
  have hle : (∫ y in Set.Ioi Y, ‖F y‖) ≤ 0 := by
    refine ge_of_tendsto hL1 ?_
    filter_upwards [hs] with N hN
    have h1 : (∫ y in Set.Ioi Y, ‖F y‖) = ∫ y in Set.Ioi Y, ‖U N y - F y‖ := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
      simp only [hN y hy, zero_sub, norm_neg]
    rw [h1]
    exact setIntegral_le_integral ((hU N).sub hF).norm (Eventually.of_forall fun _ => norm_nonneg _)
  have h0 : (∫ y in Set.Ioi Y, ‖F y‖) = 0 :=
    le_antisymm hle (setIntegral_nonneg measurableSet_Ioi fun _ _ => norm_nonneg _)
  have hz := (setIntegral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun _ => norm_nonneg _) hF.norm.integrableOn).mp h0
  have hz' := (ae_restrict_iff' measurableSet_Ioi).mp hz
  filter_upwards [hz'] with y hy hyY
  simpa only [Pi.zero_apply, norm_eq_zero] using hy hyY

/-! ### Prime and pole limits -/

/-- A continuous compactly supported source vanishing above `1` has its weighted mass bounded by its
`L²` and eighth exponential masses. -/
theorem weightedTwo_of_support {U : ℝ → ℝ} (hU : Continuous U) (hUc : HasCompactSupport U)
    (hs : ∀ y, 1 < y → U y = 0) :
    WeightedTwo U ∧ exponentialSourceMass U ≤
      Real.exp 2 * (∫ y, U y ^ 2) + (∫ y, U y ^ 2 * Real.exp (-(8 * y))) := by
  have hU2c : HasCompactSupport fun y => U y ^ 2 := by
    rw [hasCompactSupport_iff_eventuallyEq] at hUc ⊢
    exact hUc.mono fun y hy => by
      change U y = 0 at hy
      change U y ^ 2 = 0
      rw [hy, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hU2 : Integrable fun y => U y ^ 2 := (hU.pow 2).integrable_of_hasCompactSupport hU2c
  have hU8 : Integrable fun y => U y ^ 2 * Real.exp (-(8 * y)) :=
    ((hU.pow 2).mul (by fun_prop)).integrable_of_hasCompactSupport hU2c.mul_right
  obtain ⟨hW, hb⟩ := exponentialSourceMass_le_of_support (Y := 1) zero_le_one
    hU.aestronglyMeasurable hU2 hU8 (Eventually.of_forall hs)
  refine ⟨hW, hb.trans ?_⟩
  have h6 : Real.exp (-(6 * 1)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have h8 : 0 ≤ ∫ y, U y ^ 2 * Real.exp (-(8 * y)) :=
    integral_nonneg fun y => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have h := mul_le_mul_of_nonneg_right h6 h8
  rw [show (2 : ℝ) * 1 = 2 by norm_num]
  linarith only [h]

/-- **Strong limits with bounded eighth mass converge in the weighted norm.** -/
theorem tendsto_exponentialSourceMass_sub {l : Filter ℕ} {U : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hU : ∀ N, Continuous (U N)) (hUc : ∀ N, HasCompactSupport (U N))
    (hFm : AEStronglyMeasurable F volume) (hF2 : Integrable fun y => F y ^ 2)
    (hF8 : Integrable fun y => F y ^ 2 * Real.exp (-(8 * y)))
    {M : ℝ} (hM : ∀ N, (∫ y, U N y ^ 2 * Real.exp (-(8 * y))) ≤ M)
    (hsupp : ∀ᶠ N in l, ∀ y, 1 < y → U N y = 0) (hFs : ∀ᵐ y, 1 < y → F y = 0)
    (hstrong : ∀ ε > 0, ∀ᶠ N in l, (∫ y, (U N y - F y) ^ 2) ≤ ε) :
    Tendsto (fun N => exponentialSourceMass fun y => U N y - F y) l (𝓝 0) := by
  have hF80 : 0 ≤ ∫ y, F y ^ 2 * Real.exp (-(8 * y)) :=
    integral_nonneg fun y => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  let W : ℝ := 2 * M + 2 * ∫ y, F y ^ 2 * Real.exp (-(8 * y))
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- choose the cut so the far tail costs at most `ε / 3`
  have hY : ∀ᶠ Y : ℝ in atTop, Real.exp (-(6 * Y)) * W < ε / 3 := by
    have h : Tendsto (fun Y : ℝ => Real.exp (-(6 * Y)) * W) atTop (𝓝 (0 * W)) := by
      refine (Real.tendsto_exp_atBot.comp ?_).mul_const W
      exact tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by norm_num))
    rw [zero_mul] at h
    exact h.eventually (gt_mem_nhds (by positivity))
  obtain ⟨Y, hYW, hY1⟩ := (hY.and (eventually_ge_atTop (1 : ℝ))).exists
  have hY0 : 0 ≤ Y := zero_le_one.trans hY1
  have hexp : 0 < Real.exp (2 * Y) := Real.exp_pos _
  filter_upwards [hsupp, hstrong (ε / (3 * Real.exp (2 * Y))) (by positivity)] with N hN1 hN2
  have hUi2 : HasCompactSupport fun y => U N y ^ 2 := by
    have := hUc N
    rw [hasCompactSupport_iff_eventuallyEq] at this ⊢
    exact this.mono fun y hy => by
      change U N y = 0 at hy
      change U N y ^ 2 = 0
      rw [hy, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hU2 : Integrable fun y => U N y ^ 2 := ((hU N).pow 2).integrable_of_hasCompactSupport hUi2
  have hU8 : Integrable fun y => U N y ^ 2 * Real.exp (-(8 * y)) :=
    (((hU N).pow 2).mul (by fun_prop)).integrable_of_hasCompactSupport hUi2.mul_right
  have hdm : AEStronglyMeasurable (fun y => U N y - F y) volume :=
    (hU N).aestronglyMeasurable.sub hFm
  have hdom2 : Integrable fun y => 2 * U N y ^ 2 + 2 * F y ^ 2 :=
    (hU2.const_mul 2).add (hF2.const_mul 2)
  have hd2 : Integrable fun y => (U N y - F y) ^ 2 := by
    refine hdom2.mono' (hdm.pow 2) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith only [sq_nonneg (U N y + F y)]
  have hdom8 : Integrable fun y => 2 * (U N y ^ 2 * Real.exp (-(8 * y))) +
      2 * (F y ^ 2 * Real.exp (-(8 * y))) := (hU8.const_mul 2).add (hF8.const_mul 2)
  have hexp8m : AEStronglyMeasurable (fun y : ℝ => Real.exp (-(8 * y))) volume :=
    Continuous.aestronglyMeasurable (by fun_prop)
  have hd8pt : ∀ y, (U N y - F y) ^ 2 * Real.exp (-(8 * y)) ≤
      2 * (U N y ^ 2 * Real.exp (-(8 * y))) + 2 * (F y ^ 2 * Real.exp (-(8 * y))) := by
    intro y
    have h : (U N y - F y) ^ 2 ≤ 2 * U N y ^ 2 + 2 * F y ^ 2 := by
      nlinarith only [sq_nonneg (U N y + F y)]
    have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos (-(8 * y))).le
    linarith only [h']
  have hd8 : Integrable fun y => (U N y - F y) ^ 2 * Real.exp (-(8 * y)) := by
    refine hdom8.mono' ((hdm.pow 2).mul hexp8m) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    exact hd8pt y
  have hsd : ∀ᵐ y, Y < y → U N y - F y = 0 := by
    filter_upwards [hFs] with y hy hyY
    have hy1 : 1 < y := hY1.trans_lt hyY
    rw [hN1 y hy1, hy hy1, sub_zero]
  obtain ⟨-, hb⟩ := exponentialSourceMass_le_of_support hY0 hdm hd2 hd8 hsd
  have hW8 : (∫ y, (U N y - F y) ^ 2 * Real.exp (-(8 * y))) ≤ W := by
    have h := integral_mono hd8 hdom8 hd8pt
    rw [integral_add (hU8.const_mul 2) (hF8.const_mul 2), integral_const_mul,
      integral_const_mul] at h
    dsimp only [W]
    linarith only [h, hM N]
  have h1 : Real.exp (2 * Y) * (∫ y, (U N y - F y) ^ 2) ≤ ε / 3 := by
    have h := mul_le_mul_of_nonneg_left hN2 hexp.le
    refine h.trans_eq ?_
    field_simp
  have h2 : Real.exp (-(6 * Y)) * (∫ y, (U N y - F y) ^ 2 * Real.exp (-(8 * y))) ≤ ε / 3 := by
    have h := mul_le_mul_of_nonneg_left hW8 (Real.exp_pos (-(6 * Y))).le
    linarith only [h, hYW]
  have h0 := exponentialSourceMass_nonneg fun y => U N y - F y
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith only [hb, h1, h2, hε]

/-- **The prime sum and the pole moments pass to strong limits with bounded eighth mass.** -/
theorem tendsto_prime_and_pole_of_strong_limit {l : Filter ℕ} {U : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hU : ∀ N, Continuous (U N)) (hUc : ∀ N, HasCompactSupport (U N))
    (hFW : WeightedTwo F) {M : ℝ}
    (hmass : ∀ N, (∫ y, U N y ^ 2) ≤ 1)
    (hM : ∀ N, (∫ y, U N y ^ 2 * Real.exp (-(8 * y))) ≤ M)
    (hsupp : ∀ᶠ N in l, ∀ y, 1 < y → U N y = 0)
    (hd : Tendsto (fun N => exponentialSourceMass fun y => U N y - F y) l (𝓝 0)) :
    Tendsto (fun N => primeSum (U N)) l (𝓝 (primeSum F)) ∧
      Tendsto (fun N => coshHalfMoment (U N)) l (𝓝 (coshHalfMoment F)) ∧
      Tendsto (fun N => sinhHalfMoment (U N)) l (𝓝 (sinhHalfMoment F)) := by
  have hroot : Tendsto (fun N => Real.sqrt (exponentialSourceMass fun y => U N y - F y)) l (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hd
    rw [Real.sqrt_zero] at h
    exact h
  let B : ℝ := Real.exp 2 + M
  have hbound : ∀ᶠ N in l, WeightedTwo (U N) ∧ exponentialSourceMass (U N) ≤ B := by
    filter_upwards [hsupp] with N hN
    obtain ⟨hW, hb⟩ := weightedTwo_of_support (hU N) (hUc N) hN
    refine ⟨hW, hb.trans ?_⟩
    have h := mul_le_mul_of_nonneg_left (hmass N) (Real.exp_pos 2).le
    dsimp only [B]
    linarith only [h, hM N]
  have hK : 0 ≤ Real.sqrt (∫ u, Real.exp (-|u|)) := Real.sqrt_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    let C : ℝ := 2 * vonMangoldtThreeHalvesMass *
      (Real.sqrt B + Real.sqrt (exponentialSourceMass F))
    have hC : 0 ≤ C := mul_nonneg (mul_nonneg zero_le_two vonMangoldtThreeHalvesMass_nonneg)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hlim := hroot.const_mul C
    rw [mul_zero] at hlim
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [hbound] with N hN
    rw [Real.norm_eq_abs]
    refine (abs_primeSum_sub_le hN.1 hFW).trans ?_
    have hsq := Real.sqrt_le_sqrt hN.2
    have hr0 := Real.sqrt_nonneg (exponentialSourceMass fun y => U N y - F y)
    have hadd : Real.sqrt (exponentialSourceMass (U N)) + Real.sqrt (exponentialSourceMass F) ≤
        Real.sqrt B + Real.sqrt (exponentialSourceMass F) := by linarith only [hsq]
    have h := mul_le_mul_of_nonneg_left hadd hr0
    have hV : 0 ≤ 2 * vonMangoldtThreeHalvesMass :=
      mul_nonneg zero_le_two vonMangoldtThreeHalvesMass_nonneg
    have h' := mul_le_mul_of_nonneg_left h hV
    refine h'.trans_eq ?_
    dsimp only [C]
    ring
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim := hroot.mul_const (Real.sqrt (∫ u, Real.exp (-|u|)))
    rw [zero_mul] at hlim
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [hbound] with N hN
    rw [Real.norm_eq_abs]
    exact abs_coshHalfMoment_sub_le hN.1 hFW
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim := hroot.mul_const (Real.sqrt (∫ u, Real.exp (-|u|)))
    rw [zero_mul] at hlim
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [hbound] with N hN
    rw [Real.norm_eq_abs]
    exact abs_sinhHalfMoment_sub_le hN.1 hFW

/-! ### Bounded Weil energy -/

/-- Weil's form in archimedean form. -/
theorem weilQuad_eq_arch_sub_prime_add_pole {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    weilQuad f = archForm f - primeSum f +
      (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2) := by
  rw [weilQuad_eq hf hfc, archForm_eq_levyEnergy hf hfc]

/-- **Bounded Weil form and bounded masses keep the high frequencies uniformly small.** -/
theorem high_tails_of_bounded_weilQuad {l : Filter ℕ} {U : ℕ → ℝ → ℝ}
    (hU : ∀ N, ContDiff ℝ 2 (U N)) (hUc : ∀ N, HasCompactSupport (U N))
    {M b : ℝ} (hmass : ∀ N, (∫ y, U N y ^ 2) ≤ 1)
    (hM : ∀ N, (∫ y, U N y ^ 2 * Real.exp (-(8 * y))) ≤ M)
    (hsupp : ∀ᶠ N in l, ∀ y, 1 < y → U N y = 0)
    (hb : ∀ᶠ N in l, weilQuad (U N) ≤ b) :
    ∀ ε > 0, ∃ T > 0, ∀ᶠ N in l, highFourierMass (U N) T ≤ ε := by
  let B : ℝ := Real.exp 2 + M
  let K : ℝ := ∫ u, Real.exp (-|u|)
  let V : ℝ := 2 * vonMangoldtThreeHalvesMass
  let E : ℝ := |b| + V * |B| + 2 * (|B| * K) + (factorialSpanGammaOffset + Real.log 2)
  have hK : 0 ≤ K := integral_nonneg fun _ => (Real.exp_pos _).le
  have hV : 0 ≤ V := mul_nonneg zero_le_two vonMangoldtThreeHalvesMass_nonneg
  have hd : 0 ≤ factorialSpanGammaOffset + Real.log 2 :=
    add_nonneg factorialSpanGammaOffset_nonneg (Real.log_nonneg one_le_two)
  have hE : 0 ≤ E := by
    have h1 := abs_nonneg b
    have h2 := mul_nonneg hV (abs_nonneg B)
    have h3 := mul_nonneg (abs_nonneg B) hK
    dsimp only [E]
    linarith only [h1, h2, h3, hd]
  intro ε hε
  let T : ℝ := Real.exp (factorialSpanGammaOffset + 1 + E / ε)
  have hT0 : 0 < T := Real.exp_pos _
  refine ⟨T, hT0, ?_⟩
  have hEε : 0 ≤ E / ε := div_nonneg hE hε.le
  have hTge : Real.exp (factorialSpanGammaOffset + 1) ≤ T :=
    Real.exp_le_exp.mpr (by linarith only [hEε])
  have hlogT : Real.log T - factorialSpanGammaOffset = 1 + E / ε := by
    rw [Real.log_exp]; ring
  filter_upwards [hsupp, hb] with N hN1 hN2
  obtain ⟨hW, hB⟩ := weightedTwo_of_support (hU N).continuous (hUc N) hN1
  have hB' : exponentialSourceMass (U N) ≤ B := by
    have h := mul_le_mul_of_nonneg_left (hmass N) (Real.exp_pos 2).le
    dsimp only [B]
    linarith only [hB, h, hM N]
  have hA0 := exponentialSourceMass_nonneg (U N)
  have hA : exponentialSourceMass (U N) ≤ |B| := hB'.trans (le_abs_self B)
  have hprime := abs_primeSum_le hW
  have hsinh : sinhHalfMoment (U N) ^ 2 ≤ |B| * K := by
    obtain ⟨-, hs⟩ := abs_integral_mul_kernel_le hW
      (Real.continuous_sinh.comp (continuous_id.div_const 2)) abs_sinh_half_le_exp
    have hsq : sinhHalfMoment (U N) ^ 2 ≤ exponentialSourceMass (U N) * K := by
      rw [← sq_abs, ← Real.sq_sqrt (mul_nonneg hA0 hK), Real.sqrt_mul hA0]
      exact pow_le_pow_left₀ (abs_nonneg _) hs 2
    exact hsq.trans (mul_le_mul_of_nonneg_right hA hK)
  have hweil := weilQuad_eq_arch_sub_prime_add_pole (hU N) (hUc N)
  have harch : archForm (U N) ≤ |b| + V * |B| + 2 * (|B| * K) := by
    have h1 : primeSum (U N) ≤ V * |B| :=
      (le_abs_self _).trans (hprime.trans (mul_le_mul_of_nonneg_left hA hV))
    have h2 := sq_nonneg (coshHalfMoment (U N))
    have h3 := le_abs_self b
    linarith only [hweil, hN2, h1, h2, h3, hsinh]
  have hhigh := highFourierMass_le_of_archForm (hU N) (hUc N) hTge
  have hmul := mul_le_mul_of_nonneg_left (hmass N) hd
  rw [hlogT] at hhigh
  have hpos : 0 < 1 + E / ε := by linarith only [hEε]
  have hle : (1 + E / ε) * highFourierMass (U N) T ≤ E := by
    dsimp only [E]
    linarith only [hhigh, harch, hmul]
  have hfin : highFourierMass (U N) T ≤ E / (1 + E / ε) := by
    rw [le_div_iff₀ hpos]
    linarith only [hle]
  refine hfin.trans ?_
  rw [div_le_iff₀ hpos]
  have : ε * (E / ε) = E := by field_simp
  nlinarith only [this, hε]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
