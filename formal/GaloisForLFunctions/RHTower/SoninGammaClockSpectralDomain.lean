import GaloisForLFunctions.RHTower.SoninGammaClockSymbol
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import GaloisForLFunctions.HTGeometry.MaximalRealL2Multiplication
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanMellinTransport

/-!
# Exact maximal domain of the Gamma clock symbol

The original finite clock integrals lie between the complete Gamma symbol
and zero. Their exact quotient yields strong admission on the maximal
spectral domain. Conversely, any cofinal strong cutoff limit identifies the
literal Gamma product almost everywhere and forces membership in that
domain. Physical Mellin transport of the finite source remains a separate
identification; no such transport or RH conclusion is assumed here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology LinearPMap
namespace RHTower

/-- Literal finite-cutoff Gamma multiplier, including the clock-zero counterterm. -/
def gammaClockCutoffSymbol (ε R ξ : ℝ) : ℝ :=
  ∫ u in Icc ε R, 2*(Real.cos (ξ*u)-1)*ccmPublishedArchimedeanDensity u/u

private theorem density_pos {u : ℝ} (hu : 0 < u) :
    0 < ccmPublishedArchimedeanDensity u := by
  unfold ccmPublishedArchimedeanDensity
  exact div_pos (Real.exp_pos _) (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith)))

private theorem integrand_nonpos (ξ u : ℝ) (hu : 0 < u) :
    2*(Real.cos (ξ*u)-1)*ccmPublishedArchimedeanDensity u/u ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg _ hu.le
  have hc := Real.cos_le_one (ξ*u)
  have hg := density_pos hu
  nlinarith

/-- The complete Gamma clock symbol has the sign of its literal symmetric integrand. -/
theorem gammaClockSymbol_nonpos (ξ : ℝ) : gammaClockSymbol ξ ≤ 0 := by
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact integrand_nonpos ξ u hu

/-- Every finite Gamma cutoff lies between its complete symbol and zero. -/
theorem gammaClockCutoffSymbol_order (ε R ξ : ℝ) (hε : 0 < ε) :
    gammaClockSymbol ξ ≤ gammaClockCutoffSymbol ε R ξ ∧ gammaClockCutoffSymbol ε R ξ ≤ 0 := by
  have hn : gammaClockCutoffSymbol ε R ξ ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact integrand_nonpos ξ u (hε.trans_le hu.1)
  refine ⟨?_, hn⟩
  have h := setIntegral_mono_set (s := Icc ε R) (gammaClockSymbol_integrable ξ).neg
    (show 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))]
      (fun u => -(2*(Real.cos (ξ*u)-1)*ccmPublishedArchimedeanDensity u/u)) from by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact neg_nonneg.mpr (integrand_nonpos ξ u hu))
    (Eventually.of_forall (fun u hu => hε.trans_le hu.1))
  simp only [Pi.neg_apply, integral_neg] at h
  change -gammaClockCutoffSymbol ε R ξ ≤ -gammaClockSymbol ξ at h
  linarith

/-- Exact symbol dominance sufficient for maximal-domain convergence. -/
theorem gammaClockCutoffSymbol_error_le (ε R ξ : ℝ) (hε : 0 < ε) :
    |gammaClockCutoffSymbol ε R ξ-gammaClockSymbol ξ| ≤ |gammaClockSymbol ξ| := by
  obtain ⟨hl, hu⟩ := gammaClockCutoffSymbol_order ε R ξ hε
  rw [abs_of_nonneg (sub_nonneg.mpr hl), abs_of_nonpos (gammaClockSymbol_nonpos ξ)]
  linarith

/-- The original finite symbols converge for every cofinal removal of both cutoffs. -/
theorem gammaClockCutoffSymbol_tendsto (ξ : ℝ)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {ε R : ι → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) :
    Tendsto (fun i => gammaClockCutoffSymbol (ε i) (R i) ξ) l (𝓝 (gammaClockSymbol ξ)) := by
  have hc : AECover (volume.restrict (Ioi (0:ℝ))) l (fun i => Icc (ε i) (R i)) :=
    (aecover_Ioi_of_Ici (hε.mono_right nhdsWithin_le_nhds)).inter (aecover_Iic hR)
  have ht := hc.integral_tendsto_of_countably_generated (gammaClockSymbol_integrable ξ)
  apply ht.congr'
  filter_upwards [hε.eventually self_mem_nhdsWithin] with i hi
  rw [Measure.restrict_restrict measurableSet_Icc,
    inter_eq_left.mpr (show Icc (ε i) (R i) ⊆ Ioi 0 from fun u hu => lt_of_lt_of_le hi hu.1)]
  rfl

private theorem symbol_measurable : Measurable gammaClockSymbol :=
  (continuous_iff_continuousAt.mpr (fun ξ => (hasDerivAt_gammaClockSymbol ξ).continuousAt)).measurable

private theorem cutoffSymbol_measurable (ε R : ℝ) : Measurable (gammaClockCutoffSymbol ε R) := by
  have h : Measurable (fun p : ℝ × ℝ =>
      2*(Real.cos (p.1*p.2)-1)*ccmPublishedArchimedeanDensity p.2/p.2) := by
    unfold ccmPublishedArchimedeanDensity
    fun_prop
  exact h.stronglyMeasurable.integral_prod_right'.measurable

/-- Exact bounded quotient used to pass the original Gamma cutoffs on the maximal domain. -/
def gammaClockCutoffRatio (ε R ξ : ℝ) : ℝ :=
  if gammaClockSymbol ξ = 0 then 1 else gammaClockCutoffSymbol ε R ξ/gammaClockSymbol ξ

private theorem ratio_measurable (ε R : ℝ) : Measurable (gammaClockCutoffRatio ε R) := by
  unfold gammaClockCutoffRatio
  exact Measurable.piecewise (measurableSet_eq_fun symbol_measurable measurable_const)
    measurable_const ((cutoffSymbol_measurable ε R).div symbol_measurable)

/-- No norm-growth envelope is needed: the literal quotient always lies in the unit interval. -/
theorem gammaClockCutoffRatio_bounds (ε R ξ : ℝ) (hε : 0 < ε) :
    0 ≤ gammaClockCutoffRatio ε R ξ ∧ gammaClockCutoffRatio ε R ξ ≤ 1 := by
  unfold gammaClockCutoffRatio
  split_ifs with hz
  · exact ⟨zero_le_one, le_rfl⟩
  · obtain ⟨hl, hu⟩ := gammaClockCutoffSymbol_order ε R ξ hε
    have hs : gammaClockSymbol ξ < 0 := lt_of_le_of_ne (gammaClockSymbol_nonpos ξ) hz
    exact ⟨div_nonneg_of_nonpos hu hs.le,
      (div_le_iff_of_neg hs).mpr (by simpa only [one_mul] using hl)⟩

/-- The quotient preserves the complete finite source, including frequencies where it vanishes. -/
theorem gammaClockCutoffRatio_mul_symbol (ε R ξ : ℝ) (hε : 0 < ε) :
    gammaClockCutoffRatio ε R ξ*gammaClockSymbol ξ = gammaClockCutoffSymbol ε R ξ := by
  unfold gammaClockCutoffRatio
  split_ifs with hz
  · obtain ⟨hl, hu⟩ := gammaClockCutoffSymbol_order ε R ξ hε
    rw [hz] at hl ⊢
    simp only [mul_zero]
    exact (le_antisymm hu hl).symm
  · exact div_mul_cancel₀ _ hz

/-- The full literal quotient tends to identity at every spectral frequency. -/
theorem gammaClockCutoffRatio_tendsto (ξ : ℝ)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {ε R : ι → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) :
    Tendsto (fun i => gammaClockCutoffRatio (ε i) (R i) ξ) l (𝓝 1) := by
  by_cases hz : gammaClockSymbol ξ = 0
  · simpa only [gammaClockCutoffRatio, if_pos hz] using (tendsto_const_nhds (x := (1:ℝ)))
  · have h := (gammaClockCutoffSymbol_tendsto ξ hε hR).div_const (gammaClockSymbol ξ)
    simpa only [gammaClockCutoffRatio, if_neg hz, div_self hz] using h


open GaloisForLFunctions.HTGeometry

private theorem clockDensity_integrable (ε R : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun u => ccmPublishedArchimedeanDensity u/u) (Icc ε R) := by
  apply ContinuousOn.integrableOn_Icc
  intro u hu
  have hu0 : 0 < u := hε.trans_le hu.1
  have hden : Real.exp u-Real.exp (-u) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith)))
  unfold ccmPublishedArchimedeanDensity
  apply ContinuousAt.continuousWithinAt
  exact ((by fun_prop : ContinuousAt (fun t : ℝ => Real.exp (t/2)) u).div
    (by fun_prop) hden).div continuousAt_id hu0.ne'

private def cutoffBound (ε R : ℝ) : ℝ :=
  ∫ u in Icc ε R, 4*‖ccmPublishedArchimedeanDensity u/u‖

private theorem cutoffBound_nonneg (ε R : ℝ) : 0 ≤ cutoffBound ε R :=
  integral_nonneg (fun _ => by positivity)

private theorem cutoffSymbol_norm_le (ε R : ℝ) (hε : 0 < ε) (ξ : ℝ) :
    ‖gammaClockCutoffSymbol ε R ξ‖ ≤ cutoffBound ε R := by
  have hf := (gammaClockSymbol_integrable ξ).mono_set
    (show Icc ε R ⊆ Ioi 0 from fun u hu => hε.trans_le hu.1)
  have hd := (clockDensity_integrable ε R hε).norm.const_mul 4
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae hf.norm hd
  filter_upwards [] with u
  have hc : ‖Real.cos (ξ*u)-1‖ ≤ 2 := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [Real.neg_one_le_cos (ξ*u), Real.cos_le_one (ξ*u)]
  rw [mul_div_assoc, norm_mul, norm_mul]
  rw [show ‖(2:ℝ)‖ = 2 by norm_num]
  nlinarith [norm_nonneg (ccmPublishedArchimedeanDensity u/u)]

/-- Actual bounded spectral action of the literal finite Gamma symbol. -/
def gammaClockCutoffSpectralOperator (ε R : ℝ) (hε : 0 < ε) :
    SpectralL2 →L[ℂ] SpectralL2 :=
  lpBoundedMulCLM (Complex.continuous_ofReal.measurable.comp (cutoffSymbol_measurable ε R))
    (cutoffBound_nonneg ε R) (fun ξ => by
      simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using! cutoffSymbol_norm_le ε R hε ξ)

private theorem cutoffSpectral_ae (ε R : ℝ) (hε : 0 < ε) (f : SpectralL2) :
    (gammaClockCutoffSpectralOperator ε R hε f : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (gammaClockCutoffSymbol ε R ξ:ℂ)*f ξ :=
  lpBoundedMulCLM_coeFn _ _ _ f

/-- The full Gamma clock multiplier on its maximal spectral domain. -/
def gammaClockSpectralOperator : SpectralL2 →ₗ.[ℂ] SpectralL2 :=
  maximalRealL2Mul volume gammaClockSymbol

private theorem spectral_ae (f : gammaClockSpectralOperator.domain) :
    (gammaClockSpectralOperator f : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (gammaClockSymbol ξ:ℂ)*(f:SpectralL2) ξ := by
  simpa only [gammaClockSpectralOperator] using!
    maximalRealL2Mul_apply_ae volume gammaClockSymbol f

/-- Reality and exact scalar admission give a densely defined self-adjoint Gamma multiplier. -/
theorem gammaClockSpectralOperator_isSelfAdjoint : IsSelfAdjoint gammaClockSpectralOperator :=
  maximalRealL2Mul_isSelfAdjoint volume symbol_measurable

private theorem ratio_complex_bound (ε R : ℝ) (hε : 0 < ε) (ξ : ℝ) :
    ‖(gammaClockCutoffRatio ε R ξ:ℂ)‖ ≤ 1 := by
  obtain ⟨h0,h1⟩ := gammaClockCutoffRatio_bounds ε R ξ hε
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] using h1

private def ratioSpectral (ε R : ℝ) (hε : 0 < ε) : SpectralL2 →L[ℂ] SpectralL2 :=
  lpBoundedMulCLM (Complex.continuous_ofReal.measurable.comp (ratio_measurable ε R))
    zero_le_one (ratio_complex_bound ε R hε)

private theorem ratioSpectral_ae (ε R : ℝ) (hε : 0 < ε) (f : SpectralL2) :
    (ratioSpectral ε R hε f : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (gammaClockCutoffRatio ε R ξ:ℂ)*f ξ := by
  simpa only [ratioSpectral, Function.comp_apply] using! lpBoundedMulCLM_coeFn
    (p := 2) (μ := volume) (Complex.continuous_ofReal.measurable.comp (ratio_measurable ε R))
      zero_le_one (ratio_complex_bound ε R hε) f

private theorem ratioSpectral_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (ε R : ι → ℝ) (hpos : ∀ i, 0 < ε i)
    (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) (f : SpectralL2) :
    Tendsto (fun i => ratioSpectral (ε i) (R i) (hpos i) f) l (𝓝 f) := by
  have hpt (ξ : ℝ) : Tendsto (fun i => (gammaClockCutoffRatio (ε i) (R i) ξ:ℂ)) l (𝓝 1) := by
    simpa only [Function.comp_apply, Complex.ofReal_one] using! Complex.continuous_ofReal.continuousAt.tendsto.comp
      (gammaClockCutoffRatio_tendsto ξ hε hR)
  have h := tendsto_lpBoundedMulCLM_apply
    (φ := fun i ξ => (gammaClockCutoffRatio (ε i) (R i) ξ:ℂ))
    (ψ := fun _ : ℝ => (1:ℂ))
    (fun i => Complex.continuous_ofReal.measurable.comp (ratio_measurable (ε i) (R i)))
    measurable_const zero_le_one (fun i => ratio_complex_bound (ε i) (R i) (hpos i))
    (fun _ => by simp) hpt f
  have hid : lpBoundedMulCLM (p := 2) (μ := volume) (φ := fun _ : ℝ => (1:ℂ))
      measurable_const zero_le_one (fun _ => by simp) f = f := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := volume) (φ := fun _ : ℝ => (1:ℂ))
      measurable_const zero_le_one (fun _ => by simp) f] with ξ hξ
    simpa only [one_mul] using hξ
  simpa only [ratioSpectral, hid] using! h

private theorem cutoffSpectral_eq_ratio (ε R : ℝ) (hε : 0 < ε)
    (f : gammaClockSpectralOperator.domain) :
    gammaClockCutoffSpectralOperator ε R hε (f:SpectralL2) =
      ratioSpectral ε R hε (gammaClockSpectralOperator f) := by
  apply Lp.ext
  filter_upwards [cutoffSpectral_ae ε R hε (f:SpectralL2),
    ratioSpectral_ae ε R hε (gammaClockSpectralOperator f),
    spectral_ae f] with ξ hcut hratio hfull
  rw [hcut, hratio, hfull, ← mul_assoc, ← Complex.ofReal_mul,
    gammaClockCutoffRatio_mul_symbol ε R ξ hε]

/-- Every vector in the maximal Gamma domain admits the ORIGINAL finite spectral cutoffs. -/
theorem gammaClockCutoffSpectralOperator_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (ε R : ι → ℝ) (hpos : ∀ i, 0 < ε i)
    (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop)
    (f : gammaClockSpectralOperator.domain) :
    Tendsto (fun i => gammaClockCutoffSpectralOperator (ε i) (R i) (hpos i) (f:SpectralL2))
      l (𝓝 (gammaClockSpectralOperator f)) := by
  simp only [cutoffSpectral_eq_ratio]
  exact ratioSpectral_tendsto ε R hpos hε hR _


/-- Strong convergence of the ORIGINAL cutoff family forces maximal-domain membership
and identifies its action. This is necessity, not only an admitted sufficient core. -/
theorem gammaClockCutoffSpectralOperator_limit_iff
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [NeBot l]
    (ε R : ι → ℝ) (hpos : ∀ i, 0 < ε i)
    (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) (f g : SpectralL2) :
    Tendsto (fun i => gammaClockCutoffSpectralOperator (ε i) (R i) (hpos i) f) l (𝓝 g) ↔
      ∃ hf : f ∈ gammaClockSpectralOperator.domain, gammaClockSpectralOperator ⟨f,hf⟩ = g := by
  constructor
  · intro ht
    obtain ⟨k,hk⟩ := l.exists_seq_tendsto
    obtain ⟨ns,hns,hae⟩ := (tendstoInMeasure_of_tendsto_Lp (ht.comp hk)).exists_seq_tendsto_ae
    have hform : ∀ᵐ ξ ∂volume, ∀ n : ℕ,
        (gammaClockCutoffSpectralOperator (ε (k (ns n))) (R (k (ns n))) (hpos (k (ns n))) f : ℝ → ℂ) ξ =
          (gammaClockCutoffSymbol (ε (k (ns n))) (R (k (ns n))) ξ:ℂ)*f ξ :=
      ae_all_iff.mpr (fun n => cutoffSpectral_ae _ _ _ f)
    have heq : (g : ℝ → ℂ) =ᵐ[volume] fun ξ => (gammaClockSymbol ξ:ℂ)*f ξ := by
      filter_upwards [hae,hform] with ξ hξ hformξ
      have hpt := gammaClockCutoffSymbol_tendsto ξ
        (hε.comp (hk.comp hns.tendsto_atTop)) (hR.comp (hk.comp hns.tendsto_atTop))
      have hc : Tendsto (fun n => (gammaClockCutoffSymbol (ε (k (ns n))) (R (k (ns n))) ξ:ℂ)*f ξ)
          atTop (𝓝 ((gammaClockSymbol ξ:ℂ)*f ξ)) :=
        (Complex.continuous_ofReal.continuousAt.tendsto.comp hpt).mul tendsto_const_nhds
      have ht' : Tendsto (fun n =>
          (gammaClockCutoffSpectralOperator (ε (k (ns n))) (R (k (ns n))) (hpos (k (ns n))) f : ℝ → ℂ) ξ)
          atTop (𝓝 ((gammaClockSymbol ξ:ℂ)*f ξ)) := by
        simp only [hformξ]
        exact hc
      exact tendsto_nhds_unique hξ ht'
    have hf : f ∈ gammaClockSpectralOperator.domain := (memLp_congr_ae heq).mp (Lp.memLp g)
    refine ⟨hf, ?_⟩
    apply Lp.ext
    exact (spectral_ae ⟨f,hf⟩).trans heq.symm
  · rintro ⟨hf,rfl⟩
    exact gammaClockCutoffSpectralOperator_tendsto ε R hpos hε hR ⟨f,hf⟩

end RHTower
