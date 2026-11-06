import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilGreenOperatorIsUniformlyBoundedOnBoundedForcing
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheHalfLineGreenOperatorHasAShiftIdentity
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilTracesHaveTheirSoftKick
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.SharpRestrictionPreservesTheCompleteComplexWeilDomain

/-!
# The Weil Riesz increments are Lipschitz in `L¹`

Let `a ≤ b = a + h`, `Δ = s_b − ρ s_a` (`chartIncrement`). The Hilbert residual only gives `‖Δ‖₁ ≲ √h`.

**Theorem** (`exists_chartIncrement_lipschitz`). `‖Δ‖₁ ≤ C h` uniformly on compact precontact intervals.

The proof is by duality against `L^∞`. Reflect, so that the new collar `[0, τ)`, `τ = 2h`, lies at the left edge, and
let `T` be the translation of `H_a` to the right edge of `H_b`. The residual `R` is Weil orthogonal to the range of `T`
(`inner_rightResidual_translate`), and it splits sharply as `T w + 𝐁`, with `𝐁` its collar and `w` the part over
the old window (`exists_rightResidual_cut`). Take `g` the sign of `w`, and `u = G_a g`. Then

  `∫|w| = Q_a(u, w) = Q_b(Tu, Tw) = −Q_b(Tu, 𝐁) = −E(Tu, 𝐁) + ⟨(Adj − B) Tu, 𝐁⟩`.

The last term is at most `C ‖𝐁‖₁ ≲ h`, as `Tu` is bounded uniformly in `g`. The cutoff costs the commutator, at most
`‖𝐁‖₁ (Lip/2) ‖u‖₁`. The energy across the collar is at most `τ ‖f₁‖_∞ ‖f₂‖_∞` by the half-line shift identity
(`norm_collar_energy_le`): this is where the logarithm that a size estimate of `E(Tu, 𝐁)` would lose disappears.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

/-! ### Pairings with a bounded function -/

theorem norm_inner_le_mul_integral {f w : RealLineL2} {A : ℝ} (hf : ∀ᵐ x ∂volume, ‖f x‖ ≤ A)
    (hw : Integrable (w : ℝ → ℂ)) : ‖inner ℂ f w‖ ≤ A * ∫ x, ‖w x‖ := by
  rw [L2.inner_def]
  calc
    _ ≤ ∫ x, A * ‖w x‖ := by
      apply norm_integral_le_of_norm_le (hw.norm.const_mul A)
      filter_upwards [hf] with x hx
      rw [RCLike.inner_apply, norm_mul, RCLike.norm_conj, mul_comm]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- The sign of a continuous function on a window, as a bounded vector of the window. -/
theorem exists_signSource (a : SuzukiPositiveAperture) (φ : ℝ → ℂ) (hφ : Continuous φ) :
    ∃ g : suzukiApertureHilbert a, (∀ᵐ x ∂volume, ‖(g : RealLineL2) x‖ ≤ 1) ∧
      ∀ f : suzukiApertureHilbert a, ((f : RealLineL2) : ℝ → ℂ) =ᵐ[volume] (Ico (-a.1) a.1).indicator φ →
        inner ℂ g f = ((∫ x in Ico (-a.1) a.1, ‖φ x‖ : ℝ) : ℂ) := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℂ, ψ = fun x => φ x / (‖φ x‖ : ℂ) := ⟨_, rfl⟩
  have hψm : Measurable ψ := by
    rw [hψ]
    exact hφ.measurable.div (Complex.measurable_ofReal.comp hφ.measurable.norm)
  have hψb (x : ℝ) : ‖ψ x‖ ≤ 1 := by
    rw [hψ]
    simp only
    rw [norm_div, Complex.norm_real, norm_norm]
    exact div_self_le_one _
  have hval (x : ℝ) : φ x * conj (ψ x) = ((‖φ x‖ : ℝ) : ℂ) := by
    rw [hψ]
    simp only
    by_cases h0 : φ x = 0
    · simp [h0]
    · have hne : ((‖φ x‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0)
      rw [map_div₀, Complex.conj_ofReal, ← mul_div_assoc, Complex.mul_conj']
      field_simp
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (centralInterval a.1)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      unfold centralInterval
      exact isCompact_Icc.measure_lt_top⟩
  have hmem : MemLp ((centralInterval a.1).indicator ψ) 2 (volume : Measure ℝ) :=
    (memLp_indicator_iff_restrict (measurableSet_centralInterval a.1)).mpr
      (MemLp.of_bound hψm.aestronglyMeasurable 1 (Eventually.of_forall hψb))
  obtain ⟨L, hL⟩ : ∃ L : RealLineL2, L = hmem.toLp _ := ⟨_, rfl⟩
  have hLv : (L : ℝ → ℂ) =ᵐ[volume] (centralInterval a.1).indicator ψ := by
    rw [hL]
    exact hmem.coeFn_toLp
  obtain ⟨g, hg⟩ : ∃ g : suzukiApertureHilbert a, (g : RealLineL2) =
      indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) L :=
    ⟨⟨indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) L,
      LinearMap.mem_range.mpr ⟨L, rfl⟩⟩, rfl⟩
  have hgv : ((g : RealLineL2) : ℝ → ℂ) =ᵐ[volume] (centralInterval a.1).indicator ψ := by
    rw [hg]
    filter_upwards [indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) L, hLv]
      with x h1 h2
    rw [h1]
    by_cases hx : x ∈ centralInterval a.1
    · rw [indicator_of_mem hx, h2]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  refine ⟨g, ?_, fun f hf => ?_⟩
  · filter_upwards [hgv] with x hx
    rw [hx]
    by_cases hm : x ∈ centralInterval a.1
    · rw [indicator_of_mem hm]
      exact hψb x
    · rw [indicator_of_notMem hm, norm_zero]
      exact zero_le_one
  change inner ℂ (g : RealLineL2) (f : RealLineL2) = _
  rw [L2.inner_def, ← integral_indicator measurableSet_Ico, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [hgv, hf] with x h1 h2
  rw [h1, h2, RCLike.inner_apply]
  by_cases hm : x ∈ Ico (-a.1) a.1
  · have hc : x ∈ centralInterval a.1 := ⟨hm.1, hm.2.le⟩
    rw [indicator_of_mem hm, indicator_of_mem hc, indicator_of_mem hm]
    exact hval x
  · rw [indicator_of_notMem hm, indicator_of_notMem hm, zero_mul, Complex.ofReal_zero]

/-- The chart forcing is bounded by the forcing and the `L¹` mass of the solution. -/
theorem norm_chartLocalizedForcing_le (C : ChartCutoff) (a : SuzukiPositiveAperture)
    (u g : suzukiApertureHilbert a) {Ag Lu : ℝ} (hAg : 0 ≤ Ag) (hLu : 0 ≤ Lu)
    (hg : ∀ᵐ x ∂volume, ‖(g : RealLineL2) x‖ ≤ Ag) (hu : ∫ x, ‖(u : RealLineL2) x‖ ≤ Lu) :
    ∀ᵐ y ∂volume, ‖((chartLocalizedForcing C a u g : LogarithmicHalfLineL2) : RealLineL2) y‖ ≤
      Ag + C.lip / 2 * Lu := by
  have hC0 : 0 ≤ C.lip / 2 := div_nonneg C.lip_nonneg (by norm_num)
  apply logarithmicHalfLineRestriction_bounded _ (add_nonneg hAg (mul_nonneg hC0 hLu))
  obtain ⟨τu, hτu⟩ : ∃ τu : RealLineL2, τu = logTranslationCLM (-a.1) (u : RealLineL2) := ⟨_, rfl⟩
  obtain ⟨τg, hτg⟩ : ∃ τg : RealLineL2, τg = logTranslationCLM (-a.1) (g : RealLineL2) := ⟨_, rfl⟩
  rw [← hτu, ← hτg]
  have hi := integrable_aperture a u
  have hv : (τu : ℝ → ℂ) =ᵐ[volume] fun x => (u : RealLineL2) (x + -a.1) := by
    rw [hτu]
    exact logarithmicTranslation_coeFn (-a.1) (u : RealLineL2)
  have hiτ : Integrable (τu : ℝ → ℂ) := (hi.comp_add_right (-a.1)).congr hv.symm
  have hint : ∫ t, ‖τu t‖ = ∫ x, ‖(u : RealLineL2) x‖ := by
    rw [← integral_add_right_eq_self (fun x => ‖(u : RealLineL2) x‖) (-a.1)]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    rw [hx]
  have hgt := (measurePreserving_add_right (volume : Measure ℝ) (-a.1)).quasiMeasurePreserving.ae hg
  have hgv : (τg : ℝ → ℂ) =ᵐ[volume] fun x => (g : RealLineL2) (x + -a.1) := by
    rw [hτg]
    exact logarithmicTranslation_coeFn (-a.1) (g : RealLineL2)
  filter_upwards [Lp.coeFn_add (C.mult τg) (C.comm.op τu), C.mult_coeFn τg, hgv, hgt,
    C.comm.op_coeFn τu] with y hadd hm ht hgy hk
  rw [hadd, Pi.add_apply]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [hm, ht, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ 1 * Ag := mul_le_mul (C.abs_le y) hgy (norm_nonneg _) zero_le_one
      _ = Ag := one_mul _
  · rw [hk]
    change ‖C.commutatorIntegral (τu : ℝ → ℂ) y‖ ≤ _
    refine (C.norm_commutatorIntegral_le hiτ y).trans ?_
    rw [hint]
    exact mul_le_mul_of_nonneg_left hu hC0

namespace WeilHilbertBeforeContact

/-! ### The right residual -/

private theorem fit_neg {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) :
    a.1.1 + |-(b.1.1 - a.1.1)| ≤ b.1.1 := by
  rw [abs_neg, abs_of_nonneg (sub_nonneg.mpr hab)]
  linarith only

/-- Translation to the right edge of the larger window. -/
def rightTranslate {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) :
    WeilHilbertBeforeContact a →ₗᵢ[ℂ] WeilHilbertBeforeContact b :=
  translate (-(b.1.1 - a.1.1)) (fit_neg hab)

/-- The residual of the Riesz vector with respect to the right translate. -/
def rightResidual {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (ζ : ℂ) :
    WeilHilbertBeforeContact b :=
  evalVector b ζ - chartPhase (-ζ) (b.1.1 - a.1.1) • rightTranslate hab (evalVector a ζ)

/-- **The residual is Weil orthogonal to the old window.** -/
theorem inner_rightResidual_translate {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (ζ : ℂ)
    (x : WeilHilbertBeforeContact a) :
    inner ℂ (rightResidual hab ζ) (rightTranslate hab x) = 0 := by
  obtain ⟨h, hh⟩ : ∃ h, h = b.1.1 - a.1.1 := ⟨_, rfl⟩
  have h1 : eval b ζ (rightTranslate hab x) =
      Complex.exp (-I * ζ * ((-(b.1.1 - a.1.1) : ℝ) : ℂ)) * eval a ζ x :=
    fourier_translate (-(b.1.1 - a.1.1)) (fit_neg hab) x ζ
  have hconj : (starRingEnd ℂ) (chartPhase (-ζ) (b.1.1 - a.1.1)) =
      Complex.exp (-I * ζ * ((-(b.1.1 - a.1.1) : ℝ) : ℂ)) := by
    rw [chartPhase, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
    push_cast
    ring
  rw [rightResidual, inner_sub_left (E := WeilHilbertBeforeContact b),
    inner_smul_left (E := WeilHilbertBeforeContact b), (rightTranslate hab).inner_map_map,
    inner_evalVector, inner_evalVector, h1, hconj, sub_self]

/-- The physical source of the residual is the reflected increment. -/
theorem physical_rightResidual_ae {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (ζ : ℂ) :
    (ccmArchimedeanFormEmbedding b.1 (toForm b (rightResidual hab ζ)) : ℝ → ℂ) =ᵐ[volume]
      fun x => chartIncrement a b (-ζ) (b.1.1 - x) := by
  have hval : ccmArchimedeanFormEmbedding b.1 (toForm b (rightResidual hab ζ)) =
      ccmArchimedeanFormEmbedding b.1 (toForm b (evalVector b ζ)) -
        chartPhase (-ζ) (b.1.1 - a.1.1) • logTranslationCLM (-(b.1.1 - a.1.1))
          (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a ζ))) := by
    rw [rightResidual]
    simp only [map_sub, map_smul]
    congr 2
    exact physical_translate (-(b.1.1 - a.1.1)) (fit_neg hab) (evalVector a ζ)
  rw [hval]
  have hshift := (evalVectorContinuousRepresentative_ae a ζ).comp_tendsto
    (MellinL2.realTranslation_measurePreserving (-(b.1.1 - a.1.1))).quasiMeasurePreserving.tendsto_ae
  filter_upwards [Lp.coeFn_sub (ccmArchimedeanFormEmbedding b.1 (toForm b (evalVector b ζ)))
      (chartPhase (-ζ) (b.1.1 - a.1.1) • logTranslationCLM (-(b.1.1 - a.1.1))
        (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a ζ)))),
    Lp.coeFn_smul (chartPhase (-ζ) (b.1.1 - a.1.1)) (logTranslationCLM (-(b.1.1 - a.1.1))
      (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a ζ)))),
    logarithmicTranslation_coeFn (-(b.1.1 - a.1.1))
      (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a ζ))),
    evalVectorContinuousRepresentative_ae b ζ, hshift] with x h1 h2 h3 h4 h5
  change evalVectorContinuousRepresentative a ζ (x + -(b.1.1 - a.1.1)) =
    ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a ζ)) (x + -(b.1.1 - a.1.1)) at h5
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul, h3, ← h4, ← h5, chartIncrement, chartSource,
    chartSource, evalVectorContinuousRepresentative_neg, evalVectorContinuousRepresentative_neg]
  congr 3 <;> ring

/-- **The sharp cut of the residual.** It is a translate of a vector of the old window plus a collar. -/
theorem exists_rightResidual_cut {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (ζ : ℂ) :
    ∃ (wv : WeilHilbertBeforeContact a) (bv : WeilHilbertBeforeContact b),
      rightResidual hab ζ = rightTranslate hab wv + bv ∧
      (ccmArchimedeanFormEmbedding a.1 (toForm a wv) : ℝ → ℂ) =ᵐ[volume]
        (Ico (-a.1.1) a.1.1).indicator (fun x => chartIncrement a b (-ζ) (a.1.1 - x)) ∧
      (ccmArchimedeanFormEmbedding b.1 (toForm b bv) : ℝ → ℂ) =ᵐ[volume]
        (Ico (-b.1.1) (2 * (b.1.1 - a.1.1) - b.1.1)).indicator
          (fun x => chartIncrement a b (-ζ) (b.1.1 - x)) := by
  have ha0 : 0 < a.1.1 := a.1.2
  have hb0 : 0 < b.1.1 := b.1.2
  obtain ⟨h, hh⟩ : ∃ h, h = b.1.1 - a.1.1 := ⟨_, rfl⟩
  have hh0 : 0 ≤ h := by
    rw [hh]
    exact sub_nonneg.mpr hab
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, u₀ = toForm b (rightResidual hab ζ) := ⟨_, rfl⟩
  have hφ := physical_rightResidual_ae hab ζ
  rw [← hu₀] at hφ
  rw [← hh] at hφ ⊢
  have hs₁ : Ico (2 * h - b.1.1) b.1.1 ⊆ centralInterval b.1.1 := fun x hx =>
    ⟨by linarith only [hx.1, hh0], hx.2.le⟩
  have hs₂ : Ico (-b.1.1) (2 * h - b.1.1) ⊆ centralInterval b.1.1 := fun x hx =>
    ⟨hx.1, by linarith only [hx.2, hh, ha0]⟩
  obtain ⟨wb, hwb⟩ := exists_ccm_form_of_intervalRestriction b.1 b.1 hs₁ u₀
  obtain ⟨bb, hbb⟩ := exists_ccm_form_of_intervalRestriction b.1 b.1 hs₂ u₀
  have hcut (s : Set ℝ) (hs : MeasurableSet s) :
      (indicatorCutoff s hs (ccmArchimedeanFormEmbedding b.1 u₀) : ℝ → ℂ) =ᵐ[volume]
        s.indicator (fun x => chartIncrement a b (-ζ) (b.1.1 - x)) := by
    filter_upwards [indicatorCutoff_ae s hs (ccmArchimedeanFormEmbedding b.1 u₀), hφ] with x h1 h2
    rw [h1]
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx, indicator_of_mem hx, h2]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  have hwbv := hcut (Ico (2 * h - b.1.1) b.1.1) measurableSet_Ico
  rw [← hwb] at hwbv
  have hbbv := hcut (Ico (-b.1.1) (2 * h - b.1.1)) measurableSet_Ico
  rw [← hbb] at hbbv
  -- The vector over the old window.
  obtain ⟨fw, hfw⟩ : ∃ fw : RealLineL2, fw =
      logTranslationCLM h (ccmArchimedeanFormEmbedding b.1 wb) := ⟨_, rfl⟩
  have hfwv : (fw : ℝ → ℂ) =ᵐ[volume]
      (Ico (-a.1.1) a.1.1).indicator (fun x => chartIncrement a b (-ζ) (a.1.1 - x)) := by
    have ht := (measurePreserving_add_right (volume : Measure ℝ) h).quasiMeasurePreserving.ae hwbv
    rw [hfw]
    filter_upwards [logarithmicTranslation_coeFn h (ccmArchimedeanFormEmbedding b.1 wb), ht] with x h1 h2
    rw [h1, h2]
    by_cases hx : x ∈ Ico (-a.1.1) a.1.1
    · rw [indicator_of_mem hx, indicator_of_mem (show x + h ∈ Ico (2 * h - b.1.1) b.1.1 from
        ⟨by linarith only [hx.1, hh], by linarith only [hx.2, hh]⟩)]
      congr 1
      linarith only [hh]
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun hm : x + h ∈ Ico (2 * h - b.1.1) b.1.1 =>
        hx ⟨by linarith only [hm.1, hh], by linarith only [hm.2, hh]⟩)]
  have hfwmem : fw ∈ suzukiApertureHilbert a.1 := by
    refine LinearMap.mem_range.mpr ⟨fw, Lp.ext ?_⟩
    filter_upwards [indicatorCutoff_ae (centralInterval a.1.1) (measurableSet_centralInterval a.1.1) fw,
      hfwv] with x h1 h2
    change indicatorCutoff (centralInterval a.1.1) (measurableSet_centralInterval a.1.1) fw x = _
    rw [h1]
    by_cases hx : x ∈ centralInterval a.1.1
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, h2, indicator_of_notMem (fun hm : x ∈ Ico (-a.1.1) a.1.1 =>
        hx ⟨hm.1, hm.2.le⟩)]
  have hfwE : HasLogarithmicEnergy fw := by
    rw [hfw]
    exact hasLogarithmicEnergy_translation h (hasLogarithmicEnergy_ccm_form b.1 wb)
  obtain ⟨w, hw⟩ := exists_ccm_form_of_logarithmicEnergy a.1 ⟨fw, hfwmem⟩ hfwE
  have hwcoe : ccmArchimedeanFormEmbedding a.1 w = fw := congrArg Subtype.val hw
  refine ⟨(toForm a).symm w, (toForm b).symm bb, ?_, ?_, ?_⟩
  · apply (toForm b).injective
    rw [map_add, LinearEquiv.apply_symm_apply, ← hu₀]
    apply ccmArchimedeanFormEmbedding_injective b.1
    rw [map_add]
    have hT : ccmArchimedeanFormEmbedding b.1 (toForm b (rightTranslate hab ((toForm a).symm w))) =
        ccmArchimedeanFormEmbedding b.1 wb := by
      have hp := physical_translate (-(b.1.1 - a.1.1)) (fit_neg hab) ((toForm a).symm w)
      rw [LinearEquiv.apply_symm_apply, hwcoe, hfw, ← hh] at hp
      refine hp.trans ?_
      exact congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T (ccmArchimedeanFormEmbedding b.1 wb))
        (logTranslationCLM_neg_mul h)
    rw [hT]
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (ccmArchimedeanFormEmbedding b.1 wb)
      (ccmArchimedeanFormEmbedding b.1 bb), hwbv, hbbv, hφ] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, h3, h4]
    by_cases hx1 : x < -b.1.1
    · rw [indicator_of_notMem (fun hm : x ∈ Ico (2 * h - b.1.1) b.1.1 => by
          linarith only [hm.1, hx1, hh0]),
        indicator_of_notMem (fun hm : x ∈ Ico (-b.1.1) (2 * h - b.1.1) => by linarith only [hm.1, hx1]),
        add_zero]
      exact chartIncrement_eq_zero hab _ (Or.inr (by linarith only [hx1]))
    by_cases hx2 : x < 2 * h - b.1.1
    · rw [indicator_of_notMem (fun hm : x ∈ Ico (2 * h - b.1.1) b.1.1 => by linarith only [hm.1, hx2]),
        indicator_of_mem (show x ∈ Ico (-b.1.1) (2 * h - b.1.1) from ⟨not_lt.mp hx1, hx2⟩), zero_add]
    by_cases hx3 : x < b.1.1
    · rw [indicator_of_mem (show x ∈ Ico (2 * h - b.1.1) b.1.1 from ⟨not_lt.mp hx2, hx3⟩),
        indicator_of_notMem (fun hm : x ∈ Ico (-b.1.1) (2 * h - b.1.1) => hx2 hm.2), add_zero]
    · rw [indicator_of_notMem (fun hm : x ∈ Ico (2 * h - b.1.1) b.1.1 => hx3 hm.2),
        indicator_of_notMem (fun hm : x ∈ Ico (-b.1.1) (2 * h - b.1.1) => by
          linarith only [hm.2, not_lt.mp hx3, hh, ha0]), add_zero]
      exact chartIncrement_eq_zero hab _ (Or.inl (by linarith only [not_lt.mp hx3]))
  · rw [LinearEquiv.apply_symm_apply, hwcoe]
    exact hfwv
  · rw [LinearEquiv.apply_symm_apply]
    exact hbbv

/-- The Riesz identity across the cut: the pairing with the old part is minus the pairing with the collar. -/
theorem inner_source_eq_neg_collar {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (ζ : ℂ)
    (g : suzukiApertureHilbert a.1) (wv : WeilHilbertBeforeContact a) (bv : WeilHilbertBeforeContact b)
    (hcut : rightResidual hab ζ = rightTranslate hab wv + bv) :
    inner ℂ g (ccmArchimedeanFormToAperture a.1 (toForm a wv)) =
      -inner ℂ (rightTranslate hab (sourceVector a g)) bv := by
  have h1 := inner_sourceVector a g wv
  have h2 : inner ℂ (rightTranslate hab (sourceVector a g)) (rightTranslate hab wv) =
      inner ℂ (sourceVector a g) wv := (rightTranslate hab).inner_map_map _ _
  have h0 : inner ℂ (rightTranslate hab (sourceVector a g)) (rightResidual hab ζ) = 0 := by
    have := inner_rightResidual_translate hab ζ (sourceVector a g)
    rw [← inner_conj_symm, this, map_zero]
  rw [hcut, inner_add_right (E := WeilHilbertBeforeContact b)] at h0
  rw [← h1, ← h2]
  linear_combination h0

/-- The Weil inner product is the logarithmic form minus the bounded adjustment. -/
theorem inner_eq_full_sub (b : PrecontactAperture) (x y : WeilHilbertBeforeContact b) :
    inner ℂ x y = logarithmicFullForm (ccmArchimedeanFormEmbedding b.1 (toForm b x))
        (ccmArchimedeanFormEmbedding b.1 (toForm b y)) -
      inner ℂ ((logarithmicDirichletAdjustment b.1 - ccmRestrictedWeilBoundedRemainder b.1)
        (ccmArchimedeanFormToAperture b.1 (toForm b x)))
          (ccmArchimedeanFormToAperture b.1 (toForm b y)) := by
  rw [inner_eq_weil, ccmRestrictedWeilForm, logarithmicFullForm_ccm_embedding,
    logarithmicDirichletForm_eq_adjustment, sub_apply, inner_sub_left]
  ring

/-- The bounded adjustment of the Weil form is uniformly bounded on bounded vectors. -/
theorem exists_uniform_adjustment_bound (a₂ : PrecontactAperture) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b : PrecontactAperture, b.1.1 ≤ a₂.1.1 → ∀ u : CCMArchimedeanFormDomain b.1,
      ∀ {A : ℝ}, 0 ≤ A → (∫ x, ‖(ccmArchimedeanFormToAperture b.1 u : RealLineL2) x‖) ≤ A →
        (∀ᵐ x ∂volume, ‖(ccmArchimedeanFormToAperture b.1 u : RealLineL2) x‖ ≤ A) →
        ∀ᵐ x ∂volume, ‖(((logarithmicDirichletAdjustment b.1 - ccmRestrictedWeilBoundedRemainder b.1)
          (ccmArchimedeanFormToAperture b.1 u) : suzukiApertureHilbert b.1) : RealLineL2) x‖ ≤ K * A := by
  obtain ⟨E, hEd⟩ : ∃ E, E = Real.exp (a₂.1.1 / 2) := ⟨_, rfl⟩
  have hE0 : 0 < E := hEd ▸ Real.exp_pos _
  obtain ⟨D, hDd⟩ : ∃ D : ℝ, D = 0 + |logarithmicFormScalar| + ‖ccmArchimedeanRemainderScalar‖ := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    rw [hDd]
    positivity
  obtain ⟨K₂, hK₂d⟩ : ∃ K₂, K₂ = D + ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊,
      |vonMangoldtWeight n| * (1 / Real.sqrt n) * 2 := ⟨_, rfl⟩
  have hK₂0 : 0 ≤ K₂ := by
    rw [hK₂d]
    exact add_nonneg hD0 (Finset.sum_nonneg fun n _ => by positivity)
  refine ⟨3 / 4 + (E + E) * E + K₂, by positivity, fun b hb u A hA hL hM => ?_⟩
  obtain ⟨U, hU⟩ : ∃ U, U = ccmArchimedeanFormToAperture b.1 u := ⟨_, rfl⟩
  rw [← hU] at hL hM ⊢
  have hzero : ∀ᵐ x ∂volume, ‖((0 : suzukiApertureHilbert b.1) : RealLineL2) x‖ ≤
      0 + 0 * ‖(ccmArchimedeanFormToAperture b.1 u : RealLineL2) x‖ := by
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx
    change ‖((0 : RealLineL2) : ℝ → ℂ) x‖ ≤ _
    rw [hx, Pi.zero_apply, norm_zero]
    norm_num
  have hdom := weightedForcing_dominated vonMangoldtWeight b.1 u 0 hzero
  rw [← hU, ← hDd] at hdom
  have hF : weightedForcing vonMangoldtWeight b.1 u 0 =
      (logarithmicDirichletAdjustment b.1 - ccmRestrictedWeilBoundedRemainder b.1) U := by
    rw [weightedForcing, zero_add, ← hU]
    rfl
  rw [hF] at hdom
  have hbb : b.1.1 / 2 ≤ a₂.1.1 / 2 := by linarith only [hb]
  have hexp : Real.exp (b.1.1 / 2) ≤ E := by
    rw [hEd]
    exact Real.exp_le_exp.mpr hbb
  have hI0 : 0 ≤ ∫ x, ‖(U : RealLineL2) x‖ := integral_nonneg fun _ => norm_nonneg _
  have hpb : Real.exp (b.1.1 / 2) * ∫ x, ‖(U : RealLineL2) x‖ ≤ E * A :=
    mul_le_mul hexp hL hI0 hE0.le
  have hp₁ := (norm_inner_polar_le b.1 (s := -1 / 2) (by norm_num [abs_le]) U).trans hpb
  have hp₂ := (norm_inner_polar_le b.1 (s := 1 / 2) (by norm_num [abs_le]) U).trans hpb
  have hpol : (‖inner ℂ (ccmPolarApertureVector b.1 (-1 / 2)) U‖ +
      ‖inner ℂ (ccmPolarApertureVector b.1 (1 / 2)) U‖) * Real.exp (b.1.1 / 2) ≤ (E * A + E * A) * E :=
    mul_le_mul (add_le_add hp₁ hp₂) hexp (Real.exp_pos _).le (by positivity)
  have hsum : ∑ j ∈ weightedIndexSet b.1, weightedCoeff vonMangoldtWeight D j ≤ K₂ := by
    rw [sum_weightedCoeff, hK₂d]
    refine add_le_add le_rfl (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor (Real.exp_le_exp.mpr ?_)))
      fun n _ _ => by positivity)
    linarith only [hb]
  have hall : ∀ᵐ x ∂(volume : Measure ℝ), ∀ j ∈ weightedIndexSet b.1,
      ‖(U : RealLineL2) (x - weightedShift j)‖ ≤ A :=
    (Filter.eventually_all_finset _).mpr fun j _ =>
      (measurePreserving_sub_right (volume : Measure ℝ) (weightedShift j)).quasiMeasurePreserving.ae hM
  filter_upwards [hdom, hall] with x h1 h2
  have hs : ∑ j ∈ weightedIndexSet b.1, weightedCoeff vonMangoldtWeight D j *
      ‖(U : RealLineL2) (x - weightedShift j)‖ ≤ K₂ * A := by
    calc
      _ ≤ ∑ j ∈ weightedIndexSet b.1, weightedCoeff vonMangoldtWeight D j * A :=
        Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (h2 j hj)
          (weightedCoeff_nonneg vonMangoldtWeight hD0 j)
      _ = (∑ j ∈ weightedIndexSet b.1, weightedCoeff vonMangoldtWeight D j) * A :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hsum hA
  have hl : 3 / 4 * (∫ x, ‖(U : RealLineL2) x‖) ≤ 3 / 4 * A :=
    mul_le_mul_of_nonneg_left hL (by norm_num)
  have he : (3 / 4 + (E + E) * E + K₂) * A = 3 / 4 * A + (E * A + E * A) * E + K₂ * A := by ring
  rw [he]
  linarith only [h1, hl, hpol, hs]

/-! ### The energy across the collar -/

/-- **The energy across the collar is linear in the shift.** -/
theorem norm_collar_energy_le {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (ζ : ℂ)
    (U F : suzukiApertureHilbert a.1) (hU : HasLogarithmicEnergy (U : RealLineL2))
    (hsolve : ∀ f : suzukiApertureHilbert a.1, HasLogarithmicEnergy (f : RealLineL2) →
      logarithmicFullForm (f : RealLineL2) (U : RealLineL2) =
        inner ℂ (f : RealLineL2) (F : RealLineL2))
    (Ca Cb : ChartCutoff) (hCa : ∀ x, 2 * a.1.1 ≤ x → Ca.toFun x = 0)
    (hCb : ∀ x, 2 * b.1.1 ≤ x → Cb.toFun x = 0)
    (hshift : ∀ r, Cb.toFun r = Ca.toFun (r - 2 * (b.1.1 - a.1.1)))
    (hone : ∀ r, r ≤ 2 * (b.1.1 - a.1.1) → Cb.toFun r = 1)
    (B : LogarithmicHalfLineL2) (hBE : HasLogarithmicEnergy (B : RealLineL2))
    (hB : (B : RealLineL2) =ᵐ[volume] (Ico 0 (2 * (b.1.1 - a.1.1))).indicator (chartSource b ζ))
    {A₁ A₂ : ℝ} (h₁ : ∀ᵐ y ∂volume,
      ‖((chartLocalizedForcing Ca a.1 U F : LogarithmicHalfLineL2) : RealLineL2) y‖ ≤ A₁)
    (h₂ : ∀ᵐ y ∂volume, ‖((chartForcing Cb b ζ : LogarithmicHalfLineL2) : RealLineL2) y‖ ≤ A₂)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) :
    ‖logarithmicFullForm (B : RealLineL2)
      (Cb.mult (logTranslationCLM (-(a.1.1 + 2 * (b.1.1 - a.1.1))) (U : RealLineL2)))‖ ≤
      2 * (b.1.1 - a.1.1) * (A₁ * A₂) := by
  obtain ⟨τ, hτd⟩ : ∃ τ, τ = 2 * (b.1.1 - a.1.1) := ⟨_, rfl⟩
  have hτ : 0 ≤ τ := by
    rw [hτd]
    linarith only [hab]
  rw [← hτd] at hB hshift hone ⊢
  -- The two Green solutions.
  obtain ⟨hPE, hPs⟩ := chartLocalized_solves Ca a.1 hCa U F hU hsolve
  have hP := logarithmicHalfLineGreenOperator_unique _ _ hPE hPs
  have hGreen₂ : ((logarithmicHalfLineGreenOperator (chartForcing Cb b ζ) :
      LogarithmicHalfLineL2) : RealLineL2) =ᵐ[volume] fun r => (Cb.toFun r : ℂ) * chartSource b ζ r := by
    filter_upwards [logarithmicHalfLineGreenOperator_eq_representative (chartForcing Cb b ζ)] with r hr
    rw [hr, logarithmicGreenRepresentative_chartForcing Cb b hCb ζ r]
  have hBv : (B : RealLineL2) =ᵐ[volume] (Iio τ).indicator
      ((logarithmicHalfLineGreenOperator (chartForcing Cb b ζ) : LogarithmicHalfLineL2) : RealLineL2) := by
    filter_upwards [hB, hGreen₂] with r h1 h2
    rw [h1]
    by_cases hr : r < τ
    · rw [indicator_of_mem (show r ∈ Iio τ from hr), h2, hone r hr.le, Complex.ofReal_one, one_mul]
      by_cases hr0 : 0 ≤ r
      · rw [indicator_of_mem (show r ∈ Ico 0 τ from ⟨hr0, hr⟩)]
      · rw [indicator_of_notMem (fun hm : r ∈ Ico 0 τ => hr0 hm.1),
          chartSource_eq_zero b ζ (Or.inl (not_le.mp hr0).le)]
    · rw [indicator_of_notMem (show r ∉ Iio τ from hr),
        indicator_of_notMem (fun hm : r ∈ Ico 0 τ => hr hm.2)]
  have hcut := norm_halfLineForm_shift_green_cut_le (chartLocalizedForcing Ca a.1 U F)
    (chartForcing Cb b ζ) τ hτ B hBE hBv h₁ h₂ hA₁ hA₂
  rw [← hP] at hcut
  -- The cut solution is the shift of the localized solution.
  have hmult : Cb.mult (logTranslationCLM (-(a.1.1 + τ)) (U : RealLineL2)) =
      ((halfShift τ hτ (chartLocalized Ca a.1 U) : LogarithmicHalfLineL2) : RealLineL2) := by
    apply Lp.ext
    have ht := (measurePreserving_sub_right (volume : Measure ℝ) τ).quasiMeasurePreserving.ae
      (Ca.mult_coeFn (logTranslationCLM (-a.1.1) (U : RealLineL2)))
    have ht2 := (measurePreserving_sub_right (volume : Measure ℝ) τ).quasiMeasurePreserving.ae
      (logarithmicTranslation_coeFn (-a.1.1) (U : RealLineL2))
    filter_upwards [Cb.mult_coeFn (logTranslationCLM (-(a.1.1 + τ)) (U : RealLineL2)),
      logarithmicTranslation_coeFn (-(a.1.1 + τ)) (U : RealLineL2),
      halfShift_coeFn τ hτ (chartLocalized Ca a.1 U), ht, ht2] with r h1 h2 h3 h4 h5
    rw [h1, h2, h3]
    change _ = Ca.mult (logTranslationCLM (-a.1.1) (U : RealLineL2)) (r - τ)
    rw [h4, h5, hshift r]
    congr 2
    ring
  rw [hmult]
  -- Conjugate symmetry of the form.
  have hconj := logarithmicFullForm_conj ((halfShift τ hτ (chartLocalized Ca a.1 U) :
    LogarithmicHalfLineL2) : RealLineL2) (B : RealLineL2)
  rw [← hconj, norm_star]
  exact hcut.trans (le_of_eq (by rw [hτd]))

/-! ### The Lipschitz bound -/

/-- The increment splits into the old part and the collar. -/
theorem integral_norm_chartIncrement_le_split {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (z : ℂ)
    {M : ℝ} (hM : ∀ t, ‖chartSource b z t‖ ≤ M) :
    ∫ t, ‖chartIncrement a b z t‖ ≤
      (∫ x in Ico (-a.1.1) a.1.1, ‖chartIncrement a b z (a.1.1 - x)‖) + 2 * (b.1.1 - a.1.1) * M := by
  have ha0 : 0 < a.1.1 := a.1.2
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun t => ‖chartIncrement a b z t‖ := ⟨_, rfl⟩
  have hFc : Continuous F := by
    rw [hF]
    exact (continuous_chartIncrement a b z).norm
  have hFi : Integrable F := by
    rw [hF]
    exact ((continuous_chartIncrement a b z).integrable_of_hasCompactSupport
      (hasCompactSupport_chartIncrement hab z)).norm
  have h1i : Integrable ((Ioc 0 (2 * a.1.1)).indicator F) :=
    hFi.integrableOn.integrable_indicator measurableSet_Ioc
  have h2i : Integrable ((Ioc (2 * a.1.1) (2 * b.1.1)).indicator fun _ => M) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Ioc
  have hpt : ∀ t, F t ≤ (Ioc 0 (2 * a.1.1)).indicator F t +
      (Ioc (2 * a.1.1) (2 * b.1.1)).indicator (fun _ => M) t := by
    intro t
    have hF0 : 0 ≤ F t := by
      rw [hF]
      exact norm_nonneg _
    by_cases ht0 : t ≤ 0
    · have : F t = 0 := by
        rw [hF]
        simp only
        rw [chartIncrement_eq_zero hab z (Or.inl ht0), norm_zero]
      rw [this, indicator_of_notMem (fun hm : t ∈ Ioc 0 (2 * a.1.1) => absurd hm.1 (not_lt.mpr ht0)),
        indicator_of_notMem (fun hm : t ∈ Ioc (2 * a.1.1) (2 * b.1.1) => by
          linarith only [hm.1, ht0, ha0]), add_zero]
    by_cases ht1 : t ≤ 2 * a.1.1
    · rw [indicator_of_mem (show t ∈ Ioc 0 (2 * a.1.1) from ⟨not_le.mp ht0, ht1⟩)]
      exact le_add_of_nonneg_right (indicator_nonneg (fun _ _ => hM0) _)
    by_cases ht2 : t ≤ 2 * b.1.1
    · rw [indicator_of_mem (show t ∈ Ioc (2 * a.1.1) (2 * b.1.1) from ⟨not_le.mp ht1, ht2⟩)]
      have hv : F t = ‖chartSource b z t‖ := by
        rw [hF]
        simp only
        rw [chartIncrement, chartSource_eq_zero a z (Or.inr (not_le.mp ht1).le), mul_zero, sub_zero]
      rw [hv]
      exact (hM t).trans (le_add_of_nonneg_left (indicator_nonneg
        (fun _ _ => by rw [hF]; exact norm_nonneg _) _))
    · have : F t = 0 := by
        rw [hF]
        simp only
        rw [chartIncrement_eq_zero hab z (Or.inr (not_le.mp ht2).le), norm_zero]
      rw [this]
      exact add_nonneg (indicator_nonneg (fun _ _ => by rw [hF]; exact norm_nonneg _) _)
        (indicator_nonneg (fun _ _ => hM0) _)
  have hint := integral_mono hFi (h1i.add h2i) hpt
  rw [integral_add h1i h2i] at hint
  have hc2 : (∫ t, (Ioc (2 * a.1.1) (2 * b.1.1)).indicator (fun _ => M) t) = 2 * (b.1.1 - a.1.1) * M := by
    rw [integral_indicator measurableSet_Ioc, setIntegral_const,
      Real.volume_real_Ioc_of_le (by linarith only [hab]), smul_eq_mul]
    ring
  have hc1 : (∫ t, (Ioc 0 (2 * a.1.1)).indicator F t) =
      ∫ x in Ico (-a.1.1) a.1.1, ‖chartIncrement a b z (a.1.1 - x)‖ := by
    rw [← integral_sub_left_eq_self ((Ioc 0 (2 * a.1.1)).indicator F) volume a.1.1,
      ← integral_indicator measurableSet_Ico]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Ico (-a.1.1) a.1.1
    · rw [indicator_of_mem hx, indicator_of_mem (show a.1.1 - x ∈ Ioc 0 (2 * a.1.1) from
        ⟨by linarith only [hx.2], by linarith only [hx.1]⟩), hF]
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun hm : a.1.1 - x ∈ Ioc 0 (2 * a.1.1) =>
        hx ⟨by linarith only [hm.2], by linarith only [hm.1]⟩)]
  rw [hc1, hc2] at hint
  rw [show (∫ t, ‖chartIncrement a b z t‖) = ∫ t, F t by rw [hF]]
  exact hint

/-- **The Riesz increments are Lipschitz in `L¹`.** -/
theorem exists_chartIncrement_lipschitz (a₁ a₂ : PrecontactAperture) (z : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : PrecontactAperture, a₁.1.1 ≤ a.1.1 → a.1.1 ≤ b.1.1 → b.1.1 ≤ a₂.1.1 →
      ∫ t, ‖chartIncrement a b z t‖ ≤ C * (b.1.1 - a.1.1) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ, ζ = -z := ⟨_, rfl⟩
  have hzζ : -ζ = z := by rw [hζ, neg_neg]
  obtain ⟨Au, hAu0, hAu⟩ := exists_uniform_source_bound a₁ a₂
  obtain ⟨Ab, hAb0, hAb⟩ := exists_uniform_endpoint_data a₁ a₂ ζ
  obtain ⟨Mz, hMz0, hMz⟩ := exists_uniform_chartSource_bound a₁ a₂ z
  obtain ⟨K₃, hK₃0, hK₃⟩ := exists_uniform_adjustment_bound a₂
  obtain ⟨c, hcd⟩ : ∃ c, c = a₁.1.1 := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hcd]
    exact a₁.1.2
  have ha₂0 : 0 < a₂.1.1 := a₂.1.2
  obtain ⟨Lp₀, hLp₀⟩ : ∃ Lp₀ : ℝ, Lp₀ = 2 / c := ⟨_, rfl⟩
  have hLp0 : 0 ≤ Lp₀ := by
    rw [hLp₀]
    positivity
  obtain ⟨A₁, hA₁d⟩ : ∃ A₁, A₁ = Au + Lp₀ / 2 * Au := ⟨_, rfl⟩
  have hA₁0 : 0 ≤ A₁ := by
    rw [hA₁d]
    positivity
  obtain ⟨N, hNd⟩ : ∃ N, N = Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊ := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂d⟩ : ∃ A₂, A₂ = Real.exp (2 * a₂.1.1 * |ζ.im|) + chartSupConstant N * Ab +
      chartBoundedConstant (2 * a₂.1.1) (2 * a₂.1.1) * Ab + Lp₀ / 2 * Ab := ⟨_, rfl⟩
  have hA₂0 : 0 ≤ A₂ := by
    rw [hA₂d]
    have h1 := chartSupConstant_nonneg N
    have h2 := chartBoundedConstant_nonneg (2 * a₂.1.1) (2 * a₂.1.1)
    positivity
  refine ⟨2 * (A₁ * A₂ + Ab * (Lp₀ / 2 * Au) + Ab * (K₃ * Au) + Mz + Ab), by positivity,
    fun a b h1 hab hb => ?_⟩
  have ha0 : 0 < a.1.1 := a.1.2
  have hb0 : 0 < b.1.1 := b.1.2
  have hba₁ : a₁.1.1 ≤ b.1.1 := h1.trans hab
  obtain ⟨h, hh⟩ : ∃ h, h = b.1.1 - a.1.1 := ⟨_, rfl⟩
  have hh0 : 0 ≤ h := by
    rw [hh]
    linarith only [hab]
  obtain ⟨τ, hτd⟩ : ∃ τ, τ = 2 * h := ⟨_, rfl⟩
  have hτ0 : 0 ≤ τ := by
    rw [hτd]
    linarith only [hh0]
  have hac : c ≤ a.1.1 := by
    rw [hcd]
    exact h1
  -- The sign of the old part and its Riesz vector.
  obtain ⟨wv, bv, hcut, hwv, hbv⟩ := exists_rightResidual_cut hab ζ
  rw [hzζ] at hwv hbv
  obtain ⟨g, hg1, hgv⟩ := exists_signSource a.1 (fun x => chartIncrement a b z (a.1.1 - x))
    ((continuous_chartIncrement a b z).comp (by fun_prop))
  have hI := hgv (ccmArchimedeanFormToAperture a.1 (toForm a wv)) hwv
  obtain ⟨hUL, hUM, hFM⟩ := hAu a h1 hb g hg1
  obtain ⟨U, hU⟩ : ∃ U, U = sourcePhysical a g := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = sourceForcing a g := ⟨_, rfl⟩
  rw [← hU] at hUL hUM
  rw [← hF] at hFM
  have hUE : HasLogarithmicEnergy (U : RealLineL2) := by
    rw [hU]
    exact hasLogarithmicEnergy_sourcePhysical a g
  have hsolve : ∀ f : suzukiApertureHilbert a.1, HasLogarithmicEnergy (f : RealLineL2) →
      logarithmicFullForm (f : RealLineL2) (U : RealLineL2) = inner ℂ (f : RealLineL2) (F : RealLineL2) := by
    rw [hU, hF]
    exact sourcePhysical_logarithmicFullForm a g
  -- The translated source.
  obtain ⟨Tu, hTu⟩ : ∃ Tu, Tu = rightTranslate hab (sourceVector a g) := ⟨_, rfl⟩
  have hTuv : ccmArchimedeanFormEmbedding b.1 (toForm b Tu) =
      logTranslationCLM (-h) (U : RealLineL2) := by
    rw [hTu, hU, hh]
    exact physical_translate (-(b.1.1 - a.1.1)) (fit_neg hab) (sourceVector a g)
  have hTuae : (ccmArchimedeanFormEmbedding b.1 (toForm b Tu) : ℝ → ℂ) =ᵐ[volume]
      fun x => (U : RealLineL2) (x + -h) := by
    rw [hTuv]
    exact logarithmicTranslation_coeFn (-h) (U : RealLineL2)
  have hTuL : ∫ x, ‖(ccmArchimedeanFormToAperture b.1 (toForm b Tu) : RealLineL2) x‖ ≤ Au := by
    refine le_trans (le_of_eq ?_) hUL
    rw [← integral_add_right_eq_self (fun x => ‖(U : RealLineL2) x‖) (-h)]
    apply integral_congr_ae
    filter_upwards [hTuae] with x hx
    change ‖ccmArchimedeanFormEmbedding b.1 (toForm b Tu) x‖ = _
    rw [hx]
  have hTuM : ∀ᵐ x ∂volume, ‖(ccmArchimedeanFormToAperture b.1 (toForm b Tu) : RealLineL2) x‖ ≤ Au := by
    have ht := (measurePreserving_add_right (volume : Measure ℝ) (-h)).quasiMeasurePreserving.ae hUM
    filter_upwards [hTuae, ht] with x h1 h2
    change ‖ccmArchimedeanFormEmbedding b.1 (toForm b Tu) x‖ ≤ _
    rw [h1]
    exact h2
  have hGb := hK₃ b hb (toForm b Tu) hAu0 hTuL hTuM
  -- The collar.
  obtain ⟨Jb, hJb⟩ : ∃ Jb, Jb = ccmArchimedeanFormToAperture b.1 (toForm b bv) := ⟨_, rfl⟩
  have hJbv : ((Jb : suzukiApertureHilbert b.1) : ℝ → ℂ) =ᵐ[volume]
      (Ico (-b.1.1) (τ - b.1.1)).indicator (fun x => chartSource b ζ (x + b.1.1)) := by
    rw [hJb]
    change (ccmArchimedeanFormEmbedding b.1 (toForm b bv) : ℝ → ℂ) =ᵐ[volume] _
    filter_upwards [hbv] with x hx
    rw [hx, ← hh, ← hτd]
    by_cases hm : x ∈ Ico (-b.1.1) (τ - b.1.1)
    · rw [indicator_of_mem hm, indicator_of_mem hm, chartIncrement,
        chartSource_eq_zero a z (Or.inr (by linarith only [hm.2, hτd, hh])), mul_zero, sub_zero,
        chartSource_reflect, ← hζ]
      congr 1
      ring
    · rw [indicator_of_notMem hm, indicator_of_notMem hm]
  have hJbL : ∫ x, ‖(Jb : RealLineL2) x‖ ≤ τ * Ab := by
    have hle : ∀ᵐ x ∂volume, ‖(Jb : RealLineL2) x‖ ≤
        (Ico (-b.1.1) (τ - b.1.1)).indicator (fun _ => Ab) x := by
      filter_upwards [hJbv] with x hx
      change ‖((Jb : suzukiApertureHilbert b.1) : ℝ → ℂ) x‖ ≤ _
      rw [hx]
      by_cases hm : x ∈ Ico (-b.1.1) (τ - b.1.1)
      · rw [indicator_of_mem hm, indicator_of_mem hm]
        exact ((hAb b hba₁ hb).2.2.1 _)
      · rw [indicator_of_notMem hm, indicator_of_notMem hm, norm_zero]
    have hci : Integrable ((Ico (-b.1.1) (τ - b.1.1)).indicator fun _ => Ab) :=
      (integrableOn_const (by simp)).integrable_indicator measurableSet_Ico
    calc
      _ ≤ ∫ x, (Ico (-b.1.1) (τ - b.1.1)).indicator (fun _ => Ab) x :=
        integral_mono_ae (integrable_aperture b.1 Jb).norm hci hle
      _ = _ := by
        rw [integral_indicator measurableSet_Ico, setIntegral_const,
          Real.volume_real_Ico_of_le (by linarith only [hτ0]), smul_eq_mul]
        ring
  -- The half-line collar and the cutoffs.
  obtain ⟨B, hB⟩ : ∃ B : LogarithmicHalfLineL2, (B : RealLineL2) =
      logTranslationCLM (-b.1.1) (Jb : RealLineL2) :=
    ⟨⟨logTranslationCLM (-b.1.1) (Jb : RealLineL2), by
      rw [mem_halfLineL2_iff]
      have hs := (measurePreserving_add_right (volume : Measure ℝ) (-b.1.1)).quasiMeasurePreserving.ae hJbv
      filter_upwards [logarithmicTranslation_coeFn (-b.1.1) (Jb : RealLineL2), hs] with x hx hz hneg
      rw [hx]
      change ((Jb : suzukiApertureHilbert b.1) : ℝ → ℂ) (x + -b.1.1) = 0
      rw [hz, indicator_of_notMem]
      intro hm
      linarith only [hm.1, hneg]⟩, rfl⟩
  have hJbE : HasLogarithmicEnergy (Jb : RealLineL2) := by
    rw [hJb]
    exact hasLogarithmicEnergy_ccm_form b.1 _
  have hBE : HasLogarithmicEnergy (B : RealLineL2) := by
    rw [hB]
    exact hasLogarithmicEnergy_translation (-b.1.1) hJbE
  have hBv : (B : RealLineL2) =ᵐ[volume] (Ico 0 τ).indicator (chartSource b ζ) := by
    have hs := (measurePreserving_add_right (volume : Measure ℝ) (-b.1.1)).quasiMeasurePreserving.ae hJbv
    rw [hB]
    filter_upwards [logarithmicTranslation_coeFn (-b.1.1) (Jb : RealLineL2), hs] with x hx hz
    rw [hx]
    change ((Jb : suzukiApertureHilbert b.1) : ℝ → ℂ) (x + -b.1.1) = _
    rw [hz]
    by_cases hm : x ∈ Ico 0 τ
    · rw [indicator_of_mem hm, indicator_of_mem (show x + -b.1.1 ∈ Ico (-b.1.1) (τ - b.1.1) from
        ⟨by linarith only [hm.1], by linarith only [hm.2]⟩), neg_add_cancel_comm]
    · rw [indicator_of_notMem hm, indicator_of_notMem (fun hn : x + -b.1.1 ∈ Ico (-b.1.1) (τ - b.1.1) =>
        hm ⟨by linarith only [hn.1], by linarith only [hn.2]⟩)]
  have hcdb : 2 * b.1.1 - c < 2 * b.1.1 - c / 2 := by linarith only [hc]
  have hcda : 2 * a.1.1 - c < 2 * a.1.1 - c / 2 := by linarith only [hc]
  obtain ⟨Ca, hCad⟩ : ∃ Ca, Ca = ChartCutoff.linear _ _ hcda := ⟨_, rfl⟩
  obtain ⟨Cb, hCbd⟩ : ∃ Cb, Cb = ChartCutoff.linear _ _ hcdb := ⟨_, rfl⟩
  have hCa : ∀ x, 2 * a.1.1 ≤ x → Ca.toFun x = 0 := fun x hx => by
    rw [hCad]
    exact ChartCutoff.linear_eq_zero hcda (by linarith only [hx, hc])
  have hCb : ∀ x, 2 * b.1.1 ≤ x → Cb.toFun x = 0 := fun x hx => by
    rw [hCbd]
    exact ChartCutoff.linear_eq_zero hcdb (by linarith only [hx, hc])
  have hshift : ∀ r, Cb.toFun r = Ca.toFun (r - 2 * (b.1.1 - a.1.1)) := fun r => by
    rw [hCad, hCbd]
    change min (max ((2 * b.1.1 - c / 2 - r) / (2 * b.1.1 - c / 2 - (2 * b.1.1 - c))) 0) 1 =
      min (max ((2 * a.1.1 - c / 2 - (r - 2 * (b.1.1 - a.1.1))) /
        (2 * a.1.1 - c / 2 - (2 * a.1.1 - c))) 0) 1
    congr 3
    · ring
    · ring
  have hone : ∀ r, r ≤ 2 * (b.1.1 - a.1.1) → Cb.toFun r = 1 := fun r hr => by
    rw [hCbd]
    exact ChartCutoff.linear_eq_one hcdb (by linarith only [hr, hac, ha0])
  have hlipa : Ca.lip = Lp₀ := by
    rw [hCad, hLp₀]
    change 1 / (2 * a.1.1 - c / 2 - (2 * a.1.1 - c)) = _
    rw [show 2 * a.1.1 - c / 2 - (2 * a.1.1 - c) = c / 2 by ring]
    field_simp
  have hlipb : Cb.lip = Lp₀ := by
    rw [hCbd, hLp₀]
    change 1 / (2 * b.1.1 - c / 2 - (2 * b.1.1 - c)) = _
    rw [show 2 * b.1.1 - c / 2 - (2 * b.1.1 - c) = c / 2 by ring]
    field_simp
  -- The forcings are bounded.
  have hF₁ : ∀ᵐ y ∂volume, ‖((chartLocalizedForcing Ca a.1 U F : LogarithmicHalfLineL2) : RealLineL2) y‖ ≤ A₁ := by
    have := norm_chartLocalizedForcing_le Ca a.1 U F hAu0 hAu0 hFM hUL
    rw [hlipa] at this
    rw [hA₁d]
    exact this
  have hF₂ : ∀ᵐ y ∂volume, ‖((chartForcing Cb b ζ : LogarithmicHalfLineL2) : RealLineL2) y‖ ≤ A₂ := by
    have := chartForcing_sup_le Cb hb hCb ζ (M := Ab) (L := Ab) ((hAb b hba₁ hb).2.2.1)
      ((hAb b hba₁ hb).2.1)
    rw [hlipb] at this
    rw [hA₂d, hNd]
    exact this
  -- The energy across the collar.
  have hen := norm_collar_energy_le hab ζ U F hUE hsolve Ca Cb hCa hCb hshift hone B hBE
    (by rw [← hh, ← hτd]; exact hBv) hF₁ hF₂ hA₁0 hA₂0
  rw [← hh, ← hτd] at hen
  obtain ⟨p, hp⟩ : ∃ p : RealLineL2, p = logTranslationCLM (-(a.1.1 + τ)) (U : RealLineL2) := ⟨_, rfl⟩
  rw [← hp] at hen
  have hpE : HasLogarithmicEnergy p := by
    rw [hp]
    exact hasLogarithmicEnergy_translation _ hUE
  have hmultB : Cb.mult (B : RealLineL2) = (B : RealLineL2) := by
    apply Lp.ext
    filter_upwards [Cb.mult_coeFn (B : RealLineL2), hBv] with r h1 h2
    rw [h1, h2]
    by_cases hm : r ∈ Ico 0 τ
    · rw [indicator_of_mem hm, hone r (by
        have := hm.2
        rw [hτd, hh] at this
        exact this.le), Complex.ofReal_one, one_mul]
    · rw [indicator_of_notMem hm, mul_zero]
  have hid := Cb.form_identity hpE hBE
  rw [hmultB] at hid
  -- `p` is the translated source.
  have hpTu : p = logTranslationCLM (-b.1.1) (ccmArchimedeanFormEmbedding b.1 (toForm b Tu)) := by
    apply Lp.ext
    have ht := (measurePreserving_add_right (volume : Measure ℝ) (-b.1.1)).quasiMeasurePreserving.ae hTuae
    rw [hp]
    filter_upwards [logarithmicTranslation_coeFn (-(a.1.1 + τ)) (U : RealLineL2),
      logarithmicTranslation_coeFn (-b.1.1) (ccmArchimedeanFormEmbedding b.1 (toForm b Tu)), ht]
      with r h1 h2 h3
    rw [h1, h2, h3]
    congr 1
    rw [hτd, hh]
    ring
  have hTuE : HasLogarithmicEnergy (ccmArchimedeanFormEmbedding b.1 (toForm b Tu)) :=
    hasLogarithmicEnergy_ccm_form b.1 _
  have hformT : logarithmicFullForm (ccmArchimedeanFormEmbedding b.1 (toForm b Tu))
      (ccmArchimedeanFormEmbedding b.1 (toForm b bv)) = logarithmicFullForm p (B : RealLineL2) := by
    have := logarithmicFullForm_translation (-b.1.1) hTuE hJbE
    rw [← hpTu, ← hB] at this
    exact this.symm
  -- The commutator.
  have hpi : Integrable (p : ℝ → ℂ) := by
    have hv : (p : ℝ → ℂ) =ᵐ[volume] fun x => (U : RealLineL2) (x + -(a.1.1 + τ)) := by
      rw [hp]
      exact logarithmicTranslation_coeFn _ (U : RealLineL2)
    exact ((integrable_aperture a.1 U).comp_add_right _).congr hv.symm
  have hpL : ∫ x, ‖p x‖ ≤ Au := by
    refine le_trans (le_of_eq ?_) hUL
    rw [← integral_add_right_eq_self (fun x => ‖(U : RealLineL2) x‖) (-(a.1.1 + τ))]
    apply integral_congr_ae
    rw [hp]
    filter_upwards [logarithmicTranslation_coeFn (-(a.1.1 + τ)) (U : RealLineL2)] with x hx
    rw [hx]
  have hBint : Integrable ((B : RealLineL2) : ℝ → ℂ) := by
    have hv : ((B : RealLineL2) : ℝ → ℂ) =ᵐ[volume] fun x => (Jb : RealLineL2) (x + -b.1.1) := by
      rw [hB]
      exact logarithmicTranslation_coeFn _ (Jb : RealLineL2)
    exact ((integrable_aperture b.1 Jb).comp_add_right _).congr hv.symm
  have hBL : ∫ x, ‖(B : RealLineL2) x‖ ≤ τ * Ab := by
    refine le_trans (le_of_eq ?_) hJbL
    rw [← integral_add_right_eq_self (fun x => ‖(Jb : RealLineL2) x‖) (-b.1.1)]
    apply integral_congr_ae
    rw [hB]
    filter_upwards [logarithmicTranslation_coeFn (-b.1.1) (Jb : RealLineL2)] with x hx
    rw [hx]
  have hBLn : 0 ≤ ∫ x, ‖(B : RealLineL2) x‖ := integral_nonneg fun _ => norm_nonneg _
  have hcomm : ‖inner ℂ (B : RealLineL2) (Cb.comm.op p)‖ ≤ Lp₀ / 2 * Au * (τ * Ab) := by
    have hK : ∀ᵐ y ∂volume, ‖(Cb.comm.op p) y‖ ≤ Lp₀ / 2 * Au := by
      filter_upwards [Cb.comm.op_coeFn p] with y hk
      rw [hk]
      change ‖Cb.commutatorIntegral (p : ℝ → ℂ) y‖ ≤ _
      refine (Cb.norm_commutatorIntegral_le hpi y).trans ?_
      rw [hlipb]
      exact mul_le_mul_of_nonneg_left hpL (by positivity)
    rw [norm_inner_symm]
    refine (norm_inner_le_mul_integral hK hBint).trans ?_
    exact mul_le_mul_of_nonneg_left hBL (by positivity)
  have hEB : ‖logarithmicFullForm p (B : RealLineL2)‖ ≤ τ * (A₁ * A₂) + Lp₀ / 2 * Au * (τ * Ab) := by
    have hc := logarithmicFullForm_conj p (B : RealLineL2)
    rw [← hc, norm_star]
    have he : logarithmicFullForm (B : RealLineL2) p =
        logarithmicFullForm (B : RealLineL2) (Cb.mult p) - inner ℂ (B : RealLineL2) (Cb.comm.op p) := by
      rw [← hid]
      ring
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (by rw [hτd]; exact hen) hcomm)
  -- The bounded adjustment.
  have hadj : ‖inner ℂ ((logarithmicDirichletAdjustment b.1 - ccmRestrictedWeilBoundedRemainder b.1)
      (ccmArchimedeanFormToAperture b.1 (toForm b Tu))) Jb‖ ≤ K₃ * Au * (τ * Ab) := by
    refine (norm_inner_le_mul_integral hGb (integrable_aperture b.1 Jb)).trans ?_
    exact mul_le_mul_of_nonneg_left hJbL (by positivity)
  -- Assembly.
  have hinner := inner_source_eq_neg_collar hab ζ g wv bv hcut
  have hfull := inner_eq_full_sub b Tu bv
  have hIval : ((∫ x in Ico (-a.1.1) a.1.1, ‖chartIncrement a b z (a.1.1 - x)‖ : ℝ) : ℂ) =
      -(logarithmicFullForm p (B : RealLineL2) -
        inner ℂ ((logarithmicDirichletAdjustment b.1 - ccmRestrictedWeilBoundedRemainder b.1)
          (ccmArchimedeanFormToAperture b.1 (toForm b Tu))) Jb) := by
    rw [← hI, hinner, ← hTu, hfull, hformT, hJb]
  have hInn : 0 ≤ ∫ x in Ico (-a.1.1) a.1.1, ‖chartIncrement a b z (a.1.1 - x)‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have hIle : (∫ x in Ico (-a.1.1) a.1.1, ‖chartIncrement a b z (a.1.1 - x)‖) ≤
      τ * (A₁ * A₂) + Lp₀ / 2 * Au * (τ * Ab) + K₃ * Au * (τ * Ab) := by
    have hn := congrArg norm hIval
    rw [Complex.norm_real, Real.norm_of_nonneg hInn, norm_neg] at hn
    rw [hn]
    exact (norm_sub_le _ _).trans (add_le_add hEB hadj)
  have hsplit := integral_norm_chartIncrement_le_split hab z (M := Mz) (fun t => (hMz b hba₁ hb t).1)
  rw [← hh, ← hτd] at hsplit
  refine hsplit.trans ?_
  have hfinal : 2 * (A₁ * A₂ + Ab * (Lp₀ / 2 * Au) + Ab * (K₃ * Au) + Mz + Ab) * h =
      τ * (A₁ * A₂) + Lp₀ / 2 * Au * (τ * Ab) + K₃ * Au * (τ * Ab) + τ * Mz + τ * Ab := by
    rw [hτd]
    ring
  rw [← hh, hfinal]
  have hτAb : 0 ≤ τ * Ab := mul_nonneg hτ0 hAb0
  linarith only [hIle, hτAb]

end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
