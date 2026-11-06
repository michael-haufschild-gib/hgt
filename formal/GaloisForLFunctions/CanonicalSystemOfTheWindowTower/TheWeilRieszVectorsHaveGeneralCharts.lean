import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheRenewalReadoutHasAnExplicitModulus
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.ReflectionExchangesTheWeilEndpointTraces
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.ThePrimeAndPolarWeilResponsesAreContinuous

/-!
# General half-line charts of the actual Weil Riesz vectors

In the left-endpoint coordinate `s(t) = U_a(t − a)` the actual Riesz source vanishes off `[0,2a]`.
For any bounded Lipschitz cutoff `χ` vanishing on `[2a,∞)`, the product `χ s` is the half-line Green
solution of

`F(y) = χ(y)(e^{−i z̄ (y−a)} + κ s(y) + B s(y) + Σ_n w_n (s(y+log n) + s(y−log n))) + 𝒦_χ s(y)`,

where `B` collects the bounded convolution and both polar terms, and `𝒦_χ` is the cutoff commutator.
If `χ = 1` near zero, `∫ v F` is the left endpoint trace. The formula is translation invariant in
`y`, so the forcings of two apertures can be compared term by term.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

/-- A continuous bounded Lipschitz cutoff. -/
structure ChartCutoff where
  toFun : ℝ → ℝ
  continuous' : Continuous toFun
  abs_le : ∀ x, |toFun x| ≤ 1
  lip : ℝ
  lip_nonneg : 0 ≤ lip
  lipschitz : ∀ x y, |toFun x - toFun y| ≤ lip * |x - y|

namespace ChartCutoff

variable (C : ChartCutoff)

/-- Multiplication by the cutoff. -/
def mult : RealLineL2 →L[ℂ] RealLineL2 :=
  logarithmicCutoffMultiplier C.continuous'.measurable zero_le_one C.abs_le

/-- The commutator of the logarithmic form with the cutoff. -/
def comm : SchurKernel (volume : Measure ℝ) :=
  logarithmicCutoffSchurKernel C.continuous'.measurable C.lip_nonneg C.lipschitz

theorem mult_coeFn (f : RealLineL2) :
    (C.mult f : ℝ → ℂ) =ᵐ[volume] fun x => (C.toFun x : ℂ) * f x :=
  logarithmicCutoffMultiplier_coeFn _ _ _ f

theorem hasLogarithmicEnergy_mult {w : RealLineL2} (hw : HasLogarithmicEnergy w) :
    HasLogarithmicEnergy (C.mult w) :=
  hasLogarithmicEnergy_cutoff C.continuous'.measurable zero_le_one C.abs_le C.lip_nonneg
    C.lipschitz hw

theorem form_identity {u w : RealLineL2} (hu : HasLogarithmicEnergy u)
    (hw : HasLogarithmicEnergy w) :
    logarithmicFullForm w (C.mult u) - logarithmicFullForm (C.mult w) u =
      inner ℂ w (C.comm.op u) :=
  logarithmicFullForm_cutoff_identity C.continuous'.measurable zero_le_one C.abs_le C.lip_nonneg
    C.lipschitz hu hw

theorem inner_mult (f g : RealLineL2) : inner ℂ (C.mult f) g = inner ℂ f (C.mult g) :=
  inner_logarithmicCutoffMultiplier _ _ _ f g

theorem mult_mem_halfLine {f : RealLineL2} (hf : f ∈ halfLineL2) : C.mult f ∈ halfLineL2 := by
  rw [mem_halfLineL2_iff]
  filter_upwards [C.mult_coeFn f, (mem_halfLineL2_iff f).mp hf] with x hx hfz
  intro hneg
  rw [hx, hfz hneg, mul_zero]

/-- The literal commutator integral of a physical function. -/
def commutatorIntegral (S : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ t : ℝ, logarithmicCutoffKernel C.toFun y t * S t

end ChartCutoff

/-- The mass coefficient of the literal forcing. -/
def chartMass : ℂ := -(logarithmicFormScalar : ℂ) - ccmArchimedeanRemainderScalar

/-- The bounded convolution and the two polar terms of the forcing. -/
def chartBounded (S : ℝ → ℂ) (y : ℝ) : ℂ :=
  (∫ t : ℝ, (archLogRemainder |y - t| : ℂ) * S t) -
    ((Real.exp ((1 / 2) * y) : ℂ) * (∫ t : ℝ, (Real.exp ((-1 / 2) * t) : ℂ) * S t) +
      (Real.exp ((-1 / 2) * y) : ℂ) * ∫ t : ℝ, (Real.exp ((1 / 2) * t) : ℂ) * S t)

/-- The prime translations of the forcing, over a finite set of prime powers. -/
def chartPrime (N : Finset ℕ) (S : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∑ n ∈ N, (criticalMellinAtomWeight n : ℂ) * (S (y + Real.log n) + S (y - Real.log n))

private theorem aperture_zero (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ∀ᵐ x ∂volume, x ∉ centralInterval a.1 → (f : RealLineL2) x = 0 := by
  have hc := indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) f.1
  rw [indicatorCutoff_suzukiApertureHilbert] at hc
  filter_upwards [hc] with x hx hn
  rw [hx, indicator_of_notMem hn]

private theorem translated_mem_halfLine (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) : logTranslationCLM (-a.1) (f : RealLineL2) ∈ halfLineL2 := by
  rw [mem_halfLineL2_iff]
  have hs := (MellinL2.realTranslation_measurePreserving (-a.1)).quasiMeasurePreserving.ae
    (aperture_zero a f)
  filter_upwards [logarithmicTranslation_coeFn (-a.1) (f : RealLineL2), hs] with x hx hsx
  intro hneg
  rw [hx]
  change (f : RealLineL2) (x + -a.1) = 0
  apply hsx
  change ¬(-a.1 ≤ x + -a.1 ∧ x + -a.1 ≤ a.1)
  intro h
  linarith only [h.1, hneg]

private theorem cutoff_translated_mem (C : ChartCutoff) (a : SuzukiPositiveAperture)
    (hC : ∀ x, 2 * a.1 ≤ x → C.toFun x = 0) (w : LogarithmicHalfLineL2) :
    logTranslationCLM a.1 (C.mult w) ∈ suzukiApertureHilbert a := by
  let f := logTranslationCLM a.1 (C.mult w)
  have hP := (C.mult_coeFn (w : RealLineL2)).comp_tendsto
    (MellinL2.realTranslation_measurePreserving a.1).quasiMeasurePreserving.tendsto_ae
  have hw := (MellinL2.realTranslation_measurePreserving a.1).quasiMeasurePreserving.ae
    ((mem_halfLineL2_iff (w : RealLineL2)).mp w.property)
  have hzero : ∀ᵐ x ∂volume, x ∉ centralInterval a.1 → f x = 0 := by
    filter_upwards [logarithmicTranslation_coeFn a.1 (C.mult w), hP, hw] with x hx hPx hwx
    intro hout
    change (C.mult w) (x + a.1) = (C.toFun (x + a.1) : ℂ) * (w : RealLineL2) (x + a.1) at hPx
    change logTranslationCLM a.1 (C.mult w) x = 0
    rw [hx, hPx]
    change x + a.1 < 0 → (w : RealLineL2) (x + a.1) = 0 at hwx
    by_cases hleft : x < -a.1
    · rw [hwx (by linarith only [hleft]), mul_zero]
    · have hright : a.1 < x := by
        by_contra! h
        exact hout ⟨le_of_not_gt hleft, h⟩
      rw [hC _ (by linarith only [hright]), Complex.ofReal_zero, zero_mul]
  change ∃ g : RealLineL2, indicatorCutoff (centralInterval a.1)
    (measurableSet_centralInterval a.1) g = logTranslationCLM a.1 (C.mult w)
  refine ⟨f, ?_⟩
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) f,
    hzero] with x hx hfx
  rw [hx]
  by_cases hmem : x ∈ centralInterval a.1
  · rw [indicator_of_mem hmem]
  · rw [indicator_of_notMem hmem, hfx hmem]

private theorem translation_cancel (a : ℝ) (f : RealLineL2) :
    logTranslationCLM a (logTranslationCLM (-a) f) = f := by
  have h : logTranslationCLM (-(-a)) (logTranslationCLM (-a) f) = f :=
    congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T f) (logTranslationCLM_neg_mul (-a))
  simpa only [neg_neg] using h

/-- The cutoff, translated source on the half-line. -/
def chartLocalized (C : ChartCutoff) (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    LogarithmicHalfLineL2 :=
  ⟨C.mult (logTranslationCLM (-a.1) f), C.mult_mem_halfLine (translated_mem_halfLine a f)⟩

/-- The full forcing of the chart equation. -/
def chartLocalizedForcing (C : ChartCutoff) (a : SuzukiPositiveAperture)
    (u g : suzukiApertureHilbert a) : LogarithmicHalfLineL2 :=
  logarithmicHalfLineRestriction
    (C.mult (logTranslationCLM (-a.1) (g : RealLineL2)) +
      C.comm.op (logTranslationCLM (-a.1) (u : RealLineL2)))

/-- **The chart equation**: a cutoff vanishing past the far endpoint turns the interval equation into
the half-line equation with its literal commutator. -/
theorem chartLocalized_solves (C : ChartCutoff) (a : SuzukiPositiveAperture)
    (hC : ∀ x, 2 * a.1 ≤ x → C.toFun x = 0) (u g : suzukiApertureHilbert a)
    (hu : HasLogarithmicEnergy (u : RealLineL2))
    (hsolve : ∀ f : suzukiApertureHilbert a, HasLogarithmicEnergy (f : RealLineL2) →
      logarithmicFullForm (f : RealLineL2) (u : RealLineL2) =
        inner ℂ (f : RealLineL2) (g : RealLineL2)) :
    HasLogarithmicEnergy (chartLocalized C a u : RealLineL2) ∧
    ∀ w : LogarithmicHalfLineL2, HasLogarithmicEnergy (w : RealLineL2) →
      logarithmicHalfLineForm w (chartLocalized C a u) =
        inner ℂ w (chartLocalizedForcing C a u g) := by
  let s : RealLineL2 := logTranslationCLM (-a.1) (u : RealLineL2)
  have hs : HasLogarithmicEnergy s := hasLogarithmicEnergy_translation (-a.1) hu
  refine ⟨C.hasLogarithmicEnergy_mult hs, fun w hw => ?_⟩
  have hPw := C.hasLogarithmicEnergy_mult hw
  let f : suzukiApertureHilbert a :=
    ⟨logTranslationCLM a.1 (C.mult w), cutoff_translated_mem C a hC w⟩
  have hf : HasLogarithmicEnergy (f : RealLineL2) := hasLogarithmicEnergy_translation a.1 hPw
  have he := hsolve f hf
  have hshift := logarithmicFullForm_translation a.1 hPw hs
  have hcancel : logTranslationCLM a.1 s = (u : RealLineL2) := translation_cancel _ _
  rw [hcancel] at hshift
  have hmid : logarithmicFullForm (C.mult w) s =
      inner ℂ (w : RealLineL2) (C.mult (logTranslationCLM (-a.1) (g : RealLineL2))) := by
    calc
      _ = logarithmicFullForm (logTranslationCLM a.1 (C.mult w)) (u : RealLineL2) := hshift.symm
      _ = inner ℂ (logTranslationCLM a.1 (C.mult w)) (g : RealLineL2) := he
      _ = inner ℂ (C.mult w) (logTranslationCLM (-a.1) (g : RealLineL2)) :=
        inner_logTranslationCLM _ _ _
      _ = _ := C.inner_mult _ _
  have hcomm := C.form_identity hs hw
  change logarithmicFullForm (w : RealLineL2) (C.mult s) =
    inner ℂ w (logarithmicHalfLineRestriction
      (C.mult (logTranslationCLM (-a.1) (g : RealLineL2)) + C.comm.op s))
  rw [inner_logarithmicHalfLineRestriction, inner_add_right]
  calc
    _ = inner ℂ (w : RealLineL2) (C.comm.op s) + logarithmicFullForm (C.mult w) s :=
      sub_eq_iff_eq_add.mp hcomm
    _ = _ := by rw [hmid, add_comm]

namespace WeilHilbertBeforeContact

/-- The physical source in the left-endpoint coordinate. -/
def chartSource (a : PrecontactAperture) (z : ℂ) (t : ℝ) : ℂ :=
  evalVectorContinuousRepresentative a z (t - a.1.1)

theorem continuous_chartSource (a : PrecontactAperture) (z : ℂ) :
    Continuous (chartSource a z) :=
  (continuous_evalVectorContinuousRepresentative a z).comp (by fun_prop)

theorem chartSource_eq_zero (a : PrecontactAperture) (z : ℂ) {t : ℝ}
    (ht : t ≤ 0 ∨ 2 * a.1.1 ≤ t) : chartSource a z t = 0 := by
  apply evalVectorContinuousRepresentative_eq_zero
  rcases ht with h | h
  · exact Or.inl (by linarith only [h])
  · exact Or.inr (by linarith only [h])

/-- The physical source of the actual Riesz vector, as an aperture vector. -/
def chartPhysical (a : PrecontactAperture) (z : ℂ) : suzukiApertureHilbert a.1 :=
  ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z))

theorem chartPhysical_ae (a : PrecontactAperture) (z : ℂ) :
    ((chartPhysical a z : suzukiApertureHilbert a.1) : ℝ → ℂ) =ᵐ[volume]
      evalVectorContinuousRepresentative a z := by
  have h : ((chartPhysical a z : suzukiApertureHilbert a.1) : RealLineL2) =
      ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)) :=
    ccmArchimedeanFormToAperture_coe a.1 _
  rw [h]
  exact (evalVectorContinuousRepresentative_ae a z).symm

/-- The translate of the physical source is the chart source almost everywhere. -/
theorem translated_chartPhysical_ae (a : PrecontactAperture) (z : ℂ) :
    (logTranslationCLM (-a.1.1) ((chartPhysical a z : suzukiApertureHilbert a.1) : RealLineL2) :
      ℝ → ℂ) =ᵐ[volume] chartSource a z := by
  have ht := (chartPhysical_ae a z).comp_tendsto
    (MellinL2.realTranslation_measurePreserving (-a.1.1)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [logarithmicTranslation_coeFn (-a.1.1)
    ((chartPhysical a z : suzukiApertureHilbert a.1) : RealLineL2), ht] with t hl hr
  rw [hl]
  exact hr

/-- The forcing of the chart at the actual Riesz vector. -/
def chartForcing (C : ChartCutoff) (a : PrecontactAperture) (z : ℂ) : LogarithmicHalfLineL2 :=
  chartLocalizedForcing C a.1 (chartPhysical a z) (logarithmicForcing a z)

/-- The chart forcing is essentially bounded. -/
theorem chartForcing_bounded (C : ChartCutoff) (a : PrecontactAperture) (z : ℂ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ y ∂volume, ‖(chartForcing C a z : RealLineL2) y‖ ≤ A := by
  obtain ⟨Cu, hCu, hu⟩ := evalVector_physical_essentially_bounded a z
  obtain ⟨Cg, hCg, hg⟩ := evalVector_logarithmicForcing_bounded a z
  refine ⟨Cg + C.lip * Cu, add_nonneg hCg (mul_nonneg C.lip_nonneg hCu), ?_⟩
  apply logarithmicHalfLineRestriction_bounded _
    (add_nonneg hCg (mul_nonneg C.lip_nonneg hCu))
  have hut := (MellinL2.realTranslation_measurePreserving (-a.1.1)).quasiMeasurePreserving.ae hu
  have hgt := (MellinL2.realTranslation_measurePreserving (-a.1.1)).quasiMeasurePreserving.ae hg
  have hK := logarithmicCutoffSchurKernel_preserves_boundedness C.continuous'.measurable
    C.lip_nonneg C.lipschitz (logTranslationCLM (-a.1.1)
      ((chartPhysical a z : suzukiApertureHilbert a.1) : RealLineL2)) (C := Cu) (by
      filter_upwards [logarithmicTranslation_coeFn (-a.1.1)
        ((chartPhysical a z : suzukiApertureHilbert a.1) : RealLineL2), hut] with t ht hb
      rw [ht]
      exact hb)
  filter_upwards [Lp.coeFn_add
    (C.mult (logTranslationCLM (-a.1.1) (logarithmicForcing a z : RealLineL2)))
    (C.comm.op (logTranslationCLM (-a.1.1)
      ((chartPhysical a z : suzukiApertureHilbert a.1) : RealLineL2))),
    C.mult_coeFn (logTranslationCLM (-a.1.1) (logarithmicForcing a z : RealLineL2)),
    logarithmicTranslation_coeFn (-a.1.1) (logarithmicForcing a z : RealLineL2), hgt, hK]
    with y hadd hm ht hg hk
  rw [hadd, Pi.add_apply]
  refine (norm_add_le _ _).trans (add_le_add ?_ hk)
  rw [hm, ht, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ 1 * Cg := mul_le_mul (C.abs_le y) hg (norm_nonneg _) zero_le_one
    _ = Cg := one_mul _

/-- **The Green representation in a general chart**, at every point. -/
theorem logarithmicGreenRepresentative_chartForcing (C : ChartCutoff) (a : PrecontactAperture)
    (hC : ∀ x, 2 * a.1.1 ≤ x → C.toFun x = 0) (z : ℂ) (t : ℝ) :
    logarithmicGreenRepresentative (chartForcing C a z) t =
      (C.toFun t : ℂ) * chartSource a z t := by
  obtain ⟨A, hA, hb⟩ := chartForcing_bounded C a z
  have hsol := chartLocalized_solves C a.1 hC (chartPhysical a z) (logarithmicForcing a z)
    (hasLogarithmicEnergy_ccm_form a.1 _) (fun f hf => evalVector_logarithmic_fullForm a z f hf)
  have hu := logarithmicHalfLineGreenOperator_unique _ _ hsol.1 hsol.2
  have hG := logarithmicHalfLineGreenOperator_eq_representative (chartForcing C a z)
  change ((logarithmicHalfLineGreenOperator (chartLocalizedForcing C a.1 (chartPhysical a z)
    (logarithmicForcing a z)) : RealLineL2) : ℝ → ℂ) =ᵐ[volume] _ at hG
  rw [← hu] at hG
  have hae : logarithmicGreenRepresentative (chartForcing C a z) =ᵐ[volume]
      fun t => (C.toFun t : ℂ) * chartSource a z t := by
    filter_upwards [hG, C.mult_coeFn (logTranslationCLM (-a.1.1)
      ((chartPhysical a z : suzukiApertureHilbert a.1) : RealLineL2)),
      translated_chartPhysical_ae a z] with t h1 h2 h3
    rw [← h1]
    change C.mult (logTranslationCLM (-a.1.1)
      ((chartPhysical a z : suzukiApertureHilbert a.1) : RealLineL2)) t = _
    rw [h2, h3]
  have hcont : Continuous (fun t => (C.toFun t : ℂ) * chartSource a z t) :=
    (Complex.continuous_ofReal.comp C.continuous').mul (continuous_chartSource a z)
  exact congrFun ((Continuous.ae_eq_iff_eq volume
    (continuous_logarithmicGreenRepresentative _ hA hb) hcont).mp hae) t

/-- **The chart reads the left endpoint trace.** -/
theorem logarithmicBackwardConvolution_chartForcing_zero (C : ChartCutoff)
    (a : PrecontactAperture) (hC : ∀ x, 2 * a.1.1 ≤ x → C.toFun x = 0) {c : ℝ} (hc : 0 < c)
    (hone : ∀ x, x ≤ c → C.toFun x = 1) (z : ℂ) :
    logarithmicBackwardConvolution (chartForcing C a z : RealLineL2) 0 =
      evalVectorLeftTrace a z := by
  obtain ⟨A, hA, hb⟩ := chartForcing_bounded C a z
  have hl := logarithmicHalfLineGreenOperator_normalized_boundary_limit (chartForcing C a z)
    (δ := 1) (by norm_num) hA (hb.mono fun _ hy _ => hy)
  have hr := evalVectorContinuousRepresentative_left_normalized_limit a z
  have he : (fun t : ℝ => logarithmicGreenRepresentative (chartForcing C a z) t *
      (Real.sqrt (Real.log (1 / t)) : ℂ)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun t => evalVectorContinuousRepresentative a z (t - a.1.1) *
        (Real.sqrt (Real.log (1 / t)) : ℂ) := by
    filter_upwards [(eventually_lt_nhds hc).filter_mono nhdsWithin_le_nhds] with t ht
    rw [logarithmicGreenRepresentative_chartForcing C a hC, hone t ht.le, Complex.ofReal_one,
      one_mul]
    rfl
  have hlim := tendsto_nhds_unique (hl.congr' he) hr
  simpa only [logarithmicBackwardConvolution, sub_zero] using hlim

private theorem inner_polar_chartPhysical (a : PrecontactAperture) (z : ℂ) (σ : ℝ) :
    inner ℂ (ccmPolarApertureVector a.1 σ) (chartPhysical a z) =
      ∫ x : ℝ, (Real.exp (σ * x) : ℂ) * evalVectorContinuousRepresentative a z x := by
  change inner ℂ (ccmPolarL2Vector a.1 σ : SoninL2)
    ((chartPhysical a z : suzukiApertureHilbert a.1) : SoninL2) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ccmPolarL2Vector_coeFn a.1 σ, chartPhysical_ae a z] with x hp hu
  rw [hp, hu]
  by_cases hx : x ∈ centralInterval a.1.1
  · rw [indicator_of_mem hx]
    simp only [RCLike.inner_apply, ccmPolarProfile, Complex.conj_ofReal]
    ring
  · rw [indicator_of_notMem hx]
    have hzero : evalVectorContinuousRepresentative a z x = 0 := by
      apply evalVectorContinuousRepresentative_eq_zero
      have hs : ¬(-a.1.1 ≤ x ∧ x ≤ a.1.1) := hx
      rcases not_and_or.mp hs with h | h
      · exact Or.inl (lt_of_not_ge h).le
      · exact Or.inr (lt_of_not_ge h).le
    simp only [hzero, inner_zero_right, mul_zero]

private theorem moment_shift (a : PrecontactAperture) (z : ℂ) (σ : ℝ) :
    (∫ x : ℝ, (Real.exp (σ * x) : ℂ) * evalVectorContinuousRepresentative a z x) =
      (Real.exp (-(σ * a.1.1)) : ℂ) * ∫ t : ℝ, (Real.exp (σ * t) : ℂ) * chartSource a z t := by
  rw [← integral_sub_right_eq_self
    (fun x : ℝ => (Real.exp (σ * x) : ℂ) * evalVectorContinuousRepresentative a z x) a.1.1,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  have he : Real.exp (σ * (t - a.1.1)) = Real.exp (-(σ * a.1.1)) * Real.exp (σ * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  push_cast
  rw [chartSource]
  ring

private theorem convolution_shift (a : PrecontactAperture) (z : ℂ) (y : ℝ) :
    (∫ t : ℝ, (archLogRemainder |(y - a.1.1) - t| : ℂ) * evalVectorContinuousRepresentative a z t) =
      ∫ t : ℝ, (archLogRemainder |y - t| : ℂ) * chartSource a z t := by
  rw [← integral_sub_right_eq_self
    (fun t : ℝ => (archLogRemainder |(y - a.1.1) - t| : ℂ) *
      evalVectorContinuousRepresentative a z t) a.1.1]
  apply integral_congr_ae
  filter_upwards with t
  rw [show (y - a.1.1) - (t - a.1.1) = y - t by ring]
  rfl

/-- The literal value of the logarithmic forcing on the aperture. -/
theorem logarithmicForcing_ae (a : PrecontactAperture) (z : ℂ) :
    ∀ᵐ x ∂volume, x ∈ Icc (-a.1.1) a.1.1 →
      ((logarithmicForcing a z : suzukiApertureHilbert a.1) : ℝ → ℂ) x =
        Complex.exp (-I * star z * (x : ℂ)) +
          ((-(logarithmicFormScalar : ℂ)) * evalVectorContinuousRepresentative a z x +
            ∫ t : ℝ, (archLogRemainder |x - t| : ℂ) * evalVectorContinuousRepresentative a z t) -
          continuousWeilRemainderProfile a.1 (chartPhysical a z)
            (evalVectorContinuousRepresentative a z) x := by
  let u := chartPhysical a z
  have hval : ((logarithmicForcing a z : suzukiApertureHilbert a.1) : SoninL2) =
      (evaluationForcing a.1 z : SoninL2) +
        (((-(logarithmicFormScalar : ℂ)) • (u : SoninL2) +
          (ccmApertureCompression a.1 archLogConvolution u : SoninL2)) -
          (ccmRestrictedWeilBoundedRemainder a.1 u : SoninL2)) := rfl
  change ∀ᵐ x ∂volume, x ∈ Icc (-a.1.1) a.1.1 →
    ((logarithmicForcing a z : suzukiApertureHilbert a.1) : SoninL2) x = _
  rw [hval]
  have hrem := (ae_restrict_iff' (measurableSet_centralInterval a.1.1)).mp
    (continuousWeilRemainderProfile_ae a.1 u (evalVectorContinuousRepresentative a z)
      (chartPhysical_ae a z).symm)
  rw [ccmApertureCompression_val]
  filter_upwards [Lp.coeFn_add (evaluationForcing a.1 z : SoninL2)
      (((-(logarithmicFormScalar : ℂ)) • (u : SoninL2) +
        indicatorCutoff (centralInterval a.1.1) (measurableSet_centralInterval a.1.1)
          (archLogConvolution (u : SoninL2))) -
        (ccmRestrictedWeilBoundedRemainder a.1 u : SoninL2)),
    Lp.coeFn_sub ((-(logarithmicFormScalar : ℂ)) • (u : SoninL2) +
        indicatorCutoff (centralInterval a.1.1) (measurableSet_centralInterval a.1.1)
          (archLogConvolution (u : SoninL2)))
      (ccmRestrictedWeilBoundedRemainder a.1 u : SoninL2),
    Lp.coeFn_add ((-(logarithmicFormScalar : ℂ)) • (u : SoninL2))
      (indicatorCutoff (centralInterval a.1.1) (measurableSet_centralInterval a.1.1)
        (archLogConvolution (u : SoninL2))),
    Lp.coeFn_smul (-(logarithmicFormScalar : ℂ)) (u : SoninL2),
    evaluationForcing_coeFn a.1 z,
    indicatorCutoff_ae (centralInterval a.1.1) (measurableSet_centralInterval a.1.1)
      (archLogConvolution (u : SoninL2)),
    archLogConvolution_coeFn (u : SoninL2), chartPhysical_ae a z, hrem]
    with x h1 h2 h3 h4 he hc hconv hu hr hx
  have hcentral : x ∈ centralInterval a.1.1 := hx
  rw [h1, Pi.add_apply, h2, Pi.sub_apply, h3, Pi.add_apply, h4, Pi.smul_apply, smul_eq_mul, he, hc,
    indicator_of_mem hx, indicator_of_mem hcentral, hconv, hu]
  have hint : (∫ y : ℝ, (archLogRemainder |x - y| : ℂ) * (u : SoninL2) y) =
      ∫ t : ℝ, (archLogRemainder |x - t| : ℂ) * evalVectorContinuousRepresentative a z t := by
    apply integral_congr_ae
    filter_upwards [chartPhysical_ae a z] with y hy
    rw [show (u : SoninL2) y = _ from hy]
  rw [hint, hr hcentral]

/-- **The literal forcing formula.** On the positive half-line the chart forcing is the cutoff times
the exponential, mass, bounded and prime terms, plus the commutator. `N` may be any finite set
containing the prime powers of the window whose other elements lie beyond it. -/
theorem chartForcing_ae (C : ChartCutoff) (a : PrecontactAperture)
    (hC : ∀ x, 2 * a.1.1 ≤ x → C.toFun x = 0) (z : ℂ) {N : Finset ℕ}
    (hN : Finset.Icc 2 ⌊Real.exp (2 * a.1.1)⌋₊ ⊆ N)
    (hN' : ∀ n ∈ N, n ∉ Finset.Icc 2 ⌊Real.exp (2 * a.1.1)⌋₊ → 2 * a.1.1 ≤ Real.log n) :
    ∀ᵐ y ∂volume, 0 ≤ y → ((chartForcing C a z : LogarithmicHalfLineL2) : RealLineL2) y =
      (C.toFun y : ℂ) * (Complex.exp (-I * star z * ((y - a.1.1 : ℝ) : ℂ)) +
        chartMass * chartSource a z y + chartBounded (chartSource a z) y +
        chartPrime N (chartSource a z) y) +
      C.commutatorIntegral (chartSource a z) y := by
  let u := chartPhysical a z
  let g := logarithmicForcing a z
  let τg := logTranslationCLM (-a.1.1) (g : RealLineL2)
  let τu := logTranslationCLM (-a.1.1) (u : RealLineL2)
  have hgt := (MellinL2.realTranslation_measurePreserving (-a.1.1)).quasiMeasurePreserving.ae
    (logarithmicForcing_ae a z)
  have hu0 : τu =ᵐ[volume] chartSource a z := translated_chartPhysical_ae a z
  filter_upwards [indicatorCutoff_ae (Ici (0 : ℝ)) measurableSet_Ici (C.mult τg + C.comm.op τu),
    Lp.coeFn_add (C.mult τg) (C.comm.op τu), C.mult_coeFn τg,
    logarithmicTranslation_coeFn (-a.1.1) (g : RealLineL2), C.comm.op_coeFn τu, hgt]
    with y hi hadd hm ht hk hg hy
  change (indicatorCutoff (Ici (0 : ℝ)) measurableSet_Ici (C.mult τg + C.comm.op τu)) y = _
  rw [hi, indicator_of_mem (show y ∈ Ici (0 : ℝ) from hy), hadd, Pi.add_apply, hm, hk]
  have hcomm : (∫ t : ℝ, C.comm.toFun y t * τu t) = C.commutatorIntegral (chartSource a z) y := by
    apply integral_congr_ae
    filter_upwards [hu0] with t ht
    rw [ht]
    rfl
  rw [hcomm]
  congr 1
  by_cases hya : y < 2 * a.1.1
  swap
  · rw [hC y (not_lt.mp hya)]
    simp
  congr 1
  rw [show τg y = (g : RealLineL2) (y + -a.1.1) from ht]
  have hx : y + -a.1.1 ∈ Icc (-a.1.1) a.1.1 :=
    ⟨by linarith only [hy], by linarith only [hya]⟩
  change y + -a.1.1 ∈ Icc (-a.1.1) a.1.1 → ((g : suzukiApertureHilbert a.1) : ℝ → ℂ) (y + -a.1.1) = _
    at hg
  rw [show (g : RealLineL2) (y + -a.1.1) = ((g : suzukiApertureHilbert a.1) : ℝ → ℂ) (y + -a.1.1)
    from rfl, hg hx, continuousWeilRemainderProfile]
  rw [← sub_eq_add_neg y a.1.1]
  -- The polar moments in the left-endpoint coordinate.
  have hm1 : inner ℂ (ccmPolarApertureVector a.1 (-1 / 2)) u =
      (Real.exp (-((-1 / 2) * a.1.1)) : ℂ) *
        ∫ t : ℝ, (Real.exp ((-1 / 2) * t) : ℂ) * chartSource a z t := by
    rw [inner_polar_chartPhysical, moment_shift]
  have hm2 : inner ℂ (ccmPolarApertureVector a.1 (1 / 2)) u =
      (Real.exp (-((1 / 2) * a.1.1)) : ℂ) *
        ∫ t : ℝ, (Real.exp ((1 / 2) * t) : ℂ) * chartSource a z t := by
    rw [inner_polar_chartPhysical, moment_shift]
  change _ = _ + _ * evalVectorContinuousRepresentative a z (y - a.1.1) + _ + _
  rw [show inner ℂ (ccmPolarApertureVector a.1 (-1 / 2)) (chartPhysical a z) = _ from hm1,
    show inner ℂ (ccmPolarApertureVector a.1 (1 / 2)) (chartPhysical a z) = _ from hm2,
    convolution_shift]
  have he1 : (Real.exp (-((-1 / 2) * a.1.1)) : ℂ) * ccmPolarProfile (1 / 2) (y - a.1.1) =
      (Real.exp ((1 / 2) * y) : ℂ) := by
    rw [ccmPolarProfile, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have he2 : (Real.exp (-((1 / 2) * a.1.1)) : ℂ) * ccmPolarProfile (-1 / 2) (y - a.1.1) =
      (Real.exp ((-1 / 2) * y) : ℂ) := by
    rw [ccmPolarProfile, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  -- The prime terms over the enlarged set.
  have hprime : (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1.1)⌋₊, (criticalMellinAtomWeight n : ℂ) *
      (evalVectorContinuousRepresentative a z (y - a.1.1 + Real.log n) +
        evalVectorContinuousRepresentative a z (y - a.1.1 - Real.log n))) =
      chartPrime N (chartSource a z) y := by
    rw [chartPrime, ← Finset.sum_subset hN]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [chartSource, chartSource, show y + Real.log n - a.1.1 = y - a.1.1 + Real.log n by ring,
        show y - Real.log n - a.1.1 = y - a.1.1 - Real.log n by ring]
    · intro n hn hn'
      have hl := hN' n hn hn'
      rw [chartSource_eq_zero a z (Or.inr (by linarith only [hl, hy])),
        chartSource_eq_zero a z (Or.inl (by linarith only [hl, hya]))]
      ring
  rw [hprime, chartBounded, chartMass]
  simp only [chartSource]
  linear_combination (-(∫ t : ℝ, (Real.exp ((-1 / 2) * t) : ℂ) *
      evalVectorContinuousRepresentative a z (t - a.1.1))) * he1 -
    (∫ t : ℝ, (Real.exp ((1 / 2) * t) : ℂ) *
      evalVectorContinuousRepresentative a z (t - a.1.1)) * he2

end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
