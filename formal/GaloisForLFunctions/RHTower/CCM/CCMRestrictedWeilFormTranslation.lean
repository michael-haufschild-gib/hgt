import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarConstrainedRightContinuity
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadQuantileGammaChiSquareProducer
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier

/-!
# Translation of the full constrained Weil form domain

Physical translation is unimodular multiplication in the exact weighted Fourier space.
It preserves the archimedean form norm, transports compact aperture support, and preserves
the literal constrained source quadratic when the translated aperture fits.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct FourierTransform

noncomputable section
namespace RHTower

/-- Physical translation acting on the exact weighted Fourier space. -/
def ccmArchimedeanPhaseMul (h : ℝ) :
    CCMArchimedeanFourierL2 →L[ℂ] CCMArchimedeanFourierL2 :=
  lpBoundedMulCLM (MellinL2.fourierPhase_continuous h).measurable zero_le_one
    (fun x => (MellinL2.norm_fourierPhase h x).le)

theorem ccmArchimedeanPhaseMul_coeFn (h : ℝ) (u : CCMArchimedeanFourierL2) :
    (ccmArchimedeanPhaseMul h u : ℝ → ℂ) =ᵐ[ccmArchimedeanFormMeasure]
      fun x => MellinL2.fourierPhase h x * u x :=
  lpBoundedMulCLM_coeFn _ _ _ _

theorem norm_ccmArchimedeanPhaseMul (h : ℝ) (u : CCMArchimedeanFourierL2) :
    ‖ccmArchimedeanPhaseMul h u‖ = ‖u‖ := by
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (ccmArchimedeanPhaseMul_coeFn h u)]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards with x
  simp only [norm_mul, MellinL2.norm_fourierPhase, one_mul]

theorem ccmArchimedeanWeightedToL2_phaseMul (h : ℝ) (u : CCMArchimedeanFourierL2) :
    ccmArchimedeanWeightedToL2 (ccmArchimedeanPhaseMul h u) =
      MellinL2.fourierPhaseMulUnitary h (ccmArchimedeanWeightedToL2 u) := by
  apply Lp.ext
  have hphase := (ccmArchimedeanPhaseMul_coeFn h u).filter_mono
    (ae_mono volume_le_ccmArchimedeanFormMeasure)
  filter_upwards [ccmArchimedeanWeightedToL2_coeFn (ccmArchimedeanPhaseMul h u),
    ccmArchimedeanWeightedToL2_coeFn u, hphase,
    MellinL2.fourierPhaseMulAux_ae h (ccmArchimedeanWeightedToL2 u)] with x h1 h2 h3 h4
  change ccmArchimedeanWeightedToL2 (ccmArchimedeanPhaseMul h u) x =
    MellinL2.fourierPhaseMulAux h (ccmArchimedeanWeightedToL2 u) x
  rw [h1, h3, h4, h2]

theorem ccmArchimedeanFourierToTime_phaseMul (h : ℝ) (u : CCMArchimedeanFourierL2) :
    ccmArchimedeanFourierToTime (ccmArchimedeanPhaseMul h u) =
      logTranslationCLM h (ccmArchimedeanFourierToTime u) := by
  apply fourierUnitary.injective
  rw [fourierUnitary_ccmArchimedeanFourierToTime, ccmArchimedeanWeightedToL2_phaseMul]
  change _ = fourierUnitary
    (MellinL2.additiveTranslationUnitary h (ccmArchimedeanFourierToTime u))
  rw [show fourierUnitary (MellinL2.additiveTranslationUnitary h
      (ccmArchimedeanFourierToTime u)) = MellinL2.fourierPhaseMulUnitary h
      (fourierUnitary (ccmArchimedeanFourierToTime u)) from
    MellinL2.fourier_additiveTranslation h (ccmArchimedeanFourierToTime u),
    fourierUnitary_ccmArchimedeanFourierToTime]

private theorem translation_coeFn (h : ℝ) (f : SoninL2) :
    (logTranslationCLM h f : ℝ → ℂ) =ᵐ[volume] fun x => f (x + h) := by
  exact (Lp.coeFn_compMeasurePreserving f
    (MellinL2.realTranslation_measurePreserving h)).trans
      (Eventually.of_forall fun _ => rfl)

private theorem translated_cutoff {a b : SuzukiPositiveAperture} {h : ℝ}
    (hab : a.1 + |h| ≤ b.1) (u : CCMArchimedeanFormDomain a) :
    indicatorCutoff (centralInterval b.1) (measurableSet_centralInterval b.1)
      (logTranslationCLM h (ccmArchimedeanFourierToTime u.1)) =
      logTranslationCLM h (ccmArchimedeanFourierToTime u.1) := by
  let f := ccmArchimedeanFourierToTime u.1
  have hfix : indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1) f = f :=
    indicatorCutoff_ccmArchimedeanFormEmbedding a u
  have hfae : ∀ᵐ x, x ∉ centralInterval a.1 → f x = 0 := by
    have hcoe := indicatorCutoff_ae (centralInterval a.1)
      (measurableSet_centralInterval a.1) f
    rw [hfix] at hcoe
    filter_upwards [hcoe] with x hx hnot
    rw [hx, indicator_of_notMem hnot]
  have hshift := (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae.eventually hfae
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (centralInterval b.1)
    (measurableSet_centralInterval b.1) (logTranslationCLM h f),
    translation_coeFn h f, hshift] with x hcut htrans hz
  change indicatorCutoff (centralInterval b.1) (measurableSet_centralInterval b.1)
    (logTranslationCLM h f) x = logTranslationCLM h f x
  rw [hcut]
  by_cases hx : x ∈ centralInterval b.1
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, htrans]
    symm
    apply hz
    intro ha
    apply hx
    change -a.1 ≤ x + h ∧ x + h ≤ a.1 at ha
    change -b.1 ≤ x ∧ x ≤ b.1
    constructor <;> linarith [le_abs_self h, neg_abs_le h, ha.1, ha.2]

private theorem phaseMul_mem_formDomain {a b : SuzukiPositiveAperture} {h : ℝ}
    (hab : a.1 + |h| ≤ b.1) (u : CCMArchimedeanFormDomain a) :
    ccmArchimedeanPhaseMul h u.1 ∈ (ccmArchimedeanSupportDefect b).ker := by
  rw [LinearMap.mem_ker]
  change (1 - indicatorCutoff (centralInterval b.1) (measurableSet_centralInterval b.1))
    (ccmArchimedeanFourierToTime (ccmArchimedeanPhaseMul h u.1)) = 0
  rw [sub_apply, one_apply_eq_self, ccmArchimedeanFourierToTime_phaseMul,
    translated_cutoff hab u, sub_self]

/-- Translation between any two apertures with sufficient support margin. -/
def ccmArchimedeanFormTranslate {a b : SuzukiPositiveAperture} (h : ℝ)
    (hab : a.1 + |h| ≤ b.1) : CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain b :=
  ((ccmArchimedeanPhaseMul h).comp (ccmArchimedeanSupportDefect a).ker.subtypeL).codRestrict
    (ccmArchimedeanSupportDefect b).ker (phaseMul_mem_formDomain hab)

theorem ccmArchimedeanFormTranslate_val {a b : SuzukiPositiveAperture} (h : ℝ)
    (hab : a.1 + |h| ≤ b.1) (u : CCMArchimedeanFormDomain a) :
    (ccmArchimedeanFormTranslate h hab u).1 = ccmArchimedeanPhaseMul h u.1 := rfl

theorem norm_ccmArchimedeanFormTranslate {a b : SuzukiPositiveAperture} (h : ℝ)
    (hab : a.1 + |h| ≤ b.1) (u : CCMArchimedeanFormDomain a) :
    ‖ccmArchimedeanFormTranslate h hab u‖ = ‖u‖ :=
  norm_ccmArchimedeanPhaseMul h u.1

theorem ccmArchimedeanFormTranslate_physical {a b : SuzukiPositiveAperture} (h : ℝ)
    (hab : a.1 + |h| ≤ b.1) (u : CCMArchimedeanFormDomain a) :
    (ccmArchimedeanFormToAperture b (ccmArchimedeanFormTranslate h hab u) : SoninL2) =
      logTranslationCLM h (ccmArchimedeanFormToAperture a u : SoninL2) :=
  ccmArchimedeanFourierToTime_phaseMul h u.1

theorem norm_ccmArchimedeanFormTranslate_physical {a b : SuzukiPositiveAperture} (h : ℝ)
    (hab : a.1 + |h| ≤ b.1) (u : CCMArchimedeanFormDomain a) :
    ‖ccmArchimedeanFormToAperture b (ccmArchimedeanFormTranslate h hab u)‖ =
      ‖ccmArchimedeanFormToAperture a u‖ := by
  change ‖(ccmArchimedeanFormToAperture b (ccmArchimedeanFormTranslate h hab u) : SoninL2)‖ = _
  rw [ccmArchimedeanFormTranslate_physical]
  exact (MellinL2.additiveTranslationUnitary h).norm_map _

private theorem cutoff_translation_polar {a b : SuzukiPositiveAperture} {h : ℝ}
    (hab : a.1 + |h| ≤ b.1) (s : ℝ) :
    indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
      (logTranslationCLM (-h) (ccmPolarL2Vector b s)) =
        (Real.exp (-s * h) : ℂ) • ccmPolarL2Vector a s := by
  have hpb := (ccmPolarL2Vector_coeFn b s).comp_tendsto
    (MellinL2.realTranslation_measurePreserving (-h)).quasiMeasurePreserving.tendsto_ae
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (centralInterval a.1)
    (measurableSet_centralInterval a.1) (logTranslationCLM (-h) (ccmPolarL2Vector b s)),
    translation_coeFn (-h) (ccmPolarL2Vector b s), hpb,
    ccmPolarL2Vector_coeFn a s,
    Lp.coeFn_smul (Real.exp (-s * h) : ℂ) (ccmPolarL2Vector a s)]
    with x hcut htrans hpb hpa hsmul
  change ccmPolarL2Vector b s (x + -h) =
    (centralInterval b.1).indicator (ccmPolarProfile s) (x + -h) at hpb
  rw [hcut, hsmul]
  change (centralInterval a.1).indicator
      (fun x => logTranslationCLM (-h) (ccmPolarL2Vector b s) x) x =
    (Real.exp (-s * h) : ℂ) * ccmPolarL2Vector a s x
  rw [hpa]
  by_cases hx : x ∈ centralInterval a.1
  · have hxb : x + -h ∈ centralInterval b.1 := by
      change -a.1 ≤ x ∧ x ≤ a.1 at hx
      change -b.1 ≤ x + -h ∧ x + -h ≤ b.1
      constructor <;> linarith [hx.1, hx.2, le_abs_self h, neg_abs_le h]
    rw [indicator_of_mem hx, indicator_of_mem hx, htrans, hpb, indicator_of_mem hxb]
    simp only [ccmPolarProfile]
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

/-- Both exponential pole coordinates transform by their exact nonzero character. -/
theorem inner_polar_ccmArchimedeanFormTranslate {a b : SuzukiPositiveAperture} (h : ℝ)
    (hab : a.1 + |h| ≤ b.1) (s : ℝ) (u : CCMArchimedeanFormDomain a) :
    inner ℂ (ccmPolarApertureVector b s)
      (ccmArchimedeanFormToAperture b (ccmArchimedeanFormTranslate h hab u)) =
      (Real.exp (-s * h) : ℂ) *
        inner ℂ (ccmPolarApertureVector a s) (ccmArchimedeanFormToAperture a u) := by
  let f : SoninL2 := ccmArchimedeanFormToAperture a u
  let P := indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
  have hPf : P f = f := indicatorCutoff_ccmArchimedeanFormEmbedding a u
  change inner ℂ (ccmPolarL2Vector b s)
    (ccmArchimedeanFormToAperture b (ccmArchimedeanFormTranslate h hab u) : SoninL2) =
      (Real.exp (-s * h) : ℂ) * inner ℂ (ccmPolarL2Vector a s) f
  rw [ccmArchimedeanFormTranslate_physical]
  have hadj := inner_logTranslationCLM (-h) (ccmPolarL2Vector b s) f
  simp only [neg_neg] at hadj
  rw [← hadj]
  calc
    _ = inner ℂ (logTranslationCLM (-h) (ccmPolarL2Vector b s)) (P f) := by rw [hPf]
    _ = inner ℂ (P (logTranslationCLM (-h) (ccmPolarL2Vector b s))) f :=
      (indicatorCutoff_symmetric _ _ _ _).symm
    _ = _ := by
      rw [show P (logTranslationCLM (-h) (ccmPolarL2Vector b s)) =
        (Real.exp (-s * h) : ℂ) • ccmPolarL2Vector a s from cutoff_translation_polar hab s,
        inner_smul_left]
      simp only [Complex.conj_ofReal]

theorem IsPolarConstrained.translate {a b : SuzukiPositiveAperture} {u : CCMArchimedeanFormDomain a}
    (hu : IsPolarConstrained a u) (h : ℝ) (hab : a.1 + |h| ≤ b.1) :
    IsPolarConstrained b (ccmArchimedeanFormTranslate h hab u) := by
  unfold IsPolarConstrained
  rw [inner_polar_ccmArchimedeanFormTranslate, inner_polar_ccmArchimedeanFormTranslate,
    hu.1, hu.2, mul_zero, mul_zero]
  exact ⟨rfl, rfl⟩

private theorem translation_pairing (t h : ℝ) (f : SoninL2) :
    inner ℂ (logTranslationCLM t (logTranslationCLM h f)) (logTranslationCLM h f) =
      inner ℂ (logTranslationCLM t f) f := by
  rw [logTranslationCLM_add_apply, add_comm t h, ← logTranslationCLM_add_apply]
  exact (MellinL2.additiveTranslationUnitary h).inner_map_map _ _

/-- Translation preserves the complete literal prime–Gamma quadratic on the pole-constrained
sector. Extra prime indices at the larger aperture vanish by support, via exact extension. -/
theorem ccmRestrictedWeilSourceQuadratic_translate {a b : SuzukiPositiveAperture} (h : ℝ)
    (hab : a.1 + |h| ≤ b.1) (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u) :
    ccmRestrictedWeilSourceQuadratic b (ccmArchimedeanFormTranslate h hab u) =
      ccmRestrictedWeilSourceQuadratic a u := by
  have hab' : a.1 ≤ b.1 := by linarith [abs_nonneg h]
  obtain ⟨w, hwval⟩ := exists_ccmArchimedeanFormDomain_extension hab' u
  have hw : IsPolarConstrained b w := (isPolarConstrained_iff_of_val_eq hab' hwval).mpr hu
  have hv := hu.translate h hab
  let v := ccmArchimedeanFormTranslate h hab u
  change IsPolarConstrained b v at hv
  have hgamma :
      (∫ x, 2 * gammaHardyPhaseRate (2 * Real.pi * x) * ‖(v.1 : ℝ → ℂ) x‖ ^ 2) =
      ∫ x, 2 * gammaHardyPhaseRate (2 * Real.pi * x) * ‖(w.1 : ℝ → ℂ) x‖ ^ 2 := by
    rw [hwval]
    apply integral_congr_ae
    have hp := (ccmArchimedeanPhaseMul_coeFn h u.1).filter_mono
      (ae_mono volume_le_ccmArchimedeanFormMeasure)
    filter_upwards [hp] with x hx
    change _ * ‖ccmArchimedeanPhaseMul h u.1 x‖ ^ 2 = _
    rw [hx, norm_mul, MellinL2.norm_fourierPhase, one_mul]
  have hp : ∀ t : ℝ,
      inner ℂ (logTranslationCLM t (ccmArchimedeanFormToAperture b v : SoninL2))
        (ccmArchimedeanFormToAperture b v : SoninL2) =
      inner ℂ (logTranslationCLM t (ccmArchimedeanFormToAperture b w : SoninL2))
        (ccmArchimedeanFormToAperture b w : SoninL2) := by
    intro t
    rw [ccmArchimedeanFormToAperture_coe_eq_of_val_eq hwval]
    change inner ℂ (logTranslationCLM t
      (ccmArchimedeanFormToAperture b (ccmArchimedeanFormTranslate h hab u) : SoninL2))
        (ccmArchimedeanFormToAperture b (ccmArchimedeanFormTranslate h hab u) : SoninL2) = _
    rw [ccmArchimedeanFormTranslate_physical]
    exact translation_pairing t h _
  calc
    _ = ccmRestrictedWeilSourceQuadratic b w := by
      change ccmRestrictedWeilSourceQuadratic b v = _
      simp only [ccmRestrictedWeilSourceQuadratic, hv.1, hv.2, hw.1, hw.2,
        mul_zero, Complex.zero_re, add_zero]
      simp_rw [hp]
      rw [hgamma]
    _ = _ := ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hab' hwval

end RHTower
