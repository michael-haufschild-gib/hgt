import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilBoundedRemainder
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanPhaseTemperate

/-!
# Dense source core for the exact CCM archimedean form

The literal shifted Riemann--Siegel density is a temperate multiplier.  Hence every compactly
supported smooth physical test has Fourier transform in the exact weighted form domain.  These
tests detect the orthogonal complement of the form embedding, proving dense range into the
physical aperture.  This supplies the density premise used implicitly in the representation
theorem of Connes--Consani, without replacing their density by an asymptotic logarithmic model.
-/

open MeasureTheory Set
open scoped ENNReal InnerProduct FourierTransform SchwartzMap

noncomputable section

namespace RHTower

/-- Evenness removes the absolute value in the exact archimedean density. -/
theorem ccmArchimedeanFormWeight_eq_linearArgument (xi : ℝ) :
    ccmArchimedeanFormWeight xi =
      1 + 2 * (gammaHardyPhaseRate (2 * Real.pi * xi) - gammaHardyPhaseRate 0) := by
  unfold ccmArchimedeanFormWeight
  congr 3
  by_cases hxi : 0 ≤ xi
  · rw [abs_of_nonneg hxi]
  · have hneg : xi < 0 := lt_of_not_ge hxi
    have habs : 2 * Real.pi * |xi| = -(2 * Real.pi * xi) := by
      rw [abs_of_neg hneg]
      ring
    rw [habs, gammaHardyPhaseRate_neg]

/-- The literal shifted Riemann--Siegel density is a Schwartz multiplier. -/
theorem ccmArchimedeanFormWeight_complex_hasTemperateGrowth :
    Function.HasTemperateGrowth
      (fun xi : ℝ => (ccmArchimedeanFormWeight xi : ℂ)) := by
  have hscale : Function.HasTemperateGrowth
      (fun xi : ℝ => 2 * Real.pi * xi) := by fun_prop
  have hrate : Function.HasTemperateGrowth
      (fun xi : ℝ => (gammaHardyPhaseRate (2 * Real.pi * xi) : ℂ)) := by
    simpa only [Function.comp_def] using
      gammaHardyPhaseRate_complex_hasTemperateGrowth.comp hscale
  have hsource : Function.HasTemperateGrowth
      (fun xi : ℝ => (1 : ℂ) + 2 *
        ((gammaHardyPhaseRate (2 * Real.pi * xi) : ℂ) -
          (gammaHardyPhaseRate 0 : ℂ))) :=
    (Function.HasTemperateGrowth.const (1 : ℂ)).add
      ((Function.HasTemperateGrowth.const (2 : ℂ)).mul
        (hrate.sub (Function.HasTemperateGrowth.const (gammaHardyPhaseRate 0 : ℂ))))
  convert hsource using 1
  funext xi
  rw [ccmArchimedeanFormWeight_eq_linearArgument]
  push_cast
  rfl

theorem _root_.SchwartzMap.integrable_ccmArchimedeanFormWeight_mul_norm_sq
    (F : SchwartzMap ℝ ℂ) :
    Integrable (fun xi : ℝ => ccmArchimedeanFormWeight xi * ‖F xi‖ ^ 2) := by
  let C : ℝ := SchwartzMap.seminorm ℂ 0 0 F
  let WF : SchwartzMap ℝ ℂ :=
    SchwartzMap.smulLeftCLM ℂ (fun xi : ℝ => (ccmArchimedeanFormWeight xi : ℂ)) F
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hWF : Integrable (fun xi : ℝ => ‖WF xi‖) := WF.integrable.norm
  have hmajor : Integrable (fun xi : ℝ => C * ‖WF xi‖) := hWF.const_mul C
  refine Integrable.mono' hmajor
    (measurable_ccmArchimedeanFormWeight.mul
      (F.continuous.norm.measurable.pow_const 2)).aestronglyMeasurable ?_
  filter_upwards with xi
  have hF : ‖F xi‖ ≤ C := SchwartzMap.norm_le_seminorm ℂ F xi
  have hweight : 0 ≤ ccmArchimedeanFormWeight xi :=
    (one_le_ccmArchimedeanFormWeight xi).trans' zero_le_one
  have hWFpoint : ‖WF xi‖ = ccmArchimedeanFormWeight xi * ‖F xi‖ := by
    rw [show WF xi = (ccmArchimedeanFormWeight xi : ℂ) • F xi by
      exact SchwartzMap.smulLeftCLM_apply_apply
        ccmArchimedeanFormWeight_complex_hasTemperateGrowth F xi]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hweight]
  have hcalc : ccmArchimedeanFormWeight xi * ‖F xi‖ ^ 2 ≤ C * ‖WF xi‖ := by
    rw [hWFpoint]
    calc
      ccmArchimedeanFormWeight xi * ‖F xi‖ ^ 2 =
          (ccmArchimedeanFormWeight xi * ‖F xi‖) * ‖F xi‖ := by ring
      _ ≤ (ccmArchimedeanFormWeight xi * ‖F xi‖) * C :=
        mul_le_mul_of_nonneg_left hF (mul_nonneg hweight (norm_nonneg _))
      _ = C * (ccmArchimedeanFormWeight xi * ‖F xi‖) := by ring
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hweight (sq_nonneg _)),
    abs_of_nonneg (mul_nonneg hC0 (norm_nonneg _))] using hcalc

theorem _root_.SchwartzMap.memLp_two_ccmArchimedeanFormMeasure
    (F : SchwartzMap ℝ ℂ) :
    MemLp (F : ℝ → ℂ) 2 ccmArchimedeanFormMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    F.continuous.aestronglyMeasurable).2
  unfold ccmArchimedeanFormMeasure
  rw [integrable_withDensity_iff_integrable_smul
    measurable_ccmArchimedeanFormWeightNNReal]
  refine F.integrable_ccmArchimedeanFormWeight_mul_norm_sq.congr ?_
  filter_upwards with xi
  rw [NNReal.smul_def, smul_eq_mul, coe_ccmArchimedeanFormWeightNNReal]

/-- Every smooth real compactly supported interior test belongs to the literal CCM form domain. -/
theorem exists_ccmArchimedeanFormDomain_eq_smoothRealTest
    (a : SuzukiPositiveAperture) (g : ℝ → ℝ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    (hgaper : tsupport g ⊆ Ioo (-a.1) a.1) :
    ∃ f : CCMArchimedeanFormDomain a,
      ccmArchimedeanFormEmbedding a f = suzukiRealTestL2 g hgdiff hgsupp := by
  let G : SchwartzMap ℝ ℂ := suzukiRealTestSchwartz g hgdiff hgsupp
  let F : SchwartzMap ℝ ℂ := 𝓕 G
  let hF : MemLp (F : ℝ → ℂ) 2 ccmArchimedeanFormMeasure :=
    F.memLp_two_ccmArchimedeanFormMeasure
  let w : CCMArchimedeanFourierL2 := hF.toLp F
  have hwToL2 : ccmArchimedeanWeightedToL2 w = F.toLp 2 volume := by
    apply Lp.ext
    have hwFweighted : (w : ℝ → ℂ) =ᵐ[ccmArchimedeanFormMeasure] F := hF.coeFn_toLp
    have hwFvolume : (w : ℝ → ℂ) =ᵐ[volume] F :=
      hwFweighted.filter_mono (ae_mono volume_le_ccmArchimedeanFormMeasure)
    filter_upwards [ccmArchimedeanWeightedToL2_coeFn w, hwFvolume,
      F.coeFn_toLp 2 volume] with x hw hFv hFL2
    rw [hw, hFv, hFL2]
  have htime : ccmArchimedeanFourierToTime w = G.toLp 2 volume := by
    apply fourierUnitary.injective
    rw [fourierUnitary_ccmArchimedeanFourierToTime, hwToL2]
    exact (SchwartzMap.toLp_fourier_eq G).symm
  have hfix : indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1) (G.toLp 2 volume) = G.toLp 2 volume := by
    apply Lp.ext
    have hcoeG : (G.toLp 2 volume : ℝ → ℂ) =ᵐ[volume]
        suzukiRealTestComplex g := by
      simpa [G, suzukiRealTestL2] using
        suzukiRealTestL2_coeFn g hgdiff hgsupp
    filter_upwards [indicatorCutoff_ae (centralInterval a.1)
        (measurableSet_centralInterval a.1) (G.toLp 2 volume),
      hcoeG] with x hcut hcoe
    rw [hcut]
    by_cases hx : x ∈ centralInterval a.1
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hcoe]
      have hgzero : g x = 0 := by
        apply Function.notMem_support.mp
        intro hxg
        apply hx
        exact Ioo_subset_Icc_self (hgaper (subset_tsupport g hxg))
      simp [suzukiRealTestComplex, hgzero]
  have hwker : w ∈ (ccmArchimedeanSupportDefect a).ker := by
    rw [LinearMap.mem_ker]
    change (1 - indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1)) (ccmArchimedeanFourierToTime w) = 0
    rw [htime, sub_apply, one_apply_eq_self, hfix, sub_self]
  refine ⟨⟨w, hwker⟩, ?_⟩
  change ccmArchimedeanFourierToTime w = suzukiRealTestL2 g hgdiff hgsupp
  exact htime

theorem denseRange_ccmArchimedeanFormToAperture (a : SuzukiPositiveAperture) :
    DenseRange (ccmArchimedeanFormToAperture a) := by
  have hdense : Dense
      ((ccmArchimedeanFormToAperture a).toLinearMap.range :
        Set (suzukiApertureHilbert a)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro h hh
    have hinside : ∀ᵐ x : ℝ ∂volume,
        x ∈ Ioo (-a.1) a.1 → (h.1 : ℝ → ℂ) x = 0 := by
      apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (((Lp.memLp h.1).locallyIntegrable (by norm_num)).locallyIntegrableOn _)
      intro g hgdiff hgsupp hgaper
      obtain ⟨f, hf⟩ := exists_ccmArchimedeanFormDomain_eq_smoothRealTest
        a g hgdiff hgsupp hgaper
      have horth : inner ℂ (ccmArchimedeanFormToAperture a f) h = 0 :=
        ((Submodule.mem_orthogonal _ _).mp hh) _ ⟨f, rfl⟩
      change inner ℂ (ccmArchimedeanFormEmbedding a f) h.1 = 0 at horth
      rw [MeasureTheory.L2.inner_def] at horth
      have htest : (ccmArchimedeanFormEmbedding a f : ℝ → ℂ) =ᵐ[volume]
          suzukiRealTestComplex g := by
        rw [hf]
        exact suzukiRealTestL2_coeFn g hgdiff hgsupp
      have hintegrand :
          (fun x : ℝ => inner ℂ
              ((ccmArchimedeanFormEmbedding a f : SoninL2) x)
                ((h.1 : SoninL2) x)) =ᵐ[volume]
            fun x => g x • (h.1 : ℝ → ℂ) x := by
        filter_upwards [htest] with x hx
        rw [hx]
        simp [suzukiRealTestComplex, RCLike.inner_apply, Complex.real_smul, mul_comm]
      rw [integral_congr_ae hintegrand] at horth
      exact horth
    have hfix := indicatorCutoff_suzukiApertureHilbert a h
    have hfixae :
        (indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) h.1 :
          ℝ → ℂ) =ᵐ[volume] (h.1 : ℝ → ℂ) := by
      rw [hfix]
    have houtside : ∀ᵐ x : ℝ ∂volume,
        x ∉ centralInterval a.1 → (h.1 : ℝ → ℂ) x = 0 := by
      filter_upwards [indicatorCutoff_ae (centralInterval a.1)
        (measurableSet_centralInterval a.1) h.1, hfixae] with x hcut hfae
      intro hx
      rw [← hfae, hcut, indicator_of_notMem hx]
    have hleft : ∀ᵐ x : ℝ ∂volume, x ≠ -a.1 := by
      rw [ae_iff]
      simp
    have hright : ∀ᵐ x : ℝ ∂volume, x ≠ a.1 := by
      rw [ae_iff]
      simp
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hinside, houtside, hleft, hright,
      Lp.coeFn_zero ℂ 2 volume] with x hin hout hxl hxr hzero
    change (h.1 : ℝ → ℂ) x = (0 : SoninL2) x
    rw [hzero]
    by_cases hx : x ∈ centralInterval a.1
    · apply hin
      rw [centralInterval, mem_Icc] at hx
      exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hxl), lt_of_le_of_ne hx.2 hxr⟩
    · exact hout hx
  change Dense (Set.range (ccmArchimedeanFormToAperture a))
  have hrange : Set.range (ccmArchimedeanFormToAperture a) =
      ((ccmArchimedeanFormToAperture a).toLinearMap.range :
        Set (suzukiApertureHilbert a)) := by
    ext h
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨f, rfl⟩
    · rintro ⟨f, hf⟩
      exact ⟨f, hf⟩
  rw [hrange]
  exact hdense

end RHTower
