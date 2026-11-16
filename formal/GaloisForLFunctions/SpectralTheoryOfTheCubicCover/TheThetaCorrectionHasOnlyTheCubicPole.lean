import GaloisForLFunctions.OrderSixMetaplecticTheory.TheEisensteinCorrectionIsHolomorphicOnTheRealSegment
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.IntegralCoverCorrespondences

/-!
# Cutoff-independent removal of the real spectral poles

The compact restrictions of corrected incoming seeds agree on the full upper
half-strip `Re s>1`. Multiplication by the vanishing spectral denominator
eliminates the entire seeds, so compact exhaustion identifies their real
spectral residues. The vanishing projection for cutoff `[5,6]` therefore holds
for every incoming cutoff above height one. Divided differences then supply
a holomorphic representative at each real `s>1`, except `s=4/3`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped Classical
namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover
open MetaplecticMobiusDescent.CubicEisenstein OrderSixMetaplecticTheory

private theorem correction_decomposition (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (r : ℝ) (hr : 1 < r) (hr2 : r ≤ 2) :
    ∀ᶠ s in 𝓝[≠] (r : ℂ), kernelEisensteinL2Correction a b ha hab s =
      ((((r * (2 - r) : ℝ) : ℂ) + 1) /
        (((r * (2 - r) : ℝ) : ℂ) - kernelEisensteinSpectralParameter s)) •
          eigenProjection (r * (2 - r)) (kernelL2Defect a b ha hab s) +
        regularResolvent (r * (2 - r)) (kernelEisensteinSpectralParameter s)
          (kernelL2Defect a b ha hab s) := by
  have h0 : 0 ≤ r * (2 - r) := mul_nonneg (by linarith) (by linarith)
  have h1 : r * (2 - r) < 1 := by nlinarith only [sq_pos_of_pos (sub_pos.mpr hr)]
  filter_upwards [(spectralParameter_tendsto r hr).eventually
    (resolvent_eventually_eq (r * (2 - r)) h0 h1)] with s hs
  change kernelSpectralResolvent (kernelEisensteinSpectralParameter s) _ = _
  rw [hs]
  rfl

private theorem spectral_resolvent_residue (μ : ℝ) (h0 : 0 ≤ μ) (h1 : μ < 1) :
    Tendsto (fun z : ℂ => ((μ : ℂ) - z) • kernelSpectralResolvent z)
      (𝓝[≠] (μ : ℂ)) (𝓝 (((μ : ℂ) + 1) • eigenProjection μ)) := by
  have hcont : ContinuousAt (fun z : ℂ => (((μ : ℂ) + 1) • eigenProjection μ) +
      ((μ : ℂ) - z) • regularResolvent μ z) (μ : ℂ) :=
    continuousAt_const.add ((continuousAt_const.sub continuousAt_id).smul
      (regularResolvent_analyticAt μ h0 h1).continuousAt)
  have hlim := hcont.tendsto.mono_left
    (show 𝓝[≠] (μ : ℂ) ≤ 𝓝 (μ : ℂ) from nhdsWithin_le_nhds)
  simp only [sub_self, zero_smul, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [resolvent_eventually_eq μ h0 h1, self_mem_nhdsWithin] with z hz hne
  have hne' : z ≠ (μ : ℂ) := hne
  rw [hz, smul_add, smul_smul, mul_div_cancel₀ _ (sub_ne_zero.mpr hne'.symm)]

private theorem forcing_spectral_residue (F : ℂ → KernelQuotientL2)
    (r : ℝ) (hr : 1 < r) (hr2 : r ≤ 2) (hF : ContinuousAt F (r : ℂ)) :
    Tendsto (fun s => (((r * (2 - r) : ℝ) : ℂ) - kernelEisensteinSpectralParameter s) •
      kernelSpectralResolvent (kernelEisensteinSpectralParameter s) (F s)) (𝓝[≠] (r : ℂ))
      (𝓝 (((((r * (2 - r) : ℝ) : ℂ) + 1)) •
        eigenProjection (r * (2 - r)) (F r))) := by
  have h0 : 0 ≤ r * (2 - r) := mul_nonneg (by linarith) (by linarith)
  have h1 : r * (2 - r) < 1 := by nlinarith only [sq_pos_of_pos (sub_pos.mpr hr)]
  have hR : Tendsto (fun s : ℂ => (((r * (2 - r) : ℝ) : ℂ) - kernelEisensteinSpectralParameter s) •
      kernelSpectralResolvent (kernelEisensteinSpectralParameter s)) (𝓝[≠] (r : ℂ))
      (𝓝 (((((r * (2 - r) : ℝ) : ℂ) + 1)) • eigenProjection (r * (2 - r)))) :=
    (spectral_resolvent_residue (r * (2 - r)) h0 h1).comp (spectralParameter_tendsto r hr)
  exact ((isBoundedBilinearMap_apply (𝕜 := ℂ) (E := KernelQuotientL2)
    (F := KernelQuotientL2)).continuous.tendsto _).comp
      (hR.prodMk_nhds (hF.tendsto.mono_left nhdsWithin_le_nhds))

private theorem correction_spectral_residue (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (r : ℝ) (hr : 1 < r) (hr2 : r ≤ 2) :
    Tendsto (fun s => (((r * (2 - r) : ℝ) : ℂ) - kernelEisensteinSpectralParameter s) •
      kernelEisensteinL2Correction a b ha hab s) (𝓝[≠] (r : ℂ))
      (𝓝 (((((r * (2 - r) : ℝ) : ℂ) + 1)) •
        eigenProjection (r * (2 - r)) (kernelL2Defect a b ha hab r))) :=
  forcing_spectral_residue (kernelL2Defect a b ha hab) r hr hr2
    (kernelL2Defect_entire a b ha hab).continuous.continuousAt

private theorem localCorrectedSeed_cutoff_eq_upper
    (S : Set KernelQuotient) (hS : IsCompact S)
    (a b c d : ℝ) (ha : 1 < a) (hab : a < b) (hc : 1 < c) (hcd : c < d) :
    Set.EqOn (kernelLocalCorrectedSeed S hS a b (by linarith) hab)
      (kernelLocalCorrectedSeed S hS c d (by linarith) hcd) upperStrip := by
  have h1 : AnalyticOnNhd ℂ (kernelLocalCorrectedSeed S hS a b (by linarith) hab) upperStrip :=
    fun s hs => kernelLocalCorrectedSeed_analyticAt_nonreal S hS a b (by linarith) hab s
      (by linarith [hs.1]) hs.2.ne'
  have h2 : AnalyticOnNhd ℂ (kernelLocalCorrectedSeed S hS c d (by linarith) hcd) upperStrip :=
    fun s hs => kernelLocalCorrectedSeed_analyticAt_nonreal S hS c d (by linarith) hcd s
      (by linarith [hs.1]) hs.2.ne'
  have hopen : IsOpen {s : ℂ | 4 < s.re ∧ 0 < s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  apply h1.eqOn_of_preconnected_of_eventuallyEq h2 upperStrip_isPreconnected
    (by norm_num [upperStrip] : (5 + Complex.I : ℂ) ∈ upperStrip)
  filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
  exact kernelLocalCorrectedSeed_initial_eq S hS a b c d ha hab hc hcd s hs.1 hs.2

/-- Real spectral residues are independent of the incoming height cutoff. -/
theorem correction_spectral_residue_cutoff_independent
    (a b c d : ℝ) (ha : 1 < a) (hab : a < b) (hc : 1 < c) (hcd : c < d)
    (r : ℝ) (hr : 1 < r) (hr2 : r ≤ 2) :
    eigenProjection (r * (2 - r)) (kernelL2Defect a b (by linarith) hab r) =
      eigenProjection (r * (2 - r)) (kernelL2Defect c d (by linarith) hcd r) := by
  let μ : ℝ := r * (2 - r)
  have hval : kernelEisensteinSpectralParameter (r : ℂ) = (μ : ℂ) := by
    dsimp only [μ, kernelEisensteinSpectralParameter]
    push_cast
    ring
  let L := 𝓝[{s : ℂ | 0 < s.im}] (r : ℂ)
  haveI : L.NeBot := upper_nhdsWithin_neBot r
  have hL : L ≤ 𝓝[≠] (r : ℂ) := nhdsWithin_mono _ fun s hs h => by
    rw [Set.mem_singleton_iff] at h
    rw [Set.mem_setOf_eq, h, Complex.ofReal_im] at hs
    exact lt_irrefl 0 hs
  have hlocal (S : Set KernelQuotient) (hS : IsCompact S)
      (a b : ℝ) (ha : 0 < a) (hab : a < b) :
      Tendsto (fun s => ((μ : ℂ) - kernelEisensteinSpectralParameter s) •
        kernelLocalCorrectedSeed S hS a b ha hab s) L
        (𝓝 (kernelMassRestrictionCLM S hS.measurableSet
          (((μ : ℂ) + 1) • eigenProjection μ (kernelL2Defect a b ha hab r)))) := by
    have hseed : Tendsto (fun s => ((μ : ℂ) - kernelEisensteinSpectralParameter s) •
        kernelLocalSeedL2 S hS a b ha s) L (𝓝 0) := by
      have hcont : ContinuousAt (fun s => ((μ : ℂ) - kernelEisensteinSpectralParameter s) •
          kernelLocalSeedL2 S hS a b ha s) (r : ℂ) :=
        (continuousAt_const.sub spectralParameter_continuous.continuousAt).smul
          ((kernelLocalSeedL2_entire S hS a b ha).continuous.continuousAt)
      have h := hcont.tendsto
      rw [hval, sub_self, zero_smul] at h
      exact h.mono_left (hL.trans nhdsWithin_le_nhds)
    have hcorr := ((kernelMassRestrictionCLM S hS.measurableSet).continuous.continuousAt.tendsto.comp
      (correction_spectral_residue a b ha hab r hr hr2)).mono_left hL
    simpa only [kernelLocalCorrectedSeed, smul_add, map_smul, Function.comp_def, zero_add]
      using hseed.add hcorr
  have hscale : ((μ : ℂ) + 1) • eigenProjection μ (kernelL2Defect a b (by linarith) hab r) =
      ((μ : ℂ) + 1) • eigenProjection μ (kernelL2Defect c d (by linarith) hcd r) := by
    apply kernelL2_eq_of_compact_restrictions
    intro S hS
    apply tendsto_nhds_unique_of_eventuallyEq
      (hlocal S hS a b (by linarith) hab) (hlocal S hS c d (by linarith) hcd)
    have hre : ∀ᶠ s in 𝓝 (r : ℂ), 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hr
    filter_upwards [hre.filter_mono (hL.trans nhdsWithin_le_nhds), self_mem_nhdsWithin] with s hs hi
    exact congrArg (fun v : KernelQuotientL2 => ((μ : ℂ) - kernelEisensteinSpectralParameter s) • v)
      (localCorrectedSeed_cutoff_eq_upper S hS a b c d ha hab hc hcd ⟨hs, hi⟩)
  have hμ0 : 0 ≤ μ := mul_nonneg (by linarith) (by linarith)
  have hμ1 : (μ : ℂ) + 1 ≠ 0 := by
    have : μ + 1 ≠ 0 := by linarith
    exact_mod_cast this
  exact (smul_right_injective _ hμ1) hscale

/-- Every incoming cutoff annihilates the real eigenspaces away from `s=4/3`. -/
theorem eigenProjection_kernelL2Defect_eq_zero (a b : ℝ) (ha : 1 < a) (hab : a < b)
    (r : ℝ) (hr : 1 < r) (hr2 : r ≤ 2) (hr43 : r ≠ 4 / 3) :
    eigenProjection (r * (2 - r)) (kernelL2Defect a b (by linarith) hab r) = 0 := by
  rw [correction_spectral_residue_cutoff_independent a b 5 6 ha hab (by norm_num)
    (by norm_num) r hr hr2]
  exact eigenProjection_seedDefect_eq_zero r hr hr2 hr43

/-- Every incoming cutoff has a holomorphic representative near real `r>1`, except `4/3`. -/
theorem kernelEisensteinCorrection_removable (a b : ℝ) (ha : 1 < a) (hab : a < b)
    (r : ℝ) (hr : 1 < r) (hr43 : r ≠ 4 / 3) :
    ∃ C : ℂ → KernelQuotientL2, AnalyticAt ℂ C (r : ℂ) ∧
      ∀ᶠ s in 𝓝[≠] (r : ℂ), C s = kernelEisensteinL2Correction a b (by linarith) hab s := by
  have ha0 : 0 < a := by linarith
  let F : ℂ → KernelQuotientL2 := kernelL2Defect a b ha0 hab
  have hF : Differentiable ℂ F := kernelL2Defect_entire a b ha0 hab
  have hval : kernelEisensteinSpectralParameter (r : ℂ) = ((r * (2 - r) : ℝ) : ℂ) := by
    unfold kernelEisensteinSpectralParameter
    push_cast
    ring
  by_cases hr2 : r ≤ 2
  · have hμ0 : 0 ≤ r * (2 - r) := mul_nonneg (by linarith) (by linarith)
    have hμ1 : r * (2 - r) < 1 := by nlinarith only [sq_pos_of_pos (sub_pos.mpr hr)]
    have hPi : eigenProjection (r * (2 - r)) (F r) = 0 :=
      eigenProjection_kernelL2Defect_eq_zero a b ha hab r hr hr2 hr43
    have hden : ((r : ℂ) + (r : ℂ) - 2) ≠ 0 := by
      have : (r + r - 2 : ℝ) ≠ 0 := by linarith
      exact_mod_cast this
    have hdslope : AnalyticAt ℂ (dslope F (r : ℂ)) (r : ℂ) :=
      ((Complex.differentiableOn_dslope Filter.univ_mem).mpr hF.differentiableOn).analyticAt
        Filter.univ_mem
    refine ⟨fun s : ℂ => ((((r * (2 - r) : ℝ) : ℂ) + 1) •
        eigenProjection (r * (2 - r)) ((s + (r : ℂ) - 2)⁻¹ • dslope F (r : ℂ) s) +
      regularResolvent (r * (2 - r)) (kernelEisensteinSpectralParameter s) (F s)), ?_, ?_⟩
    · have hinv : AnalyticAt ℂ (fun s : ℂ => (s + (r : ℂ) - 2)⁻¹) (r : ℂ) :=
        ((analyticAt_id.add analyticAt_const).sub analyticAt_const).inv hden
      have hin := hinv.smul hdslope
      have hfirst : AnalyticAt ℂ (fun s : ℂ => ((((r * (2 - r) : ℝ) : ℂ) + 1) •
          eigenProjection (r * (2 - r)) ((s + (r : ℂ) - 2)⁻¹ • dslope F (r : ℂ) s)))
          (r : ℂ) :=
        ((((((r * (2 - r) : ℝ) : ℂ) + 1) • eigenProjection (r * (2 - r))).analyticAt _).comp hin :)
      have hRreg : AnalyticAt ℂ (fun s => regularResolvent (r * (2 - r))
          (kernelEisensteinSpectralParameter s)) (r : ℂ) :=
        (regularResolvent_analyticAt _ hμ0 hμ1).comp_of_eq (spectralParameter_analyticAt _) hval
      have hsecond : AnalyticAt ℂ (fun s => regularResolvent (r * (2 - r))
          (kernelEisensteinSpectralParameter s) (F s)) (r : ℂ) :=
        ((ContinuousLinearMap.apply ℂ KernelQuotientL2).analyticAt_bilinear
          (F r, regularResolvent (r * (2 - r)) (kernelEisensteinSpectralParameter r))).comp₂
            (hF.analyticAt _) hRreg
      exact hfirst.add hsecond
    · filter_upwards [correction_decomposition a b ha0 hab r hr hr2, self_mem_nhdsWithin]
        with s hs hs0
      rw [hs]
      congr 1
      have hs0' : s ≠ (r : ℂ) := hs0
      rw [dslope_of_ne _ hs0', slope_def_module, smul_smul, map_smul, map_sub, hPi,
        sub_zero, smul_smul]
      congr 1
      have hμc : ((r * (2 - r) : ℝ) : ℂ) = (r : ℂ) * (2 - r) := by push_cast; ring
      rw [hμc, spectralParameter_sub]
      have hne1 : s - r ≠ 0 := sub_ne_zero.mpr hs0'
      by_cases hne2 : s + r - 2 = 0
      · rw [hne2]
        simp
      · field_simp
  · have hr2' : 2 < r := lt_of_not_ge hr2
    have hneg : r * (2 - r) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    refine ⟨kernelEisensteinL2Correction a b ha0 hab, ?_, Eventually.of_forall fun _ => rfl⟩
    have hU := isUnit_spectralForm_of_neg hneg
    have hinv : AnalyticAt ℂ (fun z => Ring.inverse (kernelSpectralFormOperator z))
        ((r * (2 - r) : ℝ) : ℂ) := kernelSpectralFormInverse_analyticAt_of_isUnit _ hU
    have hR : AnalyticAt ℂ kernelSpectralResolvent ((r * (2 - r) : ℝ) : ℂ) := by
      change AnalyticAt ℂ (⇑kernelL2SandwichCLM ∘ fun z => Ring.inverse (kernelSpectralFormOperator z)) _
      exact (kernelL2SandwichCLM.analyticAt _).comp hinv
    have hE : AnalyticAt ℂ kernelEisensteinResolvent (r : ℂ) :=
      hR.comp_of_eq (spectralParameter_analyticAt _) hval
    exact ((ContinuousLinearMap.apply ℂ KernelQuotientL2).analyticAt_bilinear
      (F r, kernelEisensteinResolvent r)).comp₂ (hF.analyticAt _) hE

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
