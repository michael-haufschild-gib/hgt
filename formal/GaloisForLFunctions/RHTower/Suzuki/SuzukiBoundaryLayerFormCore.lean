import GaloisForLFunctions.RHTower.Suzuki.SuzukiBoundaryLayerHlogConvergence

/-!
# Suzuki boundary layers as genuine `H^log` form-domain vectors

The preceding boundary-layer module proves convergence of weighted Fourier integrals.  This file
performs the non-formal bookkeeping that is mathematically essential in Suzuki's equation (3.2):

* every complex-valued globally smooth compactly supported aperture test is realized in the
  complete `H^log(-a,a)` form domain;
* every nonsmooth endpoint error is realized from its classical Fourier transform;
* the zero-extended exponential is an actual form-domain vector;
* its explicit smooth cutoffs converge in the Hilbert form norm.

Suzuki defines `C_c^∞(-a,a)` as globally smooth functions whose support is contained in the closed
interval `[-a,a]`; topological support is therefore allowed to meet the endpoints.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal FourierTransform ContDiff SchwartzMap

noncomputable section

namespace RHTower

/-! ## Complex smooth tests in the complete form domain -/

def suzukiComplexTestSchwartz (g : ℝ → ℂ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g) :
    SchwartzMap ℝ ℂ :=
  hgsupp.toSchwartzMap hgdiff

def suzukiComplexTestL2 (g : ℝ → ℂ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g) : SoninL2 :=
  (suzukiComplexTestSchwartz g hgdiff hgsupp).toLp 2 volume

theorem suzukiComplexTestL2_coeFn (g : ℝ → ℂ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g) :
    (suzukiComplexTestL2 g hgdiff hgsupp : ℝ → ℂ) =ᵐ[volume] g :=
  (suzukiComplexTestSchwartz g hgdiff hgsupp).coeFn_toLp 2 volume

/-- Complex version of the smooth-test realization theorem.  This removes the real-valued
restriction from the earlier density infrastructure and matches Suzuki's exponential cutoffs. -/
theorem exists_suzukiHlogFormDomain_eq_smoothComplexTest
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    (hgaper : tsupport g ⊆ Icc (-a.1) a.1) :
    ∃ f : SuzukiHlogFormDomain a,
      suzukiHlogFormEmbedding a f = suzukiComplexTestL2 g hgdiff hgsupp := by
  let G : SchwartzMap ℝ ℂ := suzukiComplexTestSchwartz g hgdiff hgsupp
  let F : SchwartzMap ℝ ℂ := 𝓕 G
  let hF : MemLp (F : ℝ → ℂ) 2 suzukiHlogMeasure :=
    F.memLp_two_suzukiHlogMeasure
  let w : SuzukiHlogFourierL2 := hF.toLp F
  have hwToL2 : suzukiHlogWeightedToL2 w = F.toLp 2 volume := by
    apply Lp.ext
    have hwFweighted : (w : ℝ → ℂ) =ᵐ[suzukiHlogMeasure] F :=
      hF.coeFn_toLp
    have hwFvolume : (w : ℝ → ℂ) =ᵐ[volume] F :=
      hwFweighted.filter_mono (ae_mono volume_le_suzukiHlogMeasure)
    filter_upwards [suzukiHlogWeightedToL2_coeFn w, hwFvolume,
      F.coeFn_toLp 2 volume] with x hw hFv hFL2
    rw [hw, hFv, hFL2]
  have htime : suzukiHlogFourierToTime w = G.toLp 2 volume := by
    apply fourierUnitary.injective
    rw [fourierUnitary_suzukiHlogFourierToTime, hwToL2]
    exact (SchwartzMap.toLp_fourier_eq G).symm
  have hfix : indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1) (G.toLp 2 volume) = G.toLp 2 volume := by
    apply Lp.ext
    have hcoeG : (G.toLp 2 volume : ℝ → ℂ) =ᵐ[volume] g := by
      simpa [G, suzukiComplexTestL2] using
        suzukiComplexTestL2_coeFn g hgdiff hgsupp
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
        exact hgaper (subset_tsupport g hxg)
      rw [hgzero]
  have hwker : w ∈ (suzukiHlogSupportDefect a).ker := by
    rw [LinearMap.mem_ker]
    change (1 - indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1)) (suzukiHlogFourierToTime w) = 0
    rw [htime, sub_apply, one_apply_eq_self, hfix, sub_self]
  refine ⟨⟨w, hwker⟩, ?_⟩
  change suzukiHlogFourierToTime w = suzukiComplexTestL2 g hgdiff hgsupp
  exact htime

/-! ## Realization of arbitrary finite-energy classical Fourier transforms -/

theorem memLp_two_suzukiHlogMeasure_fourier_of_energy
    {f : ℝ → ℂ} (hf1 : Integrable f)
    (henergy : Integrable (fun ξ : ℝ =>
      suzukiLogWeight ξ * ‖𝓕 f ξ‖ ^ 2)) :
    MemLp (𝓕 f) 2 suzukiHlogMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    (GaloisForLFunctions.RHTower.continuous_fourier_of_integrable
      hf1).aestronglyMeasurable).2
  unfold suzukiHlogMeasure
  rw [integrable_withDensity_iff_integrable_smul measurable_suzukiLogWeightNNReal]
  refine henergy.congr ?_
  filter_upwards with ξ
  rw [NNReal.smul_def, smul_eq_mul, coe_suzukiLogWeightNNReal]

def suzukiHlogFourierVector (f : ℝ → ℂ) (hf1 : Integrable f)
    (henergy : Integrable (fun ξ : ℝ =>
      suzukiLogWeight ξ * ‖𝓕 f ξ‖ ^ 2)) : SuzukiHlogFourierL2 :=
  (memLp_two_suzukiHlogMeasure_fourier_of_energy hf1 henergy).toLp (𝓕 f)

theorem suzukiHlogFourierVector_coeFn (f : ℝ → ℂ) (hf1 : Integrable f)
    (henergy : Integrable (fun ξ : ℝ =>
      suzukiLogWeight ξ * ‖𝓕 f ξ‖ ^ 2)) :
    (suzukiHlogFourierVector f hf1 henergy : ℝ → ℂ) =ᵐ[suzukiHlogMeasure]
      𝓕 f :=
  (memLp_two_suzukiHlogMeasure_fourier_of_energy hf1 henergy).coeFn_toLp

theorem norm_sq_suzukiHlogFourierVector (f : ℝ → ℂ) (hf1 : Integrable f)
    (henergy : Integrable (fun ξ : ℝ =>
      suzukiLogWeight ξ * ‖𝓕 f ξ‖ ^ 2)) :
    ‖suzukiHlogFourierVector f hf1 henergy‖ ^ 2 =
      ∫ ξ : ℝ, suzukiLogWeight ξ * ‖𝓕 f ξ‖ ^ 2 := by
  rw [norm_sq_suzukiHlogFourierL2]
  apply MeasureTheory.integral_congr_ae
  have hvolume := (suzukiHlogFourierVector_coeFn f hf1 henergy).filter_mono
    (ae_mono volume_le_suzukiHlogMeasure)
  filter_upwards [hvolume] with ξ hξ
  rw [hξ]

theorem suzukiHlogWeightedToL2_fourierVector_eq
    {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (henergy : Integrable (fun ξ : ℝ =>
      suzukiLogWeight ξ * ‖𝓕 f ξ‖ ^ 2)) :
    suzukiHlogWeightedToL2 (suzukiHlogFourierVector f hf1 henergy) =
      fourierUnitary (hf2.toLp f) := by
  apply Lp.ext
  have hfourierVolume :
      (suzukiHlogFourierVector f hf1 henergy : ℝ → ℂ) =ᵐ[volume] 𝓕 f :=
    (suzukiHlogFourierVector_coeFn f hf1 henergy).filter_mono
      (ae_mono volume_le_suzukiHlogMeasure)
  filter_upwards [suzukiHlogWeightedToL2_coeFn
      (suzukiHlogFourierVector f hf1 henergy), hfourierVolume,
    GaloisForLFunctions.RHTower.coeFn_fourier_toLp hf1 hf2] with ξ hw hv hF
  rw [hw, hv]
  change 𝓕 f ξ = ((𝓕 (hf2.toLp f) : SoninL2) : ℝ → ℂ) ξ
  exact hF.symm

theorem suzukiHlogFourierToTime_fourierVector_eq
    {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (henergy : Integrable (fun ξ : ℝ =>
      suzukiLogWeight ξ * ‖𝓕 f ξ‖ ^ 2)) :
    suzukiHlogFourierToTime (suzukiHlogFourierVector f hf1 henergy) =
      hf2.toLp f := by
  apply fourierUnitary.injective
  rw [fourierUnitary_suzukiHlogFourierToTime,
    suzukiHlogWeightedToL2_fourierVector_eq hf1 hf2 henergy]

def suzukiHlogFormVectorOfFunction
    (a : SuzukiPositiveAperture) (f : ℝ → ℂ) (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ))
    (henergy : Integrable (fun ξ : ℝ =>
      suzukiLogWeight ξ * ‖𝓕 f ξ‖ ^ 2))
    (hfix : (Icc (-a.1) a.1).indicator f = f) : SuzukiHlogFormDomain a :=
  ⟨suzukiHlogFourierVector f hf1 henergy, by
    rw [LinearMap.mem_ker]
    change (1 - indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1))
        (suzukiHlogFourierToTime (suzukiHlogFourierVector f hf1 henergy)) = 0
    rw [suzukiHlogFourierToTime_fourierVector_eq hf1 hf2 henergy,
      sub_apply, one_apply_eq_self, sub_eq_zero]
    apply Lp.ext
    filter_upwards [indicatorCutoff_ae (centralInterval a.1)
        (measurableSet_centralInterval a.1) (hf2.toLp f),
      hf2.coeFn_toLp] with x hcut hcoe
    rw [hcut]
    by_cases hx : x ∈ centralInterval a.1
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hcoe]
      have hx' : x ∉ Icc (-a.1) a.1 := by
        simpa [centralInterval] using hx
      simpa [hx'] using (congrFun hfix x).symm⟩

theorem suzukiHlogFormEmbedding_formVectorOfFunction
    (a : SuzukiPositiveAperture) (f : ℝ → ℂ) (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ))
    (henergy : Integrable (fun ξ : ℝ =>
      suzukiLogWeight ξ * ‖𝓕 f ξ‖ ^ 2))
    (hfix : (Icc (-a.1) a.1).indicator f = f) :
    suzukiHlogFormEmbedding a
        (suzukiHlogFormVectorOfFunction a f hf1 hf2 henergy hfix) =
      hf2.toLp f :=
  suzukiHlogFourierToTime_fourierVector_eq hf1 hf2 henergy

/-! ## Boundary errors and smooth approximants -/

theorem memLp_two_suzukiBoundaryError (a ε κ : ℝ) :
    MemLp (suzukiBoundaryError a ε κ) 2 (volume : Measure ℝ) := by
  have hmeas := (integrable_suzukiBoundaryError a ε κ).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  refine Integrable.mono' (integrable_suzukiBoundaryError a ε κ).norm
    (hmeas.norm.pow 2) ?_
  filter_upwards with x
  have hle := norm_suzukiBoundaryError_le_one a ε κ x
  have hn := norm_nonneg (suzukiBoundaryError a ε κ x)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith

theorem indicator_suzukiBoundaryError (a ε κ : ℝ) :
    (Icc (-a) a).indicator (suzukiBoundaryError a ε κ) =
      suzukiBoundaryError a ε κ := by
  ext x
  by_cases hx : x ∈ Icc (-a) a <;> simp [suzukiBoundaryError, hx]

def suzukiBoundaryErrorFormVector
    (a : SuzukiPositiveAperture) (κ : ℝ) (m : ℕ) : SuzukiHlogFormDomain a :=
  suzukiHlogFormVectorOfFunction a
    (suzukiBoundaryErrorSequence a.1 κ m)
    (integrable_suzukiBoundaryError a.1 (suzukiBoundaryWidth a.1 m) κ)
    (memLp_two_suzukiBoundaryError a.1 (suzukiBoundaryWidth a.1 m) κ)
    (integrable_suzukiBoundaryErrorSequence_hlogEnergy a κ m)
    (indicator_suzukiBoundaryError a.1 (suzukiBoundaryWidth a.1 m) κ)

theorem suzukiHlogFormEmbedding_boundaryErrorFormVector
    (a : SuzukiPositiveAperture) (κ : ℝ) (m : ℕ) :
    suzukiHlogFormEmbedding a (suzukiBoundaryErrorFormVector a κ m) =
      (memLp_two_suzukiBoundaryError a.1 (suzukiBoundaryWidth a.1 m) κ).toLp
        (suzukiBoundaryErrorSequence a.1 κ m) :=
  suzukiHlogFormEmbedding_formVectorOfFunction _ _ _ _ _ _

theorem suzukiHlogFormEmbedding_boundaryErrorFormVector_coeFn
    (a : SuzukiPositiveAperture) (κ : ℝ) (m : ℕ) :
    (suzukiHlogFormEmbedding a (suzukiBoundaryErrorFormVector a κ m) : ℝ → ℂ)
      =ᵐ[volume] suzukiBoundaryErrorSequence a.1 κ m := by
  rw [suzukiHlogFormEmbedding_boundaryErrorFormVector]
  exact (memLp_two_suzukiBoundaryError a.1
    (suzukiBoundaryWidth a.1 m) κ).coeFn_toLp

theorem norm_sq_suzukiBoundaryErrorFormVector
    (a : SuzukiPositiveAperture) (κ : ℝ) (m : ℕ) :
    ‖suzukiBoundaryErrorFormVector a κ m‖ ^ 2 =
      ∫ ξ : ℝ, suzukiLogWeight ξ *
        ‖𝓕 (suzukiBoundaryErrorSequence a.1 κ m) ξ‖ ^ 2 := by
  change ‖suzukiHlogFourierVector
      (suzukiBoundaryErrorSequence a.1 κ m)
      (integrable_suzukiBoundaryError a.1 (suzukiBoundaryWidth a.1 m) κ)
      (integrable_suzukiBoundaryErrorSequence_hlogEnergy a κ m)‖ ^ 2 = _
  exact norm_sq_suzukiHlogFourierVector _ _ _

theorem tendsto_norm_suzukiBoundaryErrorFormVector
    (a : SuzukiPositiveAperture) (κ : ℝ) :
    Tendsto (fun m : ℕ => ‖suzukiBoundaryErrorFormVector a κ m‖)
      atTop (𝓝 0) := by
  have hsquares : Tendsto
      (fun m : ℕ => ‖suzukiBoundaryErrorFormVector a κ m‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [norm_sq_suzukiBoundaryErrorFormVector] using
      tendsto_suzukiBoundaryErrorSequence_hlogEnergy_positiveAperture a κ
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquares
  convert hsqrt using 1
  · funext m
    simp [Function.comp_apply]
  · simp

theorem tsupport_suzukiBoundaryApproximant_subset
    {a ε κ : ℝ} (hε : 0 < ε) :
    tsupport (suzukiBoundaryApproximant a ε κ) ⊆ Icc (-a) a := by
  apply closure_minimal
  · intro x hx
    change suzukiBoundaryApproximant a ε κ x ≠ 0 at hx
    by_contra hxa
    have hout : x ≤ -a ∨ a ≤ x := by
      rw [mem_Icc, not_and_or] at hxa
      exact hxa.imp le_of_not_ge le_of_not_ge
    apply hx
    rcases hout with hout | hout
    · rw [suzukiBoundaryApproximant,
        suzukiBoundaryCutoff_eq_zero_of_le_neg hε hout]
      simp
    · rw [suzukiBoundaryApproximant,
        suzukiBoundaryCutoff_eq_zero_of_aperture_le hε hout]
      simp
  · exact isClosed_Icc

def suzukiBoundaryApproximantFormVector
    (a : SuzukiPositiveAperture) (κ : ℝ) (m : ℕ) : SuzukiHlogFormDomain a :=
  Classical.choose (exists_suzukiHlogFormDomain_eq_smoothComplexTest a
    (suzukiBoundaryApproximant a.1 (suzukiBoundaryWidth a.1 m) κ)
    (contDiff_suzukiBoundaryApproximant a.1 (suzukiBoundaryWidth a.1 m) κ)
    (hasCompactSupport_suzukiBoundaryApproximant
      (suzukiBoundaryWidth_pos a.2 m))
    (tsupport_suzukiBoundaryApproximant_subset
      (suzukiBoundaryWidth_pos a.2 m)))

theorem suzukiHlogFormEmbedding_boundaryApproximantFormVector
    (a : SuzukiPositiveAperture) (κ : ℝ) (m : ℕ) :
    suzukiHlogFormEmbedding a (suzukiBoundaryApproximantFormVector a κ m) =
      suzukiComplexTestL2
        (suzukiBoundaryApproximant a.1 (suzukiBoundaryWidth a.1 m) κ)
        (contDiff_suzukiBoundaryApproximant a.1 (suzukiBoundaryWidth a.1 m) κ)
        (hasCompactSupport_suzukiBoundaryApproximant
          (suzukiBoundaryWidth_pos a.2 m)) :=
  Classical.choose_spec (exists_suzukiHlogFormDomain_eq_smoothComplexTest a
    (suzukiBoundaryApproximant a.1 (suzukiBoundaryWidth a.1 m) κ)
    (contDiff_suzukiBoundaryApproximant a.1 (suzukiBoundaryWidth a.1 m) κ)
    (hasCompactSupport_suzukiBoundaryApproximant
      (suzukiBoundaryWidth_pos a.2 m))
    (tsupport_suzukiBoundaryApproximant_subset
      (suzukiBoundaryWidth_pos a.2 m)))

theorem suzukiHlogFormEmbedding_boundaryApproximantFormVector_coeFn
    (a : SuzukiPositiveAperture) (κ : ℝ) (m : ℕ) :
    (suzukiHlogFormEmbedding a
      (suzukiBoundaryApproximantFormVector a κ m) : ℝ → ℂ) =ᵐ[volume]
        suzukiBoundaryApproximant a.1 (suzukiBoundaryWidth a.1 m) κ := by
  rw [suzukiHlogFormEmbedding_boundaryApproximantFormVector]
  exact suzukiComplexTestL2_coeFn _ _ _

/-! ## Closed, premise-free `H^log` form-core statement for every aperture exponential -/

def suzukiApertureModeFormVector
    (a : SuzukiPositiveAperture) (κ : ℝ) : SuzukiHlogFormDomain a :=
  suzukiBoundaryApproximantFormVector a κ 0 +
    suzukiBoundaryErrorFormVector a κ 0

theorem suzukiHlogFormEmbedding_approximant_add_error_coeFn
    (a : SuzukiPositiveAperture) (κ : ℝ) (m : ℕ) :
    (suzukiHlogFormEmbedding a
      (suzukiBoundaryApproximantFormVector a κ m +
        suzukiBoundaryErrorFormVector a κ m) : ℝ → ℂ) =ᵐ[volume]
      suzukiApertureModeCutoff a.1 κ := by
  rw [map_add]
  filter_upwards [Lp.coeFn_add
      (suzukiHlogFormEmbedding a (suzukiBoundaryApproximantFormVector a κ m))
      (suzukiHlogFormEmbedding a (suzukiBoundaryErrorFormVector a κ m)),
    suzukiHlogFormEmbedding_boundaryApproximantFormVector_coeFn a κ m,
    suzukiHlogFormEmbedding_boundaryErrorFormVector_coeFn a κ m] with x hadd happ herr
  rw [hadd]
  change
    (suzukiHlogFormEmbedding a (suzukiBoundaryApproximantFormVector a κ m) : ℝ → ℂ) x +
      (suzukiHlogFormEmbedding a (suzukiBoundaryErrorFormVector a κ m) : ℝ → ℂ) x =
        suzukiApertureModeCutoff a.1 κ x
  rw [happ, herr]
  calc
    suzukiBoundaryApproximant a.1 (suzukiBoundaryWidth a.1 m) κ x +
        suzukiBoundaryErrorSequence a.1 κ m x =
      suzukiBoundaryErrorSequence a.1 κ m x +
        suzukiBoundaryApproximant a.1 (suzukiBoundaryWidth a.1 m) κ x := add_comm _ _
    _ = suzukiApertureModeCutoff a.1 κ x :=
      (sub_eq_iff_eq_add.mp (congrFun
        (suzukiApertureModeCutoff_sub_approximant
          (suzukiBoundaryWidth_pos a.2 m)) x)).symm

theorem suzukiHlogFormEmbedding_apertureModeFormVector_coeFn
    (a : SuzukiPositiveAperture) (κ : ℝ) :
    (suzukiHlogFormEmbedding a (suzukiApertureModeFormVector a κ) : ℝ → ℂ)
      =ᵐ[volume] suzukiApertureModeCutoff a.1 κ :=
  suzukiHlogFormEmbedding_approximant_add_error_coeFn a κ 0

theorem suzukiApertureModeFormVector_eq_approximant_add_error
    (a : SuzukiPositiveAperture) (κ : ℝ) (m : ℕ) :
    suzukiApertureModeFormVector a κ =
      suzukiBoundaryApproximantFormVector a κ m +
        suzukiBoundaryErrorFormVector a κ m := by
  apply suzukiHlogFormEmbedding_injective a
  apply Lp.ext
  exact (suzukiHlogFormEmbedding_apertureModeFormVector_coeFn a κ).trans
    (suzukiHlogFormEmbedding_approximant_add_error_coeFn a κ m).symm

theorem suzukiApertureModeFormVector_sub_approximant
    (a : SuzukiPositiveAperture) (κ : ℝ) (m : ℕ) :
    suzukiApertureModeFormVector a κ -
      suzukiBoundaryApproximantFormVector a κ m =
        suzukiBoundaryErrorFormVector a κ m := by
  rw [suzukiApertureModeFormVector_eq_approximant_add_error]
  abel

/-- **Suzuki equation (3.2), exact `H^log` form-core content.**  For every positive aperture and
every exponential frequency, the zero-extended mode is a genuine form-domain vector and the
explicit globally smooth tests supported in `[-a,a]` converge to it in the complete form norm. -/
theorem suzukiEquationThreeTwo_hlogFormCore
    (a : SuzukiPositiveAperture) (κ : ℝ) :
    (∀ m : ℕ,
      ContDiff ℝ (⊤ : ℕ∞)
        (suzukiBoundaryApproximant a.1 (suzukiBoundaryWidth a.1 m) κ) ∧
      HasCompactSupport
        (suzukiBoundaryApproximant a.1 (suzukiBoundaryWidth a.1 m) κ) ∧
      tsupport (suzukiBoundaryApproximant a.1 (suzukiBoundaryWidth a.1 m) κ) ⊆
        Icc (-a.1) a.1) ∧
    (suzukiHlogFormEmbedding a (suzukiApertureModeFormVector a κ) : ℝ → ℂ)
      =ᵐ[volume] suzukiApertureModeCutoff a.1 κ ∧
    Tendsto (fun m : ℕ => ‖suzukiApertureModeFormVector a κ -
      suzukiBoundaryApproximantFormVector a κ m‖) atTop (𝓝 0) := by
  refine ⟨fun m => ⟨
      contDiff_suzukiBoundaryApproximant a.1 (suzukiBoundaryWidth a.1 m) κ,
      hasCompactSupport_suzukiBoundaryApproximant (suzukiBoundaryWidth_pos a.2 m),
      tsupport_suzukiBoundaryApproximant_subset (suzukiBoundaryWidth_pos a.2 m)⟩,
    suzukiHlogFormEmbedding_apertureModeFormVector_coeFn a κ, ?_⟩
  simpa only [suzukiApertureModeFormVector_sub_approximant] using
    tendsto_norm_suzukiBoundaryErrorFormVector a κ

end RHTower

end
