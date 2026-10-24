import GaloisForLFunctions.RHTower.CHMDGraphNormIsTheWeilFormNormOnAnAperture
import GaloisForLFunctions.RHTower.CHMDStationaryLocalTransform
import GaloisForLFunctions.RHTower.CHMDFullSpectralNullspace
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCompactL2Fourier
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewCompletionInsideTheWeilFormDomain

/-!
# Fixed apertures in the signed-radical quotient

Compact support separates the source graph from its full signed radical.
Compactness of the restricted Weil form embedding then makes that separation
uniform on each fixed aperture. The resulting quotient norm controls the
original graph norm. The real Weil form completion embeds with closed range,
and the completed embedding preserves the full signed Weil form. Constants
depend on the aperture; positivity of the signed form is not asserted.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace
open GaloisForLFunctions.RHTower

set_option autoImplicit false

noncomputable section
namespace RHTower
open CHMDDoobGraph CHMDPolar

instance realNormedSpace_ccmApertureForm (a : SuzukiPositiveAperture) :
    NormedSpace ℝ (CCMArchimedeanFormDomain a) :=
  Submodule.normedSpace (𝕜 := ℝ) (ccmArchimedeanSupportDefect a).ker

instance realIsBoundedSMul_ccmApertureForm (a : SuzukiPositiveAperture) :
    IsBoundedSMul ℝ (CCMArchimedeanFormDomain a) :=
  @NormedSpace.toIsBoundedSMul ℝ (CCMArchimedeanFormDomain a) _ _
    (realNormedSpace_ccmApertureForm a)

/-- The physical source of a graph vector, in ordinary complex `L²`. -/
def graphPhysicalSource : SourceGraph →L[ℝ] SoninL2 :=
  (Complex.ofRealCLM.compLpL 2 volume).comp (thetaToVolume.comp sourceMap)

theorem graphPhysicalSource_ae (p : SourceGraph) :
    graphPhysicalSource p =ᵐ[volume] fun x => (phiDoobTest p.val.fst x : ℂ) := by
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (p := 2) (μ := volume)
    (thetaToVolume (sourceMap p)), thetaToVolume_ae (sourceMap p)] with x h₁ h₂
  change (Complex.ofRealCLM.compLpL 2 volume (thetaToVolume (sourceMap p))) x = _
  rw [h₁, h₂]
  rfl

theorem graphPhysicalSource_injective : Function.Injective graphPhysicalSource := by
  intro p q hpq
  apply source_projection_injective
  apply thetaToVolume_injective
  apply Lp.ext
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (p := 2) (μ := volume)
    (thetaToVolume (sourceMap p)), Complex.ofRealCLM.coeFn_compLpL (p := 2) (μ := volume)
    (thetaToVolume (sourceMap q))] with x hp hq
  change (graphPhysicalSource p) x = _ at hp
  change (graphPhysicalSource q) x = _ at hq
  rw [hpq, hq] at hp
  exact Complex.ofReal_injective hp.symm

theorem graphPhysicalSource_suzukiCore (a : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore a.1) :
    graphPhysicalSource (suzukiCoreTestLift a u) =
      ccmArchimedeanFormEmbedding a (suzukiRestrictedWeilCoreCCMFormVector a u) := by
  apply Lp.ext
  filter_upwards [graphPhysicalSource_ae (suzukiCoreTestLift a u),
    volume_absolutelyContinuous_mass.ae_le (testLift_source u
      (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) u.hasCompactSupport),
    ccmArchimedeanFormToAperture_suzukiRestrictedWeilCoreCCMFormVector_coeFn a u]
      with x hp hs hu
  rw [hp, phiDoobTest, hs, phiDoobInv, mul_div_cancel₀ _ (riemannKernelReal_pos x).ne']
  exact hu.symm

/-- Compactly supported physical sources cannot lie in the full signed radical.
The Fourier readouts vanish at every Xi zero, so compact-`L²` uniqueness applies. -/
theorem eq_zero_of_signedRadical_of_supported_physicalSource
    {a : ℝ} (ha : 0 ≤ a) {p : SourceGraph} (hp : p ∈ signedRadical)
    (hs : suzukiCutoff a (graphPhysicalSource p) = graphPhysicalSource p) : p = 0 := by
  apply graphPhysicalSource_injective
  rw [map_zero]
  apply eq_zero_of_supported_fourier_constant_on_xiZeros ha hs (c := 0)
  intro z hz
  have hz' : XiC z = 0 := by
    have he : xi (1 / 2 - I * z) = XiC (-z) := by
      change xi (1 / 2 - I * z) = xi (1 / 2 + (-z) * I)
      congr 1
      ring
    rwa [he, XiC_even] at hz
  convert radical_graphFourierReadout_zero hp hz' using 1
  unfold suzukiCompactL2Fourier graphFourierReadout paperFT
  apply integral_congr_ae
  have hfun := congrArg (fun f : SoninL2 => (f : ℝ → ℂ)) hs
  have hcut : (suzukiCutoff a (graphPhysicalSource p) : ℝ → ℂ) =ᵐ[volume]
      fun x => (phiDoobTest p.val.fst x : ℂ) := by
    filter_upwards [graphPhysicalSource_ae p] with x hx
    exact (congrFun hfun x).trans hx
  filter_upwards [hcut] with x hx
  exact congrArg (fun y : ℂ => y * Complex.exp (I * z * (x : ℂ))) hx

/-- The critical projection factors through the mass coordinate. -/
def criticalSourceReconstruction : MassSpace →L[ℝ] SourceGraph :=
  (2 : ℝ) • criticalProjection.comp sourceMap.adjoint

theorem criticalSourceReconstruction_source (p : SourceGraph) :
    criticalSourceReconstruction (sourceMap p) = criticalProjection p := by
  have hsym (u v : SourceGraph) :
      ⟪criticalProjection u, v⟫_ℝ = ⟪u, criticalProjection v⟫_ℝ :=
    signedRadical.inner_starProjection_left_eq_right u v
  apply ext_inner_right ℝ
  intro q
  change ⟪(2 : ℝ) • criticalProjection (sourceMap.adjoint (sourceMap p)), q⟫_ℝ = _
  rw [inner_smul_graph, hsym, ContinuousLinearMap.adjoint_inner_left, hsym]
  calc
    _ = 2 * ⟪sourceMap (criticalProjection q), sourceMap p⟫_ℝ := by rw [real_inner_comm]
    _ = ⟪criticalProjection q, p⟫_ℝ :=
      (radical_inner_eq_two_source (criticalProjection_mem q) p).symm
    _ = ⟪p, criticalProjection q⟫_ℝ := real_inner_comm _ _

/-- Scalar multiplication preserves the strict interior support radius. -/
def suzukiApertureCoreSmul {a : ℝ} (c : ℝ) (u : SuzukiRestrictedWeilCore a) :
    SuzukiRestrictedWeilCore a where
  toFun x := c * u x
  smooth := contDiff_const.mul u.smooth
  supportRadius := u.supportRadius
  supportRadius_nonneg := u.supportRadius_nonneg
  supportRadius_lt_aperture := u.supportRadius_lt_aperture
  support_subset := by
    intro x hx
    apply u.support_subset
    intro hu
    exact hx (by simp only [hu, mul_zero])

theorem suzukiCoreTestLift_smul (a : SuzukiPositiveAperture) (c : ℝ)
    (u : SuzukiRestrictedWeilCore a.1) :
    suzukiCoreTestLift a (suzukiApertureCoreSmul c u) = c • suzukiCoreTestLift a u := by
  apply source_projection_injective
  apply Lp.ext
  filter_upwards [testLift_source (suzukiApertureCoreSmul c u) _ _,
    testLift_source u (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) u.hasCompactSupport,
    Lp.coeFn_smul c (suzukiCoreTestLift a u).val.fst] with x h₁ h₂ h₃
  change _ = (c • (suzukiCoreTestLift a u).val.fst) x
  rw [h₁, h₃, Pi.smul_apply, smul_eq_mul, h₂]
  simp only [phiDoobInv, suzukiApertureCoreSmul]
  ring

/-- Inverse-Doob lifts of the real smooth core on one fixed aperture. -/
def apertureGraphCore (a : SuzukiPositiveAperture) : Submodule ℝ SourceGraph where
  carrier := {p | ∃ u : SuzukiRestrictedWeilCore a.1, p = suzukiCoreTestLift a u}
  zero_mem' := by
    let u : SuzukiRestrictedWeilCore a.1 :=
      ⟨0, contDiff_const, 0, le_rfl, a.property, by simp⟩
    refine ⟨u, ?_⟩
    apply source_projection_injective
    apply Lp.ext
    filter_upwards [testLift_source u
      (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) u.hasCompactSupport,
      Lp.coeFn_zero ℝ 2 massMeasure] with x hu h₀
    change (0 : MassSpace) x = _
    rw [hu, h₀]
    simp [phiDoobInv, u]
  add_mem' := by
    rintro p q ⟨u, rfl⟩ ⟨v, rfl⟩
    refine ⟨suzukiRestrictedWeilCoreAdd u v, ?_⟩
    exact (testLift_add u v _ _ _ _).symm
  smul_mem' := by
    rintro c p ⟨u, rfl⟩
    exact ⟨suzukiApertureCoreSmul c u, (suzukiCoreTestLift_smul a c u).symm⟩

/-- The graph-norm completion of the common real aperture core. -/
def apertureGraphCompletion (a : SuzukiPositiveAperture) : Submodule ℝ SourceGraph :=
  (apertureGraphCore a).topologicalClosure

theorem isClosed_apertureGraphCompletion (a : SuzukiPositiveAperture) :
    IsClosed (apertureGraphCompletion a : Set SourceGraph) := isClosed_closure

instance complete_apertureGraphCompletion (a : SuzukiPositiveAperture) :
    CompleteSpace (apertureGraphCompletion a) :=
  (isClosed_apertureGraphCompletion a).completeSpace_coe

theorem physicalSource_supported_of_mem_apertureGraphCompletion
    (a : SuzukiPositiveAperture) {p : SourceGraph} (hp : p ∈ apertureGraphCompletion a) :
    suzukiCutoff a.1 (graphPhysicalSource p) = graphPhysicalSource p := by
  have hclosed : IsClosed {q : SourceGraph |
      suzukiCutoff a.1 (graphPhysicalSource q) = graphPhysicalSource q} :=
    isClosed_eq ((indicatorCutoff (Icc (-a.1) a.1) measurableSet_Icc).continuous.comp
      graphPhysicalSource.continuous) graphPhysicalSource.continuous
  apply closure_minimal (t := {q : SourceGraph |
      suzukiCutoff a.1 (graphPhysicalSource q) = graphPhysicalSource q}) ?_ hclosed hp
  rintro q ⟨u, rfl⟩
  change suzukiCutoff a.1 (graphPhysicalSource (suzukiCoreTestLift a u)) =
    graphPhysicalSource (suzukiCoreTestLift a u)
  rw [graphPhysicalSource_suzukiCore]
  exact indicatorCutoff_ccmArchimedeanFormEmbedding a _

theorem apertureGraphCompletion_disjoint_signedRadical (a : SuzukiPositiveAperture) :
    Disjoint (apertureGraphCompletion a) signedRadical := by
  rw [Submodule.disjoint_def]
  intro p hp hk
  exact eq_zero_of_signedRadical_of_supported_physicalSource a.property.le hk
    (physicalSource_supported_of_mem_apertureGraphCompletion a hp)

private theorem cutoff_eq_one_on_aperture (a : SuzukiPositiveAperture) {n : ℕ}
    (hn : a.1 ≤ (n : ℝ) + 1) {x : ℝ} (hx : |x| ≤ a.1) : cutoff n x = 1 := by
  apply baseCutoff.one_of_mem_closedBall
  change dist (cutoffScale n * x) 0 ≤ 1
  rw [dist_zero_right, norm_mul, Real.norm_of_nonneg (cutoffScale_pos n).le,
    Real.norm_eq_abs]
  calc
    cutoffScale n * |x| ≤ cutoffScale n * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (hx.trans hn) (cutoffScale_pos n).le
    _ = 1 := inv_mul_cancel₀ (by positivity : (n : ℝ) + 1 ≠ 0)

/-- A single bounded local inverse recovers every source in the fixed aperture. -/
theorem localThetaInverse_graphPhysicalSource_core (a : SuzukiPositiveAperture) {n : ℕ}
    (hn : a.1 ≤ (n : ℝ) + 1) (u : SuzukiRestrictedWeilCore a.1) :
    localThetaInverse n (Complex.reCLM.compLpL 2 volume
      (graphPhysicalSource (suzukiCoreTestLift a u))) = sourceMap (suzukiCoreTestLift a u) := by
  apply Lp.ext
  have hu := ccmArchimedeanFormToAperture_suzukiRestrictedWeilCoreCCMFormVector_coeFn a u
  change ccmArchimedeanFormEmbedding a (suzukiRestrictedWeilCoreCCMFormVector a u)
    =ᵐ[volume] (fun x => (u x : ℂ)) at hu
  rw [← graphPhysicalSource_suzukiCore] at hu
  filter_upwards [localThetaInverse_ae n
      (Complex.reCLM.compLpL 2 volume (graphPhysicalSource (suzukiCoreTestLift a u))),
    (withDensity_absolutelyContinuous volume _).ae_le
      (Complex.reCLM.coeFn_compLpL (p := 2) (μ := volume)
        (graphPhysicalSource (suzukiCoreTestLift a u))),
    (withDensity_absolutelyContinuous volume _).ae_le hu,
    testLift_source u (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) u.hasCompactSupport]
    with x hi hr hf hs
  change _ = (suzukiCoreTestLift a u).val.fst x
  rw [hi, hr, hf, Complex.reCLM_apply, Complex.ofReal_re, hs]
  by_cases hux : u x = 0
  · simp [localThetaInverseFactor, phiDoobInv, hux]
  · have hxa : |x| ≤ a.1 := (abs_lt.mpr (u.support_subset_aperture hux)).le
    rw [localThetaInverseFactor, cutoff_eq_one_on_aperture a hn hxa, one_mul,
      phiDoobInv, div_eq_mul_inv, mul_comm]

/-- A graph-bounded sequence of smooth sources in one aperture has a strongly
convergent subsequence in the weighted mass space. -/
theorem exists_aperture_core_source_subseq (a : SuzukiPositiveAperture)
    (u : ℕ → SuzukiRestrictedWeilCore a.1)
    (hu : ∀ n, ‖suzukiCoreTestLift a (u n)‖ ≤ 1) :
    ∃ w : MassSpace, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => sourceMap (suzukiCoreTestLift a (u (φ n)))) atTop (𝓝 w) := by
  obtain ⟨c, C, hc, _, hcmp⟩ := exists_testLift_norm_sq_equiv_weilFormNorm a
  have hbound (n : ℕ) :
      ‖suzukiRestrictedWeilCoreCCMFormVector a (u n)‖ ≤ Real.sqrt (1 / c) := by
    rw [← Real.sqrt_sq (norm_nonneg (suzukiRestrictedWeilCoreCCMFormVector a (u n)))]
    apply Real.sqrt_le_sqrt
    apply (le_div_iff₀ hc).mpr
    have h := (hcmp (u n)).1
    have hunit := hu n
    have hnonneg := norm_nonneg (suzukiCoreTestLift a (u n))
    nlinarith only [h, hunit, hnonneg]
  obtain ⟨K, hK, hsub⟩ :=
    (isCompactOperator_ccmArchimedeanFormEmbedding a).image_closedBall_subset_compact
      (Real.sqrt (1 / c))
  obtain ⟨f, _, φ, hφ, hf⟩ := hK.tendsto_subseq
    (x := fun n => ccmArchimedeanFormEmbedding a
      (suzukiRestrictedWeilCoreCCMFormVector a (u n)))
    (fun n => hsub ⟨_, by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound n, rfl⟩)
  obtain ⟨N, hN⟩ := exists_nat_gt a.1
  have hNa : a.1 ≤ (N : ℝ) + 1 := by linarith
  let T : SoninL2 →L[ℝ] MassSpace :=
    (localThetaInverse N).comp (Complex.reCLM.compLpL 2 volume)
  refine ⟨T f, φ, hφ, ?_⟩
  have ht := (T.continuous.tendsto f).comp hf
  apply ht.congr
  intro n
  change localThetaInverse N (Complex.reCLM.compLpL 2 volume
    (ccmArchimedeanFormEmbedding a
      (suzukiRestrictedWeilCoreCCMFormVector a (u (φ n))))) = _
  rw [← graphPhysicalSource_suzukiCore, localThetaInverse_graphPhysicalSource_core a hNa]

/-- The quotient norm is bounded below on each real smooth aperture core.
A hypothetical normalized sequence approaching the radical would converge to
a nonzero compactly supported radical vector, contradicting Fourier uniqueness. -/
theorem exists_aperture_quotient_core_lower_bound (a : SuzukiPositiveAperture) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : SuzukiRestrictedWeilCore a.1,
      c * ‖suzukiCoreTestLift a u‖ ≤ ‖signedQuotientMk (suzukiCoreTestLift a u)‖ := by
  by_contra! h
  obtain ⟨ε, _, hεpos, hε⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  choose u hu using fun n => h (ε n) (hεpos n)
  have hnormpos (n : ℕ) : 0 < ‖suzukiCoreTestLift a (u n)‖ := by
    by_contra! hn
    exact not_lt_of_ge (norm_nonneg _)
      ((hu n).trans_le (mul_nonpos_of_nonneg_of_nonpos (hεpos n).le hn))
  let v (n : ℕ) := suzukiApertureCoreSmul ‖suzukiCoreTestLift a (u n)‖⁻¹ (u n)
  have hvnorm (n : ℕ) : ‖suzukiCoreTestLift a (v n)‖ = 1 := by
    dsimp only [v]
    rw [suzukiCoreTestLift_smul, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (hnormpos n).ne']
  have hvquot (n : ℕ) : ‖signedQuotientMk (suzukiCoreTestLift a (v n))‖ < ε n := by
    dsimp only [v]
    rw [suzukiCoreTestLift_smul, norm_signedQuotientMk, map_smul, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), ← norm_signedQuotientMk]
    calc
      _ < ‖suzukiCoreTestLift a (u n)‖⁻¹ *
          (ε n * ‖suzukiCoreTestLift a (u n)‖) :=
        mul_lt_mul_of_pos_left (hu n) (inv_pos.mpr (hnormpos n))
      _ = ε n := by
        rw [mul_left_comm, inv_mul_cancel₀ (hnormpos n).ne', mul_one]
  have hquot : Tendsto (fun n => signedQuotientMk (suzukiCoreTestLift a (v n)))
      atTop (𝓝 0) := squeeze_zero_norm (fun n => (hvquot n).le) hε
  have hred : Tendsto (fun n => reducedSource (suzukiCoreTestLift a (v n)))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) hε
    rw [← norm_signedQuotientMk]
    exact (hvquot n).le
  obtain ⟨w, φ, hφ, hw⟩ := exists_aperture_core_source_subseq a v
    (fun n => (hvnorm n).le)
  let p := criticalSourceReconstruction w
  have hcrit : Tendsto (fun n => criticalProjection (suzukiCoreTestLift a (v (φ n))))
      atTop (𝓝 p) := by
    simpa only [Function.comp_def, criticalSourceReconstruction_source] using
      (criticalSourceReconstruction.continuous.tendsto w).comp hw
  have hp : Tendsto (fun n => suzukiCoreTestLift a (v (φ n))) atTop (𝓝 p) := by
    have hh := hcrit.add (hred.comp hφ.tendsto_atTop)
    convert hh using 1
    · funext n
      change _ = criticalProjection _ + (_ - criticalProjection _)
      abel
    · rw [add_zero]
  have hpc : p ∈ apertureGraphCompletion a :=
    (isClosed_apertureGraphCompletion a).mem_of_tendsto hp
      (Eventually.of_forall fun n => subset_closure ⟨v (φ n), rfl⟩)
  have hpk : p ∈ signedRadical := by
    apply (signedQuotientMk_eq_zero p).mp
    exact tendsto_nhds_unique ((signedQuotientMk.continuous.tendsto p).comp hp)
      (hquot.comp hφ.tendsto_atTop)
  have hpzero : p = 0 := eq_zero_of_signedRadical_of_supported_physicalSource
    a.property.le hpk (physicalSource_supported_of_mem_apertureGraphCompletion a hpc)
  have hpunit : ‖p‖ = 1 := tendsto_nhds_unique hp.norm (by
    simp only [hvnorm]
    exact tendsto_const_nhds)
  rw [hpzero, norm_zero] at hpunit
  exact zero_ne_one hpunit

/-- The fixed-aperture lower quotient bound survives graph completion. -/
theorem exists_aperture_quotient_lower_bound (a : SuzukiPositiveAperture) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ apertureGraphCompletion a,
      c * ‖p‖ ≤ ‖signedQuotientMk p‖ := by
  obtain ⟨c, hc, hcore⟩ := exists_aperture_quotient_core_lower_bound a
  refine ⟨c, hc, fun p hp => ?_⟩
  apply closure_minimal (t := {q : SourceGraph | c * ‖q‖ ≤ ‖signedQuotientMk q‖}) ?_
    (isClosed_le (continuous_const.mul continuous_norm)
      (continuous_norm.comp signedQuotientMk.continuous)) hp
  rintro q ⟨u, rfl⟩
  exact hcore u

/-- The canonical quotient coordinate on the complete real aperture graph. -/
def apertureSignedQuotient (a : SuzukiPositiveAperture) :
    apertureGraphCompletion a →L[ℝ] SignedQuotient :=
  signedQuotientMk.comp (apertureGraphCompletion a).subtypeL

theorem apertureSignedQuotient_antilipschitz (a : SuzukiPositiveAperture) :
    ∃ C : NNReal, AntilipschitzWith C (apertureSignedQuotient a) := by
  apply (antilipschitzWith_iff_exists_mul_le_norm (f := apertureSignedQuotient a)).mpr
  obtain ⟨c, hc, hb⟩ := exists_aperture_quotient_lower_bound a
  exact ⟨c, hc, fun p => hb p p.property⟩

/-- The completed real aperture has a closed, faithfully normed image in the
actual signed-radical quotient. -/
theorem isClosedEmbedding_apertureSignedQuotient (a : SuzukiPositiveAperture) :
    IsClosedEmbedding (apertureSignedQuotient a) := by
  obtain ⟨C, hC⟩ := apertureSignedQuotient_antilipschitz a
  exact hC.isClosedEmbedding (apertureSignedQuotient a).uniformContinuous

theorem apertureSignedQuotient_range_eq_closure (a : SuzukiPositiveAperture) :
    Set.range (apertureSignedQuotient a) =
      closure (signedQuotientMk '' (apertureGraphCore a : Set SourceGraph)) := by
  apply subset_antisymm
  · rintro y ⟨p, rfl⟩
    obtain ⟨u, hu, ht⟩ := mem_closure_iff_seq_limit.mp p.property
    exact mem_closure_of_tendsto ((signedQuotientMk.continuous.tendsto p.val).comp ht)
      (Eventually.of_forall fun n => ⟨u n, hu n, rfl⟩)
  · apply closure_minimal ?_ (isClosedEmbedding_apertureSignedQuotient a).isClosed_range
    rintro y ⟨p, hp, rfl⟩
    exact ⟨⟨p, subset_closure hp⟩, rfl⟩

/-- The actual quotient norm and the real restricted Weil form norm are
equivalent on the common fixed-aperture core. -/
theorem exists_quotient_norm_sq_equiv_weilFormNorm (a : SuzukiPositiveAperture) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u : SuzukiRestrictedWeilCore a.1,
      c * ‖suzukiRestrictedWeilCoreCCMFormVector a u‖ ^ 2 ≤
        ‖suzukiCoreSignedQuotient a u‖ ^ 2 ∧
      ‖suzukiCoreSignedQuotient a u‖ ^ 2 ≤
        C * ‖suzukiRestrictedWeilCoreCCMFormVector a u‖ ^ 2 := by
  obtain ⟨b, hb, hlower⟩ := exists_aperture_quotient_core_lower_bound a
  obtain ⟨c, C, hc, hC, hcmp⟩ := exists_testLift_norm_sq_equiv_weilFormNorm a
  refine ⟨b ^ 2 * c, C, by positivity, hC, fun u => ?_⟩
  have hq : (b * ‖suzukiCoreTestLift a u‖) ^ 2 ≤
      ‖suzukiCoreSignedQuotient a u‖ ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hb.le (norm_nonneg _)) (hlower u) 2
  have hmul := mul_le_mul_of_nonneg_left (hcmp u).1 (sq_nonneg b)
  have hupp : ‖suzukiCoreSignedQuotient a u‖ ^ 2 ≤ ‖suzukiCoreTestLift a u‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (Submodule.Quotient.norm_mk_le signedRadical
      (suzukiCoreTestLift a u)) 2
  constructor
  · nlinarith only [hq, hmul]
  · exact hupp.trans (hcmp u).2

/-- The Weil form coordinate of a smooth graph-core vector. Its definition is
independent of the chosen smooth representative, by the physical embedding. -/
def apertureCoreWeilVector (a : SuzukiPositiveAperture) (p : apertureGraphCore a) :
    CCMArchimedeanFormDomain a :=
  suzukiRestrictedWeilCoreCCMFormVector a (Classical.choose p.property)

theorem apertureCoreWeilVector_embedding (a : SuzukiPositiveAperture)
    (p : apertureGraphCore a) :
    ccmArchimedeanFormEmbedding a (apertureCoreWeilVector a p) = graphPhysicalSource p := by
  rw [apertureCoreWeilVector, ← graphPhysicalSource_suzukiCore,
    ← Classical.choose_spec p.property]

def apertureCoreWeilCoordinate (a : SuzukiPositiveAperture) :
    apertureGraphCore a →ₗ[ℝ] CCMArchimedeanFormDomain a where
  toFun := apertureCoreWeilVector a
  map_add' p q := by
    apply ccmArchimedeanFormEmbedding_injective a
    rw [map_add, apertureCoreWeilVector_embedding, apertureCoreWeilVector_embedding,
      apertureCoreWeilVector_embedding]
    exact graphPhysicalSource.map_add p q
  map_smul' c p := by
    apply ccmArchimedeanFormEmbedding_injective a
    change ccmArchimedeanFormEmbedding a (apertureCoreWeilVector a (c • p)) =
      (ccmArchimedeanFormEmbedding a).restrictScalars ℝ (c • apertureCoreWeilVector a p)
    rw [map_smul, apertureCoreWeilVector_embedding]
    change graphPhysicalSource (c • p.val) =
      c • ccmArchimedeanFormEmbedding a (apertureCoreWeilVector a p)
    rw [apertureCoreWeilVector_embedding, map_smul]

theorem apertureCoreWeilCoordinate_injective (a : SuzukiPositiveAperture) :
    Function.Injective (apertureCoreWeilCoordinate a) := by
  intro p q h
  apply Subtype.ext
  apply graphPhysicalSource_injective
  have hh := congrArg (ccmArchimedeanFormEmbedding a) h
  change ccmArchimedeanFormEmbedding a (apertureCoreWeilVector a p) =
    ccmArchimedeanFormEmbedding a (apertureCoreWeilVector a q) at hh
  simpa only [apertureCoreWeilVector_embedding] using hh

theorem apertureCoreWeilCoordinate_core (a : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore a.1) :
    apertureCoreWeilCoordinate a ⟨suzukiCoreTestLift a u, ⟨u, rfl⟩⟩ =
      suzukiRestrictedWeilCoreCCMFormVector a u := by
  apply ccmArchimedeanFormEmbedding_injective a
  exact (apertureCoreWeilVector_embedding a _).trans (graphPhysicalSource_suzukiCore a u)

/-- The real smooth core inside the archimedean Weil form Hilbert space. -/
def apertureWeilCore (a : SuzukiPositiveAperture) : Submodule ℝ (CCMArchimedeanFormDomain a) :=
  (apertureCoreWeilCoordinate a).range

/-- Completion of the real smooth aperture core in the restricted Weil form norm. -/
def apertureWeilCompletion (a : SuzukiPositiveAperture) :
    Submodule ℝ (CCMArchimedeanFormDomain a) := (apertureWeilCore a).topologicalClosure

instance isBoundedSMul_apertureWeilCompletion (a : SuzukiPositiveAperture) :
    IsBoundedSMul ℝ (apertureWeilCompletion a) :=
  @NormedSpace.toIsBoundedSMul ℝ (apertureWeilCompletion a) _ _
    (Submodule.normedSpace (apertureWeilCompletion a))

instance complete_apertureWeilCompletion (a : SuzukiPositiveAperture) :
    CompleteSpace (apertureWeilCompletion a) :=
  (isClosed_closure : IsClosed (apertureWeilCompletion a : Set (CCMArchimedeanFormDomain a))).completeSpace_coe

def apertureGraphCoreInclusion (a : SuzukiPositiveAperture) :
    apertureGraphCore a →ₗ[ℝ] apertureGraphCompletion a :=
  Submodule.inclusion (apertureGraphCore a).le_topologicalClosure

def apertureWeilCoreInclusion (a : SuzukiPositiveAperture) :
    apertureWeilCore a →ₗ[ℝ] apertureWeilCompletion a :=
  Submodule.inclusion (apertureWeilCore a).le_topologicalClosure

theorem denseRange_apertureGraphCoreInclusion (a : SuzukiPositiveAperture) :
    DenseRange (apertureGraphCoreInclusion a) := by
  change DenseRange (Set.inclusion (apertureGraphCore a).le_topologicalClosure)
  exact (denseRange_inclusion_iff (apertureGraphCore a).le_topologicalClosure).mpr subset_rfl

theorem denseRange_apertureWeilCoreInclusion (a : SuzukiPositiveAperture) :
    DenseRange (apertureWeilCoreInclusion a) := by
  change DenseRange (Set.inclusion (apertureWeilCore a).le_topologicalClosure)
  exact (denseRange_inclusion_iff (apertureWeilCore a).le_topologicalClosure).mpr subset_rfl

theorem exists_aperture_core_norm_comparison (a : SuzukiPositiveAperture) :
    ∃ A B : ℝ, ∀ p : apertureGraphCore a,
      ‖apertureCoreWeilCoordinate a p‖ ≤ A * ‖p‖ ∧
      ‖p‖ ≤ B * ‖apertureCoreWeilCoordinate a p‖ := by
  obtain ⟨c, C, hc, hC, hcmp⟩ := exists_testLift_norm_sq_equiv_weilFormNorm a
  refine ⟨(Real.sqrt c)⁻¹, Real.sqrt C, fun p => ?_⟩
  obtain ⟨u, hu⟩ := p.property
  have hp : p = ⟨suzukiCoreTestLift a u, ⟨u, rfl⟩⟩ := Subtype.ext hu
  rw [hp, apertureCoreWeilCoordinate_core]
  change ‖suzukiRestrictedWeilCoreCCMFormVector a u‖ ≤
      (Real.sqrt c)⁻¹ * ‖suzukiCoreTestLift a u‖ ∧
    ‖suzukiCoreTestLift a u‖ ≤ Real.sqrt C * ‖suzukiRestrictedWeilCoreCCMFormVector a u‖
  have hlo := Real.sqrt_le_sqrt (hcmp u).1
  have hhi := Real.sqrt_le_sqrt (hcmp u).2
  rw [Real.sqrt_mul hc.le, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hlo
  rw [Real.sqrt_mul hC.le, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hhi
  refine ⟨?_, hhi⟩
  calc
    ‖suzukiRestrictedWeilCoreCCMFormVector a u‖ = (Real.sqrt c)⁻¹ *
        (Real.sqrt c * ‖suzukiRestrictedWeilCoreCCMFormVector a u‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr hc).ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlo (inv_nonneg.mpr (Real.sqrt_nonneg c))

def apertureCoreGraphWeilEquiv (a : SuzukiPositiveAperture) :
    apertureGraphCore a ≃ₗ[ℝ] apertureWeilCore a :=
  LinearEquiv.ofInjective (apertureCoreWeilCoordinate a) (apertureCoreWeilCoordinate_injective a)

private theorem apertureCoreGraphWeilEquiv_bounds (a : SuzukiPositiveAperture) :
    (∃ A : ℝ, ∀ p, ‖apertureWeilCoreInclusion a (apertureCoreGraphWeilEquiv a p)‖ ≤
      A * ‖apertureGraphCoreInclusion a p‖) ∧
    (∃ B : ℝ, ∀ q, ‖apertureGraphCoreInclusion a ((apertureCoreGraphWeilEquiv a).symm q)‖ ≤
      B * ‖apertureWeilCoreInclusion a q‖) := by
  obtain ⟨A, B, h⟩ := exists_aperture_core_norm_comparison a
  refine ⟨⟨A, fun p => (h p).1⟩, ⟨B, fun q => ?_⟩⟩
  have hh := (h ((apertureCoreGraphWeilEquiv a).symm q)).2
  change ‖(apertureCoreGraphWeilEquiv a).symm q‖ ≤
    B * ‖apertureCoreGraphWeilEquiv a ((apertureCoreGraphWeilEquiv a).symm q)‖ at hh
  change ‖(apertureCoreGraphWeilEquiv a).symm q‖ ≤ B * ‖q‖
  simpa only [LinearEquiv.apply_symm_apply] using hh

/-- The two completions of the common real core are canonically isomorphic. -/
def apertureGraphWeilEquiv (a : SuzukiPositiveAperture) :
    apertureGraphCompletion a ≃L[ℝ] apertureWeilCompletion a :=
  (apertureCoreGraphWeilEquiv a).extend (apertureGraphCoreInclusion a)
    (apertureWeilCoreInclusion a) (denseRange_apertureGraphCoreInclusion a)
    (apertureCoreGraphWeilEquiv_bounds a).1 (denseRange_apertureWeilCoreInclusion a)
    (apertureCoreGraphWeilEquiv_bounds a).2

theorem apertureGraphWeilEquiv_core (a : SuzukiPositiveAperture) (p : apertureGraphCore a) :
    apertureGraphWeilEquiv a (apertureGraphCoreInclusion a p) =
      apertureWeilCoreInclusion a (apertureCoreGraphWeilEquiv a p) :=
  LinearEquiv.extend_eq _ _ _ _ _ _ _ p

/-- The actual quotient embedding of the complete real Weil form domain. -/
def apertureWeilSignedQuotient (a : SuzukiPositiveAperture) :
    apertureWeilCompletion a →L[ℝ] SignedQuotient :=
  (apertureSignedQuotient a).comp (apertureGraphWeilEquiv a).symm.toContinuousLinearMap

theorem isClosedEmbedding_apertureWeilSignedQuotient (a : SuzukiPositiveAperture) :
    IsClosedEmbedding (apertureWeilSignedQuotient a) :=
  (isClosedEmbedding_apertureSignedQuotient a).comp
    (apertureGraphWeilEquiv a).symm.toHomeomorph.isClosedEmbedding

theorem apertureWeilSignedQuotient_core (a : SuzukiPositiveAperture)
    (p : apertureGraphCore a) :
    apertureWeilSignedQuotient a
      (apertureWeilCoreInclusion a (apertureCoreGraphWeilEquiv a p)) = signedQuotientMk p := by
  rw [← apertureGraphWeilEquiv_core]
  change apertureSignedQuotient a ((apertureGraphWeilEquiv a).symm
    (apertureGraphWeilEquiv a (apertureGraphCoreInclusion a p))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- Completion preserves the full Weil form, including both polar terms. -/
theorem apertureWeilSignedQuotient_weil (a : SuzukiPositiveAperture)
    (q : apertureWeilCompletion a) :
    quotientWeilForm (apertureWeilSignedQuotient a q) =
      (ccmRestrictedWeilForm a q.val q.val).re := by
  have hclosed : IsClosed {q : apertureWeilCompletion a |
      quotientWeilForm (apertureWeilSignedQuotient a q) =
        (ccmRestrictedWeilForm a q.val q.val).re} :=
    isClosed_eq (continuous_quotientWeilForm.comp (apertureWeilSignedQuotient a).continuous)
      ((continuous_re_ccmRestrictedWeilForm_self a).comp continuous_subtype_val)
  apply closure_minimal ?_ hclosed (denseRange_apertureWeilCoreInclusion a q)
  rintro _ ⟨v, rfl⟩
  obtain ⟨p, rfl⟩ := (apertureCoreGraphWeilEquiv a).surjective v
  change quotientWeilForm (apertureWeilSignedQuotient a
    (apertureWeilCoreInclusion a (apertureCoreGraphWeilEquiv a p))) = _
  rw [apertureWeilSignedQuotient_core]
  change quotientWeilForm (signedQuotientMk p.val) =
    (ccmRestrictedWeilForm a (apertureCoreWeilCoordinate a p)
      (apertureCoreWeilCoordinate a p)).re
  obtain ⟨u, hu⟩ := p.property
  have hp : p = ⟨suzukiCoreTestLift a u, ⟨u, rfl⟩⟩ := Subtype.ext hu
  rw [hp, apertureCoreWeilCoordinate_core]
  exact suzukiCoreSignedQuotient_weil a u

end RHTower

