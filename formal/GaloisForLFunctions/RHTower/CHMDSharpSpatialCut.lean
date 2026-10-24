import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGammaBoundaryPairing
import GaloisForLFunctions.RHTower.CHMDHarmonicGroundPotentialAndMaximalDomainPrimeShiftForm
import GaloisForLFunctions.RHTower.CHMDStationaryTranslations
import GaloisForLFunctions.RHTower.CHMDSupportedApertureDomain

/-!
# Sharp spatial localization of the full arithmetic graph

The actual Gamma boundary operator controls the singular interaction across
a spatial cut. Its absolute integrability gives sharp-cut domain admission
before the edge-energy identity is integrated. Prime admission holds on
the whole mass space. Translation covariance and the closed graph theorem
give bounds independent of the cut position; every interval restriction
lands in its exact completed aperture domain.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace
noncomputable section
namespace RHTower
open CHMDDoobGraph CHMDClosedJump CHMDPolar
set_option autoImplicit false

private theorem gammaDensity_eq_arch : ccmGammaTranslationDensity = archLevyDensity := by
  funext t
  simp only [ccmGammaTranslationDensity, archLevyDensity, neg_div, neg_mul]

private def boundaryWholeKernel (f g : SuzukiPositiveL2) (p : ℝ × ℝ) : ℂ :=
  (starRingEnd ℂ) (suzukiPositiveZeroExtensionFun g p.1) *
    (ccmGammaTranslationDensity (p.1+p.2):ℂ) * suzukiPositiveZeroExtensionFun f p.2

private theorem integrable_boundaryWholeKernel (f g : SuzukiPositiveL2) :
    Integrable (boundaryWholeKernel f g) (volume.prod volume) := by
  have heq : boundaryWholeKernel f g =
      ((Ioi (0:ℝ)) ×ˢ (Ioi (0:ℝ))).indicator
        (fun p : ℝ × ℝ => (starRingEnd ℂ) (g p.1) *
          (ccmGammaTranslationDensity (p.1+p.2):ℂ) * f p.2) := by
    funext p
    by_cases hs : 0 < p.1 <;> by_cases ht : 0 < p.2 <;>
      simp [boundaryWholeKernel, suzukiPositiveZeroExtensionFun, Set.mem_prod, hs, ht]
  rw [heq, integrable_indicator_iff (measurableSet_Ioi.prod measurableSet_Ioi),
    IntegrableOn, ← Measure.prod_restrict]
  exact integrable_ccmGammaBoundary_pair f g

private theorem zeroExtension_toLp_ae {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi (0:ℝ)))) :
    suzukiPositiveZeroExtensionFun (hf.toLp f) =ᵐ[volume] (Ioi (0:ℝ)).indicator f := by
  have h := (ae_restrict_iff' measurableSet_Ioi).mp hf.coeFn_toLp
  filter_upwards [h] with t ht
  by_cases hp : t ∈ Ioi (0:ℝ)
  · simp only [suzukiPositiveZeroExtensionFun, indicator_of_mem hp, ht hp]
  · simp only [suzukiPositiveZeroExtensionFun, indicator_of_notMem hp]

private theorem crossing_change_preserving (c : ℝ) :
    MeasurePreserving (fun e : ℝ × ℝ => (e.2+e.1-c, c-e.2))
      (volume.prod volume) (volume.prod volume) := by
  have h := (measurePreserving_sub_prod (volume : Measure ℝ) volume).comp
    ((MeasurePreserving.id (volume : Measure ℝ)).prod
      (Measure.measurePreserving_sub_left (volume : Measure ℝ) c))
  convert h using 1
  funext e
  congr 1
  change e.2+e.1-c = e.1-(c-e.2)
  ring

/-- The signed stationary interaction across a cut in the original edge coordinates. -/
def sharpCrossing (c : ℝ) (f : ℝ → ℝ) (e : ℝ × ℝ) : ℝ :=
  if e.2 < c ∧ c < e.2+e.1 then
    archLevyDensity e.1 * f e.2 * f (e.2+e.1) else 0

/-- The actual singular crossing term is absolutely integrable for every
ordinary L2 source, without a jump-domain premise. -/
theorem integrable_sharpCrossing (c : ℝ) {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    Integrable (sharpCrossing c f) archBase := by
  have hc : MemLp (fun x => (f x : ℂ)) 2 volume := hf.ofReal
  have hminus : MemLp (fun t => (f (c-t):ℂ)) 2 (volume.restrict (Ioi (0:ℝ))) :=
    (hc.comp_measurePreserving (Measure.measurePreserving_sub_left volume c)).restrict _
  have hplus : MemLp (fun t => (f (t+c):ℂ)) 2 (volume.restrict (Ioi (0:ℝ))) :=
    (hc.comp_measurePreserving (measurePreserving_add_right volume c)).restrict _
  let u : SuzukiPositiveL2 := hminus.toLp _
  let v : SuzukiPositiveL2 := hplus.toLp _
  have hu := zeroExtension_toLp_ae hminus
  have hv := zeroExtension_toLp_ae hplus
  have hmap := crossing_change_preserving c
  have hleft := hmap.quasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_snd.ae hu)
  have hright := hmap.quasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst.ae hv)
  have hbase := hmap.integrable_comp_of_integrable (integrable_boundaryWholeKernel u v)
  have heq : (fun e : ℝ × ℝ => boundaryWholeKernel u v (e.2+e.1-c, c-e.2)) =ᵐ[
      volume.prod volume] fun e => (sharpCrossing c f e : ℂ) := by
    filter_upwards [hleft, hright] with e hl hr
    change suzukiPositiveZeroExtensionFun u (c-e.2) = _ at hl
    change suzukiPositiveZeroExtensionFun v (e.2+e.1-c) = _ at hr
    dsimp only [boundaryWholeKernel]
    rw [hl, hr]
    have hs : (e.2+e.1-c)+(c-e.2) = e.1 := by ring
    have ht : (e.2+e.1-c)+c = e.2+e.1 := by ring
    rw [hs, gammaDensity_eq_arch]
    by_cases h₁ : e.2 < c <;> by_cases h₂ : c < e.2+e.1 <;>
      simp [sharpCrossing, Set.mem_Ioi, sub_pos, h₁, h₂, sub_sub_cancel, ht,
        Complex.ofReal_mul, mul_comm, mul_left_comm]
  have hreal : Integrable (sharpCrossing c f) (volume.prod volume) := by
    simpa only [RCLike.re_to_complex, Complex.ofReal_re] using (hbase.congr heq).re
  rw [archBase, Measure.restrict_prod_eq_prod_univ]
  exact hreal.restrict

private theorem measurable_stationaryJump {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (stationaryJump f) :=
  (measurable_archLevyDensity.comp measurable_fst).mul ((measurable_difference hf).pow_const 2)

private theorem sharp_split_identity (c : ℝ) (f : ℝ → ℝ) {e : ℝ × ℝ}
    (ht : 0 < e.1) (hr : e.2+e.1 ≠ c) :
    stationaryJump ((Iio c).indicator f) e +
      stationaryJump ((Ici c).indicator f) e =
        stationaryJump f e + 2 * sharpCrossing c f e := by
  by_cases hl : e.2 < c
  · by_cases hrr : e.2+e.1 < c
    · have hn : ¬ c < e.2+e.1 := (not_lt_of_ge hrr.le)
      simp [stationaryJump, difference, left, right, sharpCrossing,
        hl, hrr, not_le_of_gt hl, not_le_of_gt hrr, hn]
    · have hrr' : c < e.2+e.1 := lt_of_le_of_ne (le_of_not_gt hrr) hr.symm
      simp [stationaryJump, difference, left, right, sharpCrossing,
        hl, hrr, not_le_of_gt hl, hrr'.le, hrr']; ring
  · have hll : c ≤ e.2 := le_of_not_gt hl
    have hrr : c ≤ e.2+e.1 := by linarith
    simp [stationaryJump, difference, left, right, sharpCrossing,
      hl, hll, not_lt_of_ge hrr, hrr]

/-- Sharp half-line restriction preserves the complete stationary jump domain. -/
theorem integrable_stationaryJump_indicator_Iio (c : ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (h2 : MemLp f 2 volume)
    (hE : Integrable (stationaryJump f) archBase) :
    Integrable (stationaryJump ((Iio c).indicator f)) archBase := by
  have hcross := integrable_sharpCrossing c h2
  have hsum := hE.add (hcross.const_mul 2)
  apply hsum.mono' (measurable_stationaryJump (hf.indicator measurableSet_Iio)).aestronglyMeasurable
  have ht : ∀ᵐ e ∂archBase, 0 < e.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  have hright : ∀ᵐ e ∂archBase, e.2+e.1 ≠ c := by
    have h := ((Measure.quasiMeasurePreserving_snd.comp
      (measurePreserving_prod_add (volume.restrict (Ioi (0:ℝ))) volume).quasiMeasurePreserving).ae
        (volume.ae_ne c))
    simpa only [archBase, Function.comp_def, add_comm] using h
  filter_upwards [ht, hright] with e he hr
  have hnonneg (g : ℝ → ℝ) : 0 ≤ stationaryJump g e :=
    mul_nonneg (archLevyDensity_pos he).le (sq_nonneg _)
  rw [Real.norm_of_nonneg (hnonneg _)]
  change stationaryJump ((Iio c).indicator f) e ≤ stationaryJump f e + 2 * sharpCrossing c f e
  rw [← sharp_split_identity c f he hr]
  exact le_add_of_nonneg_right (hnonneg _)

/-- Every maximal CHMD source admits its sharp half-line restriction,
including all prime-power edges. -/
theorem memLp_difference_indicator_Iio (c : ℝ) (p : SourceGraph) :
    MemLp (difference ((Iio c).indicator p.val.fst)) 2 edgeMeasure := by
  have hm := (Lp.stronglyMeasurable p.val.fst).measurable
  have h2 : MemLp ((Iio c).indicator p.val.fst) 2 massMeasure :=
    (Lp.memLp p.val.fst).indicator measurableSet_Iio
  apply (memLp_full_difference_iff_stationary (hm.indicator measurableSet_Iio) h2).mpr
  have heq : thetaProduct ((Iio c).indicator p.val.fst) =
      (Iio c).indicator (thetaProduct p.val.fst) := by
    funext x
    by_cases hx : x ∈ Iio c <;> simp [thetaProduct, hx]
  rw [heq]
  exact integrable_stationaryJump_indicator_Iio c (measurable_thetaProduct hm)
    (memLp_thetaProduct hm (Lp.memLp p.val.fst))
    ((memLp_full_difference_iff_stationary hm (Lp.memLp p.val.fst)).mp (full_difference_memLp p))

/-- The literal maximal graph vector obtained by cutting below a spatial point. -/
def sharpLowerGraph (c : ℝ) (p : SourceGraph) : SourceGraph :=
  ofFunction massMeasure edgeMeasure left right nonsingular_left nonsingular_right
    ((Iio c).indicator p.val.fst) ((Lp.memLp p.val.fst).indicator measurableSet_Iio)
    (memLp_difference_indicator_Iio c p)

theorem sharpLowerGraph_source_ae (c : ℝ) (p : SourceGraph) :
    (sharpLowerGraph c p).val.fst =ᵐ[massMeasure] (Iio c).indicator p.val.fst :=
  ((Lp.memLp p.val.fst).indicator measurableSet_Iio).coeFn_toLp


private theorem continuous_linear_of_source
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (S : E →L[ℝ] G) (J : F →L[ℝ] G) (hJ : Function.Injective J)
    (T : E →ₗ[ℝ] F) (hT : ∀ x, J (T x) = S x) : Continuous T := by
  apply LinearMap.continuous_of_isClosed_graph
  have heq : (T.graph : Set (E × F)) = {p | J p.2 = S p.1} := by
    ext p
    change p.2 = T p.1 ↔ J p.2 = S p.1
    rw [← hT p.1]
    exact hJ.eq_iff.symm
  rw [heq]
  exact isClosed_eq (J.continuous.comp continuous_snd) (S.continuous.comp continuous_fst)

private def sharpLowerL2 (μ : Measure ℝ) (c : ℝ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  admittedMultiplier μ μ ((Iio c).indicator fun _ => (1:ℝ))
    (Measure.AbsolutelyContinuous.mk fun _ _ hz => hz) (fun u => by
      have heq : (fun x => (Iio c).indicator (fun _ => (1:ℝ)) x * u x) =
          (Iio c).indicator u := by
        funext x
        by_cases hx : x < c <;> simp [hx]
      rw [heq]
      exact (Lp.memLp u).indicator measurableSet_Iio)

private theorem sharpLowerL2_ae (μ : Measure ℝ) (c : ℝ) (u : Lp ℝ 2 μ) :
    sharpLowerL2 μ c u =ᵐ[μ] (Iio c).indicator u := by
  unfold sharpLowerL2
  refine (admittedMultiplier_ae _ _ _ _ _ u).trans (Eventually.of_forall fun x => ?_)
  by_cases hx : x < c <;> simp [hx]

private theorem norm_sharpLowerL2_le (μ : Measure ℝ) (c : ℝ) (u : Lp ℝ 2 μ) :
    ‖sharpLowerL2 μ c u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [sharpLowerL2_ae μ c u] with x hx
  rw [hx]
  by_cases hc : x < c
  · simp [hc]
  · simp [hc]

private theorem sharpLowerGraph_source (c : ℝ) (p : SourceGraph) :
    sourceMap (sharpLowerGraph c p) = sharpLowerL2 massMeasure c (sourceMap p) :=
  Lp.ext ((sharpLowerGraph_source_ae c p).trans (sharpLowerL2_ae massMeasure c p.val.fst).symm)

private def sharpLowerGraphLM (c : ℝ) : SourceGraph →ₗ[ℝ] SourceGraph where
  toFun := sharpLowerGraph c
  map_add' p q := by
    apply source_projection_injective
    change sourceMap (sharpLowerGraph c (p+q)) = sourceMap (sharpLowerGraph c p + sharpLowerGraph c q)
    simp only [sharpLowerGraph_source, map_add]
  map_smul' t p := by
    apply source_projection_injective
    change sourceMap (sharpLowerGraph c (t • p)) = sourceMap (t • sharpLowerGraph c p)
    simp only [sharpLowerGraph_source, map_smul]

/-- Sharp lower-half-line localization as a bounded operator on the full graph. -/
def sharpLowerGraphCLM (c : ℝ) : SourceGraph →L[ℝ] SourceGraph :=
  ⟨sharpLowerGraphLM c,
    continuous_linear_of_source ((sharpLowerL2 massMeasure c).comp sourceMap) sourceMap
      source_projection_injective (sharpLowerGraphLM c) (sharpLowerGraph_source c)⟩

private theorem stationary_cut_difference (c : ℝ) (p : StationaryVolumeGraph) :
    MemLp (difference ((Iio c).indicator p.val.fst)) 2 stationaryMeasure := by
  have hm := (Lp.stronglyMeasurable p.val.fst).measurable
  have hd : MemLp (difference p.val.fst) 2 stationaryMeasure :=
    (Lp.memLp p.val.snd).ae_eq p.property
  apply (memLp_stationary_difference_iff (hm.indicator measurableSet_Iio)).mpr
  exact integrable_stationaryJump_indicator_Iio c hm (Lp.memLp p.val.fst)
    ((memLp_stationary_difference_iff hm).mp hd)

private def sharpStationaryLower (c : ℝ) (p : StationaryVolumeGraph) : StationaryVolumeGraph :=
  ofFunction volume stationaryMeasure left right nonsingular_stationary_volume_left
    nonsingular_stationary_volume_right ((Iio c).indicator p.val.fst)
    ((Lp.memLp p.val.fst).indicator measurableSet_Iio) (stationary_cut_difference c p)

private theorem sharpStationaryLower_ae (c : ℝ) (p : StationaryVolumeGraph) :
    (sharpStationaryLower c p).val.fst =ᵐ[volume] (Iio c).indicator p.val.fst :=
  ((Lp.memLp p.val.fst).indicator measurableSet_Iio).coeFn_toLp

private theorem sharpStationaryLower_source (c : ℝ) (p : StationaryVolumeGraph) :
    volumeSourceMap (sharpStationaryLower c p) = sharpLowerL2 volume c (volumeSourceMap p) :=
  Lp.ext ((sharpStationaryLower_ae c p).trans (sharpLowerL2_ae volume c p.val.fst).symm)

private def sharpStationaryLowerLM (c : ℝ) : StationaryVolumeGraph →ₗ[ℝ] StationaryVolumeGraph where
  toFun := sharpStationaryLower c
  map_add' p q := by
    apply volumeSourceMap_injective
    simp only [sharpStationaryLower_source, map_add]
  map_smul' t p := by
    apply volumeSourceMap_injective
    simp only [sharpStationaryLower_source, map_smul, RingHom.id_apply]

private def sharpStationaryLowerCLM (c : ℝ) : StationaryVolumeGraph →L[ℝ] StationaryVolumeGraph :=
  ⟨sharpStationaryLowerLM c,
    continuous_linear_of_source ((sharpLowerL2 volume c).comp volumeSourceMap) volumeSourceMap
      volumeSourceMap_injective (sharpStationaryLowerLM c) (sharpStationaryLower_source c)⟩

private theorem norm_volumeGraphTranslate (c : ℝ) (p : StationaryVolumeGraph) :
    ‖volumeGraphTranslate c p‖ = ‖p‖ := by
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
  simpa only [real_inner_self_eq_norm_sq] using volumeGraphTranslate_inner c p p

private theorem sharpStationaryLower_translate (c : ℝ) (p : StationaryVolumeGraph) :
    sharpStationaryLower c p =
      volumeGraphTranslate (-c) (sharpStationaryLower 0 (volumeGraphTranslate c p)) := by
  apply volumeSourceMap_injective
  apply Lp.ext
  have hcut := (measurePreserving_add_right volume (-c)).quasiMeasurePreserving.ae
    (sharpStationaryLower_ae 0 (volumeGraphTranslate c p))
  have htrans := (measurePreserving_add_right volume (-c)).quasiMeasurePreserving.ae
    (volumeTranslate_ae c p.val.fst)
  filter_upwards [sharpStationaryLower_ae c p,
    volumeTranslate_ae (-c) (sharpStationaryLower 0 (volumeGraphTranslate c p)).val.fst,
    hcut, htrans] with x hl hr hc ht
  change (sharpStationaryLower c p).val.fst x =
    volumeTranslate (-c) (sharpStationaryLower 0 (volumeGraphTranslate c p)).val.fst x
  rw [hl, hr]
  change (sharpStationaryLower 0 (volumeGraphTranslate c p)).val.fst (x + -c) = _ at hc
  rw [hc]
  change volumeTranslate c p.val.fst (x + -c) = p.val.fst (x + -c + c) at ht
  by_cases hx : x < c
  · have hx' : x + -c < 0 := by linarith
    simp only [indicator_of_mem (show x ∈ Iio c from hx),
      indicator_of_mem (show x + -c ∈ Iio 0 from hx')]
    change p.val.fst x = volumeTranslate c p.val.fst (x + -c)
    rw [ht]
    congr 1
    ring
  · have hx' : ¬ x + -c < 0 := by linarith
    simp only [indicator_of_notMem (show x ∉ Iio c from hx),
      indicator_of_notMem (show x + -c ∉ Iio 0 from hx')]

private theorem norm_sharpStationaryLower_le (c : ℝ) (p : StationaryVolumeGraph) :
    ‖sharpStationaryLower c p‖ ≤ ‖sharpStationaryLowerCLM 0‖ * ‖p‖ := by
  rw [sharpStationaryLower_translate, norm_volumeGraphTranslate]
  exact (sharpStationaryLowerCLM 0).le_opNorm (volumeGraphTranslate c p) |>.trans_eq
    (by rw [norm_volumeGraphTranslate])

private def physicalStationaryLift (p : SourceGraph) : StationaryVolumeGraph :=
  groundToVolume (fullGroundEquiv p)

private theorem physicalStationaryLift_source (p : SourceGraph) :
    volumeSourceMap (physicalStationaryLift p) = thetaToVolume (sourceMap p) := by
  rw [physicalStationaryLift, groundToVolume_source]
  rw [fullGroundEquiv_source]

private def physicalStationaryLM : SourceGraph →ₗ[ℝ] StationaryVolumeGraph where
  toFun := physicalStationaryLift
  map_add' p q := by
    apply volumeSourceMap_injective
    simp only [physicalStationaryLift_source, map_add]
  map_smul' t p := by
    apply volumeSourceMap_injective
    simp only [physicalStationaryLift_source, map_smul, RingHom.id_apply]

private def physicalStationaryCLM : SourceGraph →L[ℝ] StationaryVolumeGraph :=
  ⟨physicalStationaryLM, continuous_linear_of_source (thetaToVolume.comp sourceMap)
    volumeSourceMap volumeSourceMap_injective physicalStationaryLM physicalStationaryLift_source⟩

private theorem physicalStationaryLift_cut (c : ℝ) (p : SourceGraph) :
    physicalStationaryLift (sharpLowerGraph c p) = sharpStationaryLower c (physicalStationaryLift p) := by
  apply volumeSourceMap_injective
  rw [physicalStationaryLift_source, sharpStationaryLower_source, physicalStationaryLift_source,
    sharpLowerGraph_source]
  apply Lp.ext
  filter_upwards [thetaToVolume_ae (sharpLowerL2 massMeasure c p.val.fst),
    volume_absolutelyContinuous_mass.ae_le (sharpLowerL2_ae massMeasure c p.val.fst),
    sharpLowerL2_ae volume c (thetaToVolume p.val.fst), thetaToVolume_ae p.val.fst]
    with x ht hs hc hp
  change thetaToVolume (sharpLowerL2 massMeasure c p.val.fst) x =
    sharpLowerL2 volume c (thetaToVolume p.val.fst) x
  rw [ht, hc]
  unfold thetaProduct
  rw [hs]
  by_cases hx : x < c
  · simp only [indicator_of_mem (show x ∈ Iio c from hx)]
    exact hp.symm
  · simp only [indicator_of_notMem (show x ∉ Iio c from hx), mul_zero]

private theorem fullGround_norm_le_source_add_physical (p : SourceGraph) :
    ‖fullGroundEquiv p‖ ≤ ‖sourceMap p‖ + ‖physicalStationaryLift p‖ := by
  have hq : ‖fullGroundEquiv p‖ ^ 2 = ‖sourceMap p‖ ^ 2 + ‖(fullGroundEquiv p).val.snd‖ ^ 2 := by
    change ‖(fullGroundEquiv p).val‖ ^ 2 = _
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖stationaryGroundSourceMap (fullGroundEquiv p)‖ ^ 2 + _ = _
    rw [fullGroundEquiv_source]
  have hg : ‖physicalStationaryLift p‖ ^ 2 =
      ‖(physicalStationaryLift p).val.fst‖ ^ 2 + ‖(fullGroundEquiv p).val.snd‖ ^ 2 := by
    change ‖(physicalStationaryLift p).val‖ ^ 2 = _
    exact WithLp.prod_norm_sq_eq_of_L2 _
  have hnon := mul_nonneg (norm_nonneg (sourceMap p)) (norm_nonneg (physicalStationaryLift p))
  nlinarith only [hq, hg, sq_nonneg ‖(physicalStationaryLift p).val.fst‖,
    norm_nonneg (fullGroundEquiv p), norm_nonneg (sourceMap p),
    norm_nonneg (physicalStationaryLift p), hnon]

/-- Sharp cuts have a common full-graph bound, independent of their position.
Translation covariance supplies uniformity in the stationary coordinates. -/
theorem exists_uniform_sharpLowerGraph_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (p : SourceGraph), ‖sharpLowerGraph c p‖ ≤ C * ‖p‖ := by
  let B := ‖fullGroundEquiv.symm.toContinuousLinearMap‖
  let K := ‖sharpStationaryLowerCLM 0‖
  let H := ‖physicalStationaryCLM‖
  refine ⟨B * (1 + K * H), by positivity, ?_⟩
  intro c p
  have hsource : ‖sourceMap (sharpLowerGraph c p)‖ ≤ ‖p‖ := by
    rw [sharpLowerGraph_source]
    exact (norm_sharpLowerL2_le massMeasure c (sourceMap p)).trans (norm_source_le_graph p)
  have hphysical : ‖physicalStationaryLift (sharpLowerGraph c p)‖ ≤ K * H * ‖p‖ := by
    rw [physicalStationaryLift_cut]
    calc
      _ ≤ K * ‖physicalStationaryLift p‖ := norm_sharpStationaryLower_le c _
      _ ≤ K * (H * ‖p‖) := mul_le_mul_of_nonneg_left (physicalStationaryCLM.le_opNorm p)
        (norm_nonneg (sharpStationaryLowerCLM 0))
      _ = _ := by ring
  calc
    ‖sharpLowerGraph c p‖ = ‖fullGroundEquiv.symm (fullGroundEquiv (sharpLowerGraph c p))‖ := by
      rw [fullGroundEquiv.symm_apply_apply]
    _ ≤ B * ‖fullGroundEquiv (sharpLowerGraph c p)‖ := fullGroundEquiv.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ B * (‖sourceMap (sharpLowerGraph c p)‖ + ‖physicalStationaryLift (sharpLowerGraph c p)‖) :=
      mul_le_mul_of_nonneg_left (fullGround_norm_le_source_add_physical _)
        (norm_nonneg fullGroundEquiv.symm.toContinuousLinearMap)
    _ ≤ B * (‖p‖ + K * H * ‖p‖) :=
      mul_le_mul_of_nonneg_left (add_le_add hsource hphysical)
        (norm_nonneg fullGroundEquiv.symm.toContinuousLinearMap)
    _ = _ := by ring

/-- Exact interval localization, retaining the literal full edge differences. -/
def sharpIntervalGraph (lo hi : ℝ) (p : SourceGraph) : SourceGraph :=
  sharpLowerGraph hi (p - sharpLowerGraph lo p)

theorem sharpIntervalGraph_source_ae (lo hi : ℝ) (p : SourceGraph) :
    (sharpIntervalGraph lo hi p).val.fst =ᵐ[massMeasure] (Ico lo hi).indicator p.val.fst := by
  filter_upwards [sharpLowerGraph_source_ae hi (p - sharpLowerGraph lo p),
    sharpLowerGraph_source_ae lo p, Lp.coeFn_sub p.val.fst (sharpLowerGraph lo p).val.fst]
    with x hh hl hs
  change (sharpIntervalGraph lo hi p).val.fst x = _ at hh
  rw [hh]
  by_cases hhi : x < hi
  · rw [indicator_of_mem (show x ∈ Iio hi from hhi)]
    change (p.val.fst - (sharpLowerGraph lo p).val.fst) x = _
    rw [hs, Pi.sub_apply, hl]
    by_cases hlo : x < lo
    · simp [hhi, hlo, not_le_of_gt hlo]
    · simp [hhi, hlo, le_of_not_gt hlo]
  · simp [hhi]

theorem exists_uniform_sharpIntervalGraph_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lo hi : ℝ) (p : SourceGraph),
      ‖sharpIntervalGraph lo hi p‖ ≤ C * ‖p‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_sharpLowerGraph_bound
  refine ⟨C * (1+C), mul_nonneg hC (by linarith), ?_⟩
  intro lo hi p
  calc
    _ ≤ C * ‖p - sharpLowerGraph lo p‖ := hbound hi _
    _ ≤ C * (‖p‖ + ‖sharpLowerGraph lo p‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) hC
    _ ≤ C * (‖p‖ + C * ‖p‖) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (hbound lo p)) hC
    _ = _ := by ring

/-- Sharp localization of every maximal graph vector lies in the exact
completed aperture domain, without a smoothing collar. -/
theorem sharpIntervalGraph_mem_apertureGraphCompletion
    (a : SuzukiPositiveAperture) (p : SourceGraph) :
    sharpIntervalGraph (-a.1) a.1 p ∈ apertureGraphCompletion a := by
  apply (mem_apertureGraphCompletion_iff_supported a _).mpr
  apply (graphPhysicalSource_supported_iff a.1 _).mpr
  filter_upwards [sharpIntervalGraph_source_ae (-a.1) a.1 p] with x hx
  intro hnot
  rw [hx]
  apply indicator_of_notMem
  intro hi
  exact hnot ⟨hi.1, hi.2.le⟩


end RHTower
