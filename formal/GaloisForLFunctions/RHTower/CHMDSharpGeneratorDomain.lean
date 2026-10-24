import GaloisForLFunctions.RHTower.CHMDSharpSpatialCut
import GaloisForLFunctions.RHTower.CHMDCompactSupportOperatorCore

/-!
# Sharp boundaries in the arithmetic generator domain

The singular archimedean boundary defect factors through the actual Gamma
Hankel operator. Adding the bounded prime commutator gives a source-space
operator representing the complete sharp-cut form defect.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace
noncomputable section
namespace RHTower
open CHMDDoobGraph CHMDClosedJump CHMDPolar
set_option autoImplicit false

private theorem norm_soninHalfLine_le (f : SoninL2) : ‖soninHalfLine f‖ ≤ ‖f‖ := by
  rw [soninHalfLine, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

private def halfLineRestriction : SoninL2 →L[ℂ] SuzukiPositiveL2 :=
  LinearMap.mkContinuous
    { toFun := soninHalfLine
      map_add' := fun f g => Lp_toLp_restrict_add f g _
      map_smul' := fun c f => by
        simp only [RingHom.id_apply]
        exact Lp_toLp_restrict_smul c f _ }
    1 (fun f => by
      change ‖soninHalfLine f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using norm_soninHalfLine_le f)

/-- The literal physical source on the complete mass space. -/
def sharpBoundaryPhysical : MassSpace →L[ℝ] SoninL2 :=
  (Complex.ofRealCLM.compLpL 2 volume).comp thetaToVolume

theorem sharpBoundaryPhysical_ae (u : MassSpace) :
    sharpBoundaryPhysical u =ᵐ[volume] fun x => (thetaProduct u x : ℂ) := by
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (p := 2) (μ := volume)
    (thetaToVolume u), thetaToVolume_ae u] with x h₁ h₂
  change Complex.ofRealCLM.compLpL 2 volume (thetaToVolume u) x = _
  rw [h₁, h₂]
  rfl

private def sharpUpperPhysical (c : ℝ) : MassSpace →L[ℝ] SuzukiPositiveL2 :=
  (halfLineRestriction.restrictScalars ℝ).comp
    (((logTranslationCLM c).restrictScalars ℝ).comp sharpBoundaryPhysical)

private def sharpLowerPhysical (c : ℝ) : MassSpace →L[ℝ] SuzukiPositiveL2 :=
  (halfLineRestriction.restrictScalars ℝ).comp
    ((l2Reflection.restrictScalars ℝ).comp
      (((logTranslationCLM c).restrictScalars ℝ).comp sharpBoundaryPhysical))

private theorem sharpUpperPhysical_ae (c : ℝ) (u : MassSpace) :
    sharpUpperPhysical c u =ᵐ[volume.restrict (Ioi (0:ℝ))]
      fun s => (thetaProduct u (s+c) : ℂ) := by
  have ht : logTranslationCLM c (sharpBoundaryPhysical u) =ᵐ[volume]
      fun s => sharpBoundaryPhysical u (s+c) :=
    Lp.coeFn_compMeasurePreserving _ (MellinL2.realTranslation_measurePreserving c)
  have hp := (MellinL2.realTranslation_measurePreserving c).quasiMeasurePreserving.ae_eq_comp
    (sharpBoundaryPhysical_ae u)
  exact (coeFn_soninHalfLine _).trans (ae_restrict_of_ae (ht.trans hp))

private theorem sharpLowerPhysical_ae (c : ℝ) (u : MassSpace) :
    sharpLowerPhysical c u =ᵐ[volume.restrict (Ioi (0:ℝ))]
      fun t => (thetaProduct u (c-t) : ℂ) := by
  have ht : logTranslationCLM c (sharpBoundaryPhysical u) =ᵐ[volume]
      fun s => sharpBoundaryPhysical u (s+c) :=
    Lp.coeFn_compMeasurePreserving _ (MellinL2.realTranslation_measurePreserving c)
  have htr := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp ht
  have hp := ((MellinL2.realTranslation_measurePreserving c).comp
    (Measure.measurePreserving_neg (volume : Measure ℝ))).quasiMeasurePreserving.ae_eq_comp
      (sharpBoundaryPhysical_ae u)
  refine (coeFn_soninHalfLine _).trans (ae_restrict_of_ae ?_)
  filter_upwards [l2Reflection_ae (logTranslationCLM c (sharpBoundaryPhysical u)), htr, hp]
    with t hr ht hp
  change l2Reflection (logTranslationCLM c (sharpBoundaryPhysical u)) t = _
  rw [hr]
  change logTranslationCLM c (sharpBoundaryPhysical u) (-t) =
    sharpBoundaryPhysical u (-t+c) at ht
  rw [ht]
  change sharpBoundaryPhysical u (-t+c) = (thetaProduct u (-t+c):ℂ) at hp
  rw [hp]
  congr 2
  ring

private theorem norm_sharpUpperPhysical_le (c : ℝ) (u : MassSpace) :
    ‖sharpUpperPhysical c u‖ ≤ ‖sharpBoundaryPhysical‖ * ‖u‖ := by
  have h := norm_soninHalfLine_le (logTranslationCLM c (sharpBoundaryPhysical u))
  have ht : ‖logTranslationCLM c (sharpBoundaryPhysical u)‖ = ‖sharpBoundaryPhysical u‖ :=
    (MellinL2.additiveTranslationUnitary c).norm_map (sharpBoundaryPhysical u)
  rw [ht] at h
  exact h.trans (sharpBoundaryPhysical.le_opNorm u)

private theorem norm_sharpLowerPhysical_le (c : ℝ) (u : MassSpace) :
    ‖sharpLowerPhysical c u‖ ≤ ‖sharpBoundaryPhysical‖ * ‖u‖ := by
  have h := norm_soninHalfLine_le (l2Reflection (logTranslationCLM c (sharpBoundaryPhysical u)))
  have hr : ‖l2Reflection (logTranslationCLM c (sharpBoundaryPhysical u))‖ =
      ‖logTranslationCLM c (sharpBoundaryPhysical u)‖ := l2ReflectionIsometry.norm_map _
  have ht : ‖logTranslationCLM c (sharpBoundaryPhysical u)‖ = ‖sharpBoundaryPhysical u‖ :=
    (MellinL2.additiveTranslationUnitary c).norm_map (sharpBoundaryPhysical u)
  rw [hr, ht] at h
  exact h.trans (sharpBoundaryPhysical.le_opNorm u)

private def sharpGammaForward (c : ℝ) : MassSpace →L[ℝ] MassSpace :=
  (sharpLowerPhysical c).adjoint.comp
    ((ccmGammaBoundaryCLM.restrictScalars ℝ).comp (sharpUpperPhysical c))

/-- Bounded skew boundary operator across the literal spatial cut. -/
def sharpGammaCommutator (c : ℝ) : MassSpace →L[ℝ] MassSpace :=
  sharpGammaForward c - (sharpGammaForward c).adjoint

private def boundaryCoordinates (c : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun e := (c-e.2, e.2+e.1-c)
  invFun z := (z.1+z.2, c-z.1)
  left_inv e := by ext <;> dsimp <;> ring
  right_inv z := by ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem boundaryCoordinates_preserving (c : ℝ) :
    MeasurePreserving (boundaryCoordinates c) (volume.prod volume) (volume.prod volume) := by
  have h := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)).comp
    ((measurePreserving_sub_prod (volume : Measure ℝ) volume).comp
      ((MeasurePreserving.id (volume : Measure ℝ)).prod
        (Measure.measurePreserving_sub_left (volume : Measure ℝ) c)))
  convert h using 1
  funext e
  apply Prod.ext
  · rfl
  · change e.2+e.1-c = e.1-(c-e.2)
    ring

private def sharpBoundaryKernel (f g : SuzukiPositiveL2) (z : ℝ × ℝ) : ℂ :=
  (starRingEnd ℂ) (suzukiPositiveZeroExtensionFun g z.1) *
    (ccmGammaTranslationDensity (z.1+z.2):ℂ) * suzukiPositiveZeroExtensionFun f z.2

private theorem sharpBoundaryKernel_indicator (f g : SuzukiPositiveL2) :
    sharpBoundaryKernel f g = ((Ioi (0:ℝ)) ×ˢ Ioi (0:ℝ)).indicator
      (fun z : ℝ × ℝ => (starRingEnd ℂ) (g z.1) *
        (ccmGammaTranslationDensity (z.1+z.2):ℂ) * f z.2) := by
  funext z
  by_cases hs : 0 < z.1 <;> by_cases ht : 0 < z.2 <;>
    simp [sharpBoundaryKernel, suzukiPositiveZeroExtensionFun, Set.mem_prod, hs, ht]

private theorem integrable_sharpBoundaryKernel (f g : SuzukiPositiveL2) :
    Integrable (sharpBoundaryKernel f g) (volume.prod volume) := by
  rw [sharpBoundaryKernel_indicator, integrable_indicator_iff
    (measurableSet_Ioi.prod measurableSet_Ioi), IntegrableOn, ← Measure.prod_restrict]
  exact integrable_ccmGammaBoundary_pair f g

private theorem integral_sharpBoundaryKernel (f g : SuzukiPositiveL2) :
    (∫ z, sharpBoundaryKernel f g z ∂volume.prod volume) =
      inner ℂ g (ccmGammaBoundaryCLM f) := by
  rw [sharpBoundaryKernel_indicator, integral_indicator
    (measurableSet_Ioi.prod measurableSet_Ioi), ← Measure.prod_restrict,
    integral_prod _ (integrable_ccmGammaBoundary_pair f g), inner_ccmGammaBoundaryCLM]

private theorem zeroExtension_congr_ae (g : SuzukiPositiveL2) {f : ℝ → ℂ}
    (h : (g : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0:ℝ))] f) :
    suzukiPositiveZeroExtensionFun g =ᵐ[volume] (Ioi (0:ℝ)).indicator f := by
  have hh := (ae_restrict_iff' measurableSet_Ioi).mp h
  filter_upwards [hh] with t ht
  by_cases hp : t ∈ Ioi (0:ℝ)
  · simp only [suzukiPositiveZeroExtensionFun, indicator_of_mem hp, ht hp]
  · simp only [suzukiPositiveZeroExtensionFun, indicator_of_notMem hp]

/-- One oriented physical interaction across a sharp cut. -/
def sharpBoundaryMixed (c : ℝ) (u v : MassSpace) (e : ℝ × ℝ) : ℝ :=
  if e.2 < c ∧ c < e.2+e.1 then archWeight e * u (e.2+e.1) * v e.2 else 0

private theorem sharpBoundaryKernel_pullback (c : ℝ) (u v : MassSpace) :
    (fun e => sharpBoundaryKernel (sharpUpperPhysical c u) (sharpLowerPhysical c v)
      (boundaryCoordinates c e)) =ᵐ[volume.prod volume]
        fun e => (sharpBoundaryMixed c u v e : ℂ) := by
  have hmap := boundaryCoordinates_preserving c
  have hl := hmap.quasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst.ae
    (zeroExtension_congr_ae _ (sharpLowerPhysical_ae c v)))
  have hr := hmap.quasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_snd.ae
    (zeroExtension_congr_ae _ (sharpUpperPhysical_ae c u)))
  filter_upwards [hl, hr] with e hl hr
  change suzukiPositiveZeroExtensionFun (sharpLowerPhysical c v) (c-e.2) =
    (Ioi (0:ℝ)).indicator (fun t => (thetaProduct v (c-t):ℂ)) (c-e.2) at hl
  change suzukiPositiveZeroExtensionFun (sharpUpperPhysical c u) (e.2+e.1-c) =
    (Ioi (0:ℝ)).indicator (fun s => (thetaProduct u (s+c):ℂ)) (e.2+e.1-c) at hr
  change (starRingEnd ℂ) (suzukiPositiveZeroExtensionFun (sharpLowerPhysical c v) (c-e.2)) *
    (ccmGammaTranslationDensity ((c-e.2)+(e.2+e.1-c)):ℂ) *
      suzukiPositiveZeroExtensionFun (sharpUpperPhysical c u) (e.2+e.1-c) = _
  rw [hl, hr, show (c-e.2)+(e.2+e.1-c)=e.1 by ring]
  have hd : ccmGammaTranslationDensity e.1 = archLevyDensity e.1 := by
    simp only [ccmGammaTranslationDensity, archLevyDensity, neg_div, neg_mul]
  rw [hd]
  by_cases h₁ : e.2 < c <;> by_cases h₂ : c < e.2+e.1 <;>
    simp [sharpBoundaryMixed, Set.mem_Ioi, sub_pos, h₁, h₂, sub_sub_cancel,
      show e.2+e.1-c+c=e.2+e.1 by ring, archWeight, thetaProduct,
      Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]

private theorem integrable_sharpBoundaryMixed_whole (c : ℝ) (u v : MassSpace) :
    Integrable (sharpBoundaryMixed c u v) (volume.prod volume) := by
  have h := (boundaryCoordinates_preserving c).integrable_comp_of_integrable
    (integrable_sharpBoundaryKernel (sharpUpperPhysical c u) (sharpLowerPhysical c v))
  simpa only [RCLike.re_to_complex, Complex.ofReal_re] using
    (h.congr (sharpBoundaryKernel_pullback c u v)).re

theorem integrable_sharpBoundaryMixed (c : ℝ) (u v : MassSpace) :
    Integrable (sharpBoundaryMixed c u v) archBase := by
  rw [archBase, Measure.restrict_prod_eq_prod_univ]
  exact (integrable_sharpBoundaryMixed_whole c u v).restrict

private theorem integral_sharpBoundaryMixed_whole (c : ℝ) (u v : MassSpace) :
    (∫ e, sharpBoundaryMixed c u v e ∂volume.prod volume) =
      (inner ℂ (sharpLowerPhysical c v) (ccmGammaBoundaryCLM (sharpUpperPhysical c u))).re := by
  have h : (∫ e, (sharpBoundaryMixed c u v e : ℂ) ∂volume.prod volume) =
      inner ℂ (sharpLowerPhysical c v) (ccmGammaBoundaryCLM (sharpUpperPhysical c u)) := by
    rw [← integral_sharpBoundaryKernel]
    exact (integral_congr_ae (sharpBoundaryKernel_pullback c u v).symm).trans
      ((boundaryCoordinates_preserving c).integral_comp (boundaryCoordinates c).measurableEmbedding _)
  rw [integral_complex_ofReal] at h
  exact congrArg Complex.re h

private theorem integral_sharpBoundaryMixed_eq_whole (c : ℝ) (u v : MassSpace) :
    (∫ e, sharpBoundaryMixed c u v e ∂archBase) =
      ∫ e, sharpBoundaryMixed c u v e ∂volume.prod volume := by
  rw [archBase, Measure.restrict_prod_eq_prod_univ, ← integral_indicator
    (measurableSet_Ioi.prod MeasurableSet.univ)]
  apply integral_congr_ae
  filter_upwards [] with e
  by_cases he : 0 < e.1
  · have he' : e ∈ Ioi (0:ℝ) ×ˢ (univ : Set ℝ) := ⟨he, mem_univ _⟩
    exact indicator_of_mem he' _
  · rw [indicator_of_notMem (show e ∉ Ioi (0:ℝ) ×ˢ univ from fun h => he h.1)]
    have hn : ¬ (e.2 < c ∧ c < e.2+e.1) := by intro h; linarith [h.1, h.2]
    simp only [sharpBoundaryMixed, if_neg hn]

private theorem real_inner_positiveL2 (f g : SuzukiPositiveL2) :
    inner ℝ f g = (inner ℂ f g).re := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x in Ioi (0:ℝ), (inner ℂ (f x) (g x)).re := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact real_inner_eq_re_inner (𝕜 := ℂ) (f x) (g x)
    _ = _ := integral_re (L2.integrable_inner (𝕜 := ℂ) f g)

private theorem sharpGammaForward_inner (c : ℝ) (u v : MassSpace) :
    ⟪sharpGammaForward c u, v⟫_ℝ = ∫ e, sharpBoundaryMixed c u v e ∂archBase := by
  change ⟪(sharpLowerPhysical c).adjoint
    (ccmGammaBoundaryCLM (sharpUpperPhysical c u)), v⟫_ℝ = _
  rw [(sharpLowerPhysical c).adjoint_inner_left, real_inner_comm, real_inner_positiveL2,
    integral_sharpBoundaryMixed_eq_whole, integral_sharpBoundaryMixed_whole]

theorem sharpGammaCommutator_inner (c : ℝ) (u v : MassSpace) :
    ⟪sharpGammaCommutator c u, v⟫_ℝ =
      ∫ e, sharpBoundaryMixed c u v e - sharpBoundaryMixed c v u e ∂archBase := by
  change ⟪sharpGammaForward c u - (sharpGammaForward c).adjoint u, v⟫_ℝ = _
  rw [inner_sub_left, (sharpGammaForward c).adjoint_inner_left]
  have hc : ⟪u, sharpGammaForward c v⟫_ℝ = ⟪sharpGammaForward c v, u⟫_ℝ :=
    real_inner_comm _ _
  rw [hc, sharpGammaForward_inner, sharpGammaForward_inner,
    integral_sub (integrable_sharpBoundaryMixed c u v) (integrable_sharpBoundaryMixed c v u)]


/-- Half-line multiplication on the actual theta--cosh mass space. -/
def sharpMassCutoff (c : ℝ) : MassSpace →L[ℝ] MassSpace :=
  admittedMultiplier massMeasure massMeasure ((Iio c).indicator fun _ => (1:ℝ))
    (Measure.AbsolutelyContinuous.mk fun _ _ hz => hz) (fun u => by
      have heq : (fun x => (Iio c).indicator (fun _ => (1:ℝ)) x * u x) =
          (Iio c).indicator u := by
        funext x
        by_cases hx : x < c <;> simp [hx]
      rw [heq]
      exact (Lp.memLp u).indicator measurableSet_Iio)

theorem sharpMassCutoff_ae (c : ℝ) (u : MassSpace) :
    sharpMassCutoff c u =ᵐ[massMeasure] (Iio c).indicator u := by
  unfold sharpMassCutoff
  refine (admittedMultiplier_ae _ _ _ _ _ u).trans (Eventually.of_forall fun x => ?_)
  by_cases hx : x < c <;> simp [hx]

theorem norm_sharpMassCutoff_le (c : ℝ) (u : MassSpace) :
    ‖sharpMassCutoff c u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [sharpMassCutoff_ae c u] with x hx
  rw [hx]
  by_cases hc : x < c <;> simp [hc]

theorem sharpMassCutoff_symmetric (c : ℝ) (u v : MassSpace) :
    ⟪sharpMassCutoff c u, v⟫_ℝ = ⟪u, sharpMassCutoff c v⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sharpMassCutoff_ae c u, sharpMassCutoff_ae c v] with x hu hv
  rw [hu, hv]
  by_cases hx : x < c <;> simp [hx]

theorem sharpLowerGraph_sourceMap (c : ℝ) (p : SourceGraph) :
    sourceMap (sharpLowerGraph c p) = sharpMassCutoff c (sourceMap p) :=
  Lp.ext ((sharpLowerGraph_source_ae c p).trans (sharpMassCutoff_ae c p.val.fst).symm)

private theorem archEdge_ae (p : SourceGraph) :
    (graphArchEquiv p).val.snd =ᵐ[archMeasure] difference p.val.fst := by
  have h := (graphArchEquiv p).property
  change (graphArchEquiv p).val.snd =ᵐ[archMeasure]
    difference (graphArchEquiv p).val.fst at h
  rw [graphArchEquiv_source] at h
  exact h

private theorem sharpLower_archEdge_ae (c : ℝ) (p : SourceGraph) :
    (graphArchEquiv (sharpLowerGraph c p)).val.snd =ᵐ[archMeasure]
      difference ((Iio c).indicator p.val.fst) := by
  have hl := nonsingular_arch_left.ae_eq_comp (sharpLowerGraph_source_ae c p)
  have hr := nonsingular_arch_right.ae_eq_comp (sharpLowerGraph_source_ae c p)
  filter_upwards [archEdge_ae (sharpLowerGraph c p), hl, hr] with e he hl hr
  simp only [Function.comp_apply] at hl hr
  rw [he]
  change (sharpLowerGraph c p).val.fst (left e) - (sharpLowerGraph c p).val.fst (right e) = _
  rw [hl, hr]
  rfl

private theorem sharp_arch_edge_pairing (c : ℝ) (p q : SourceGraph) :
    ⟪(graphArchEquiv (sharpLowerGraph c p)).val.snd, (graphArchEquiv q).val.snd⟫_ℝ -
      ⟪(graphArchEquiv p).val.snd, (graphArchEquiv (sharpLowerGraph c q)).val.snd⟫_ℝ =
        ⟪sharpGammaCommutator c (sourceMap p), sourceMap q⟫_ℝ := by
  rw [cutoff_inner_realLp, cutoff_inner_realLp,
    ← integral_sub (cutoff_integrable_mul _ _) (cutoff_integrable_mul _ _)]
  have heq :
      (∫ e, (graphArchEquiv (sharpLowerGraph c p)).val.snd e * (graphArchEquiv q).val.snd e -
        (graphArchEquiv p).val.snd e * (graphArchEquiv (sharpLowerGraph c q)).val.snd e
          ∂archMeasure) =
      ∫ e, difference ((Iio c).indicator p.val.fst) e * difference q.val.fst e -
        difference p.val.fst e * difference ((Iio c).indicator q.val.fst) e ∂archMeasure := by
    apply integral_congr_ae
    filter_upwards [sharpLower_archEdge_ae c p, archEdge_ae q,
      archEdge_ae p, sharpLower_archEdge_ae c q] with e hp hq hp' hq'
    rw [hp, hq, hp', hq']
  rw [heq, archMeasure, integral_weighted archBase measurable_archWeight archWeight_nonneg_ae,
    sharpGammaCommutator_inner]
  have ht : ∀ᵐ e ∂archBase, 0 < e.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  have hright : ∀ᵐ e ∂archBase, e.2+e.1 ≠ c := by
    have h := ((Measure.quasiMeasurePreserving_snd.comp
      (measurePreserving_prod_add (volume.restrict (Ioi (0:ℝ))) volume).quasiMeasurePreserving).ae
        (volume.ae_ne c))
    simpa only [archBase, Function.comp_def, add_comm] using h
  apply integral_congr_ae
  filter_upwards [ht, hright] with e ht hr
  change archWeight e * (difference ((Iio c).indicator p.val.fst) e * difference q.val.fst e -
    difference p.val.fst e * difference ((Iio c).indicator q.val.fst) e) =
      sharpBoundaryMixed c p.val.fst q.val.fst e - sharpBoundaryMixed c q.val.fst p.val.fst e
  by_cases hl : e.2 < c
  · by_cases hrr : e.2+e.1 < c
    · have hn : ¬ c < e.2+e.1 := not_lt_of_ge hrr.le
      simp [difference, left, right, sharpBoundaryMixed, hl, hrr, hn]
    · have hrr' : c < e.2+e.1 := lt_of_le_of_ne (le_of_not_gt hrr) hr.symm
      simp [difference, left, right, sharpBoundaryMixed, hl, hrr, hrr']; ring
  · have hrr : c ≤ e.2+e.1 := by linarith
    simp [difference, left, right, sharpBoundaryMixed, hl, not_lt_of_ge hrr]

/-- The complete sharp-boundary forcing, retaining every prime-power line. -/
def sharpFullCommutator (c : ℝ) : MassSpace →L[ℝ] MassSpace :=
  sharpGammaCommutator c + primeGenerator.comp (sharpMassCutoff c) -
    (sharpMassCutoff c).comp primeGenerator

private theorem sharpFullCommutator_inner (c : ℝ) (u v : MassSpace) :
    ⟪sharpFullCommutator c u, v⟫_ℝ = ⟪sharpGammaCommutator c u, v⟫_ℝ +
      ⟪primeGenerator (sharpMassCutoff c u), v⟫_ℝ -
        ⟪primeGenerator u, sharpMassCutoff c v⟫_ℝ := by
  change ⟪sharpGammaCommutator c u + primeGenerator (sharpMassCutoff c u) -
    sharpMassCutoff c (primeGenerator u), v⟫_ℝ = _
  rw [inner_sub_left, inner_add_left, sharpMassCutoff_symmetric]

/-- The complete form defect factors through the actual source Hilbert space. -/
theorem sharpLowerGraph_pairing (c : ℝ) (p q : SourceGraph) :
    ⟪sharpLowerGraph c p, q⟫_ℝ - ⟪p, sharpLowerGraph c q⟫_ℝ =
      ⟪sharpFullCommutator c (sourceMap p), sourceMap q⟫_ℝ := by
  rw [full_graph_inner_decomposition, full_graph_inner_decomposition,
    arch_graph_inner, arch_graph_inner]
  have hp (r : SourceGraph) : archSourceMap (graphArchEquiv r) = sourceMap r :=
    graphArchEquiv_source r
  simp only [hp, sharpLowerGraph_sourceMap]
  rw [sharpMassCutoff_symmetric, sharpFullCommutator_inner]
  linarith [sharp_arch_edge_pairing c p q]

theorem rieszLift_sharpLower (c : ℝ) (w : MassSpace) :
    rieszLift (sharpMassCutoff c w + sharpFullCommutator c (resolvent w)) =
      sharpLowerGraph c (rieszLift w) := by
  apply rieszLift_unique
  intro q
  have h := sharpLowerGraph_pairing c (rieszLift w) q
  rw [inner_rieszLift] at h
  have hq : (sharpLowerGraph c q).val.fst = sharpMassCutoff c q.val.fst :=
    sharpLowerGraph_sourceMap c q
  rw [hq, ← sharpMassCutoff_symmetric] at h
  change ⟪sharpLowerGraph c (rieszLift w), q⟫_ℝ - ⟪sharpMassCutoff c w, q.val.fst⟫_ℝ =
    ⟪sharpFullCommutator c (resolvent w), q.val.fst⟫_ℝ at h
  rw [inner_add_left]
  linarith

theorem resolvent_sharpLower (c : ℝ) (w : MassSpace) :
    resolvent (sharpMassCutoff c w + sharpFullCommutator c (resolvent w)) =
      sharpMassCutoff c (resolvent w) := by
  have h := congrArg sourceMap (rieszLift_sharpLower c w)
  rw [sharpLowerGraph_sourceMap] at h
  exact h

/-- Literal half-line restriction preserves the actual arithmetic operator domain. -/
theorem sharpMassCutoff_mem_arithmeticGenerator_domain
    (c : ℝ) (u : arithmeticGenerator.domain) :
    sharpMassCutoff c u ∈ arithmeticGenerator.domain := by
  refine ⟨sharpMassCutoff c ((u : MassSpace) + arithmeticGenerator u) +
    sharpFullCommutator c u, ?_⟩
  have h := resolvent_sharpLower c ((u : MassSpace) + arithmeticGenerator u)
  rwa [arithmeticGenerator_identity] at h

def arithmeticGeneratorSharpCut (c : ℝ) (u : arithmeticGenerator.domain) :
    arithmeticGenerator.domain :=
  ⟨sharpMassCutoff c u, sharpMassCutoff_mem_arithmeticGenerator_domain c u⟩

/-- Exact localized generator equation with the constructed bounded boundary forcing. -/
theorem arithmeticGeneratorSharpCut_apply (c : ℝ) (u : arithmeticGenerator.domain) :
    arithmeticGenerator (arithmeticGeneratorSharpCut c u) =
      sharpMassCutoff c (arithmeticGenerator u) + sharpFullCommutator c u := by
  have h1 := arithmeticGenerator_identity (arithmeticGeneratorSharpCut c u)
  have h2 := resolvent_sharpLower c ((u : MassSpace) + arithmeticGenerator u)
  rw [arithmeticGenerator_identity] at h2
  have h := resolvent_injective (h1.trans h2.symm)
  change sharpMassCutoff c u + arithmeticGenerator (arithmeticGeneratorSharpCut c u) =
    sharpMassCutoff c ((u : MassSpace) + arithmeticGenerator u) + sharpFullCommutator c u at h
  rw [map_add, add_assoc] at h
  exact add_left_cancel h

theorem sharpGammaCommutator_adjoint (c : ℝ) :
    (sharpGammaCommutator c).adjoint = -sharpGammaCommutator c := by
  unfold sharpGammaCommutator
  rw [map_sub, ContinuousLinearMap.adjoint_adjoint]
  abel

theorem sharpFullCommutator_adjoint (c : ℝ) :
    (sharpFullCommutator c).adjoint = -sharpFullCommutator c := by
  have hP : (sharpMassCutoff c).adjoint = sharpMassCutoff c :=
    (show (sharpMassCutoff c).IsSymmetric from sharpMassCutoff_symmetric c).clm_adjoint_eq
  have hG : primeGenerator.adjoint = primeGenerator := primeGenerator_isSelfAdjoint.adjoint_eq
  unfold sharpFullCommutator
  rw [map_sub, map_add, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    sharpGammaCommutator_adjoint, hP, hG]
  abel

private theorem exists_uniform_sharpGammaCommutator_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, ‖sharpGammaCommutator c‖ ≤ C := by
  let M := ‖sharpBoundaryPhysical‖
  let K := ccmGammaBoundaryCLM.restrictScalars ℝ
  have hm (c : ℝ) : ‖sharpLowerPhysical c‖ ≤ M :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg sharpBoundaryPhysical)
      (norm_sharpLowerPhysical_le c)
  have hf (c : ℝ) : ‖sharpGammaForward c‖ ≤ M * (‖K‖ * M) := by
    apply ContinuousLinearMap.opNorm_le_bound (sharpGammaForward c) (by positivity)
    intro u
    change ‖(sharpLowerPhysical c).adjoint (K (sharpUpperPhysical c u))‖ ≤ _
    calc
      _ ≤ ‖(sharpLowerPhysical c).adjoint‖ * ‖K (sharpUpperPhysical c u)‖ :=
        (sharpLowerPhysical c).adjoint.le_opNorm _
      _ = ‖sharpLowerPhysical c‖ * ‖K (sharpUpperPhysical c u)‖ := by
        rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ M * (‖K‖ * (M * ‖u‖)) :=
        mul_le_mul (hm c)
          ((K.le_opNorm _).trans (mul_le_mul_of_nonneg_left
            (norm_sharpUpperPhysical_le c u) (norm_nonneg K)))
          (norm_nonneg _) (norm_nonneg sharpBoundaryPhysical)
      _ = _ := by ring
  refine ⟨2 * (M * (‖K‖ * M)), by positivity, fun c => ?_⟩
  change ‖sharpGammaForward c - (sharpGammaForward c).adjoint‖ ≤ _
  calc
    _ ≤ ‖sharpGammaForward c‖ + ‖(sharpGammaForward c).adjoint‖ := norm_sub_le _ _
    _ = 2 * ‖sharpGammaForward c‖ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hf c) (by norm_num)

/-- A single source-space commutator bound works for every cut location. -/
theorem exists_uniform_sharpFullCommutator_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, ‖sharpFullCommutator c‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_sharpGammaCommutator_bound
  refine ⟨C + 2 * ‖primeGenerator‖, by positivity, fun c => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound (sharpFullCommutator c) (by positivity)
  intro u
  have hgamma : ‖sharpGammaCommutator c u‖ ≤ C * ‖u‖ :=
    ((sharpGammaCommutator c).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (hb c) (norm_nonneg u))
  have hp : ‖primeGenerator (sharpMassCutoff c u)‖ ≤ ‖primeGenerator‖ * ‖u‖ :=
    (primeGenerator.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (norm_sharpMassCutoff_le c u) (norm_nonneg primeGenerator))
  have hq : ‖sharpMassCutoff c (primeGenerator u)‖ ≤ ‖primeGenerator‖ * ‖u‖ :=
    (norm_sharpMassCutoff_le c _).trans (primeGenerator.le_opNorm u)
  change ‖sharpGammaCommutator c u + primeGenerator (sharpMassCutoff c u) -
    sharpMassCutoff c (primeGenerator u)‖ ≤ _
  calc
    _ ≤ ‖sharpGammaCommutator c u + primeGenerator (sharpMassCutoff c u)‖ +
        ‖sharpMassCutoff c (primeGenerator u)‖ := norm_sub_le _ _
    _ ≤ (‖sharpGammaCommutator c u‖ + ‖primeGenerator (sharpMassCutoff c u)‖) +
        ‖sharpMassCutoff c (primeGenerator u)‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (C * ‖u‖ + ‖primeGenerator‖ * ‖u‖) + ‖primeGenerator‖ * ‖u‖ :=
      add_le_add (add_le_add hgamma hp) hq
    _ = _ := by ring


end RHTower
