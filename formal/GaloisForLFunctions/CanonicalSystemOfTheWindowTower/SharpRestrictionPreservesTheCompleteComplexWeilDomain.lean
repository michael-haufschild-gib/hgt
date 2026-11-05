import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicAndWeilFormDomainsAgree
import GaloisForLFunctions.RHTower.CHMDSharpSpatialCut
import GaloisForLFunctions.RHTower.CHMDRealApertureDomain

/-!
# Sharp restriction preserves the complete complex Weil domain

The two real arithmetic graph coordinates admit exact interval restriction.
Their complex reconstruction therefore admits the literal sharp cut in the
complete target form domain. Both the restricted interval and its complementary
collar retain finite logarithmic energy.
-/

open MeasureTheory Set Filter Complex
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry
open ArithmeticContinuationAndCriticalEnergy
open _root_.RHTower.CHMDDoobGraph

private theorem graphPhysicalSource_sharpInterval (a : SuzukiPositiveAperture)
    (p : SourceGraph) :
    graphPhysicalSource (sharpIntervalGraph (-a.1) a.1 p) =
      indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
        (graphPhysicalSource p) := by
  apply Lp.ext
  have hcut := volume_absolutelyContinuous_mass.ae_le
    (sharpIntervalGraph_source_ae (-a.1) a.1 p)
  filter_upwards [graphPhysicalSource_ae (sharpIntervalGraph (-a.1) a.1 p),
    graphPhysicalSource_ae p, hcut,
    indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1)
      (graphPhysicalSource p), volume.ae_ne a.1] with x hx hp hc hi hne
  rw [hx, hi]
  by_cases hm : x ∈ centralInterval a.1
  · have hm' : x ∈ Ico (-a.1) a.1 := ⟨hm.1, lt_of_le_of_ne hm.2 hne⟩
    rw [indicator_of_mem hm, hp]
    unfold phiDoobTest
    rw [hc, indicator_of_mem hm']
  · have hm' : x ∉ Ico (-a.1) a.1 := fun h => hm ⟨h.1, h.2.le⟩
    rw [indicator_of_notMem hm]
    unfold phiDoobTest
    rw [hc, indicator_of_notMem hm', mul_zero, Complex.ofReal_zero]

/-- Every complete complex aperture source admits literal restriction to any centered interval. -/
theorem exists_ccm_form_of_sharpInterval (a b : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain b) :
    ∃ v : CCMArchimedeanFormDomain a, ccmArchimedeanFormEmbedding a v =
      indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
        (ccmArchimedeanFormEmbedding b u) := by
  obtain ⟨p, r, hu, -⟩ := exists_aperture_graph_pair_preserving_weil b u
  let pc : apertureGraphCompletion a :=
    ⟨sharpIntervalGraph (-a.1) a.1 p.val, sharpIntervalGraph_mem_apertureGraphCompletion a p.val⟩
  let rc : apertureGraphCompletion a :=
    ⟨sharpIntervalGraph (-a.1) a.1 r.val, sharpIntervalGraph_mem_apertureGraphCompletion a r.val⟩
  refine ⟨(apertureGraphWeilEquiv a pc).val + I • (apertureGraphWeilEquiv a rc).val, ?_⟩
  rw [map_add, map_smul, apertureGraphWeilEquiv_physical,
    apertureGraphWeilEquiv_physical, hu, map_add, map_smul]
  change graphPhysicalSource (sharpIntervalGraph (-a.1) a.1 p.val) +
      I • graphPhysicalSource (sharpIntervalGraph (-a.1) a.1 r.val) = _
  rw [graphPhysicalSource_sharpInterval, graphPhysicalSource_sharpInterval]

/-- Sharp interval restriction preserves the complete logarithmic energy of every supported source. -/
theorem hasLogarithmicEnergy_sharpInterval (a b : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert b) (hf : HasLogarithmicEnergy (f : RealLineL2)) :
    HasLogarithmicEnergy (indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1) (f : RealLineL2)) := by
  obtain ⟨u, hu⟩ := exists_ccm_form_of_logarithmicEnergy b f hf
  have he : ccmArchimedeanFormEmbedding b u = (f : RealLineL2) :=
    congrArg (fun v : suzukiApertureHilbert b => (v : RealLineL2)) hu
  obtain ⟨v, hv⟩ := exists_ccm_form_of_sharpInterval a b u
  have hvE := hasLogarithmicEnergy_ccm_form a v
  rwa [hv, he] at hvE

/-- The complementary collar also lies in the full logarithmic form domain. -/
theorem hasLogarithmicEnergy_sharpComplement (a b : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert b) (hf : HasLogarithmicEnergy (f : RealLineL2)) :
    HasLogarithmicEnergy ((f : RealLineL2) - indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1) (f : RealLineL2)) := by
  have hc := hasLogarithmicEnergy_sharpInterval a b f hf
  rw [hasLogarithmicEnergy_iff_range_convolution] at hf hc ⊢
  exact (LinearMap.range logarithmicConvolution.toLinearMap).sub_mem hf hc

private theorem graphPhysicalSource_intervalRestriction (lo hi : ℝ) (p : SourceGraph) :
    graphPhysicalSource (sharpIntervalGraph lo hi p) =
      indicatorCutoff (Ico lo hi) measurableSet_Ico (graphPhysicalSource p) := by
  have hcut := volume_absolutelyContinuous_mass.ae_le (sharpIntervalGraph_source_ae lo hi p)
  apply Lp.ext
  filter_upwards [graphPhysicalSource_ae (sharpIntervalGraph lo hi p), graphPhysicalSource_ae p,
    hcut, indicatorCutoff_ae (Ico lo hi) measurableSet_Ico (graphPhysicalSource p)]
      with x hs hp hc hcut
  rw [hs, hcut]
  by_cases hx : x ∈ Ico lo hi
  · rw [indicator_of_mem hx, hp]
    unfold phiDoobTest
    rw [hc, indicator_of_mem hx]
  · rw [indicator_of_notMem hx]
    unfold phiDoobTest
    rw [hc, indicator_of_notMem hx, mul_zero, Complex.ofReal_zero]

private theorem intervalRestriction_mem_aperture (a : SuzukiPositiveAperture)
    {lo hi : ℝ} (hs : Ico lo hi ⊆ centralInterval a.1) (p : SourceGraph) :
    sharpIntervalGraph lo hi p ∈ apertureGraphCompletion a := by
  apply (mem_apertureGraphCompletion_iff_supported a _).mpr
  apply (graphPhysicalSource_supported_iff a.1 _).mpr
  filter_upwards [sharpIntervalGraph_source_ae lo hi p] with x hx hn
  rw [hx]
  exact indicator_of_notMem (fun hi => hn (hs hi)) _

/-- Any literal bounded interval cut belongs to every enclosing complete complex form domain. -/
theorem exists_ccm_form_of_intervalRestriction (a b : SuzukiPositiveAperture)
    {lo hi : ℝ} (hs : Ico lo hi ⊆ centralInterval a.1) (u : CCMArchimedeanFormDomain b) :
    ∃ v : CCMArchimedeanFormDomain a, ccmArchimedeanFormEmbedding a v =
      indicatorCutoff (Ico lo hi) measurableSet_Ico (ccmArchimedeanFormEmbedding b u) := by
  obtain ⟨p, r, hu, -⟩ := exists_aperture_graph_pair_preserving_weil b u
  let pc : apertureGraphCompletion a :=
    ⟨sharpIntervalGraph lo hi p.val, intervalRestriction_mem_aperture a hs p.val⟩
  let rc : apertureGraphCompletion a :=
    ⟨sharpIntervalGraph lo hi r.val, intervalRestriction_mem_aperture a hs r.val⟩
  refine ⟨(apertureGraphWeilEquiv a pc).val+I • (apertureGraphWeilEquiv a rc).val, ?_⟩
  rw [map_add, map_smul, apertureGraphWeilEquiv_physical,
    apertureGraphWeilEquiv_physical, hu, map_add, map_smul]
  change graphPhysicalSource (sharpIntervalGraph lo hi p.val)+
    I • graphPhysicalSource (sharpIntervalGraph lo hi r.val) = _
  rw [graphPhysicalSource_intervalRestriction, graphPhysicalSource_intervalRestriction]

/-- Arbitrary enclosed interval cuts preserve the exact logarithmic energy domain. -/
theorem hasLogarithmicEnergy_intervalRestriction (a b : SuzukiPositiveAperture)
    {lo hi : ℝ} (hs : Ico lo hi ⊆ centralInterval a.1) (f : suzukiApertureHilbert b)
    (hf : HasLogarithmicEnergy (f : RealLineL2)) :
    HasLogarithmicEnergy (indicatorCutoff (Ico lo hi) measurableSet_Ico (f : RealLineL2)) := by
  obtain ⟨u, hu⟩ := exists_ccm_form_of_logarithmicEnergy b f hf
  have he : ccmArchimedeanFormEmbedding b u = (f : RealLineL2) :=
    congrArg (fun v : suzukiApertureHilbert b => (v : RealLineL2)) hu
  obtain ⟨v, hv⟩ := exists_ccm_form_of_intervalRestriction a b hs u
  have h := hasLogarithmicEnergy_ccm_form a v
  rwa [hv, he] at h

/-- Every complete source splits exactly into its old interval and two sharp collars. -/
theorem exists_ccm_interval_decomposition (a b : SuzukiPositiveAperture)
    (hab : a.1 ≤ b.1) (u : CCMArchimedeanFormDomain b) :
    ∃ p : CCMArchimedeanFormDomain a, ∃ l r : CCMArchimedeanFormDomain b,
      u = r+l+apertureExt hab p ∧
      ccmArchimedeanFormEmbedding a p =
        indicatorCutoff (Ico (-a.1) a.1) measurableSet_Ico (ccmArchimedeanFormEmbedding b u) ∧
      ccmArchimedeanFormEmbedding b l =
        indicatorCutoff (Ico (-b.1) (-a.1)) measurableSet_Ico (ccmArchimedeanFormEmbedding b u) ∧
      ccmArchimedeanFormEmbedding b r =
        indicatorCutoff (Ico a.1 b.1) measurableSet_Ico (ccmArchimedeanFormEmbedding b u) := by
  have hP : Ico (-a.1) a.1 ⊆ centralInterval a.1 := fun _ hx => ⟨hx.1, hx.2.le⟩
  have hPb : Ico (-a.1) a.1 ⊆ centralInterval b.1 := by
    intro x hx
    constructor <;> linarith only [hx.1, hx.2, hab]
  have hL : Ico (-b.1) (-a.1) ⊆ centralInterval b.1 := by
    intro x hx
    exact ⟨hx.1, by linarith only [hx.2, a.property, b.property]⟩
  have hR : Ico a.1 b.1 ⊆ centralInterval b.1 := by
    intro x hx
    exact ⟨by linarith only [hx.1, a.property, b.property], hx.2.le⟩
  obtain ⟨p, hp⟩ := exists_ccm_form_of_intervalRestriction a b hP u
  obtain ⟨l, hl⟩ := exists_ccm_form_of_intervalRestriction b b hL u
  obtain ⟨r, hr⟩ := exists_ccm_form_of_intervalRestriction b b hR u
  refine ⟨p, l, r, ?_, hp, hl, hr⟩
  apply ccmArchimedeanFormToAperture_injective b
  apply Subtype.ext
  change ccmArchimedeanFormEmbedding b u =
    ccmArchimedeanFormEmbedding b (r+l+apertureExt hab p)
  have hext : ccmArchimedeanFormEmbedding b (apertureExt hab p) =
      ccmArchimedeanFormEmbedding a p :=
    ccmArchimedeanFormToAperture_coe_eq_of_val_eq (apertureExt_val hab p)
  rw [map_add, map_add, hext, hp, hl, hr]
  let f := ccmArchimedeanFormEmbedding b u
  let P := indicatorCutoff (Ico (-a.1) a.1) measurableSet_Ico f
  let L := indicatorCutoff (Ico (-b.1) (-a.1)) measurableSet_Ico f
  let R := indicatorCutoff (Ico a.1 b.1) measurableSet_Ico f
  change f = R+L+P
  have hsupport := indicatorCutoff_ae (centralInterval b.1) (measurableSet_centralInterval b.1) f
  have hfix : indicatorCutoff (centralInterval b.1) (measurableSet_centralInterval b.1) f = f :=
    indicatorCutoff_ccmArchimedeanFormEmbedding b u
  rw [hfix] at hsupport
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (R+L) P, Lp.coeFn_add R L,
    indicatorCutoff_ae (Ico (-a.1) a.1) measurableSet_Ico f,
    indicatorCutoff_ae (Ico (-b.1) (-a.1)) measurableSet_Ico f,
    indicatorCutoff_ae (Ico a.1 b.1) measurableSet_Ico f,
    hsupport, volume.ae_ne b.1] with x hsum hrl hp hl hr hs hxb
  rw [hsum, Pi.add_apply, hrl, Pi.add_apply, hp, hl, hr]
  by_cases hx : x ∈ centralInterval b.1
  · have hxb' : x < b.1 := lt_of_le_of_ne hx.2 hxb
    by_cases hxL : x < -a.1
    · have hmL : x ∈ Ico (-b.1) (-a.1) := ⟨hx.1, hxL⟩
      have hnP : x ∉ Ico (-a.1) a.1 := fun h => (not_le.mpr hxL) h.1
      have hnR : x ∉ Ico a.1 b.1 := by
        intro h
        linarith only [h.1, hxL, a.property]
      rw [indicator_of_mem hmL, indicator_of_notMem hnP, indicator_of_notMem hnR,
        zero_add, add_zero]
    · by_cases hxR : a.1 ≤ x
      · have hmR : x ∈ Ico a.1 b.1 := ⟨hxR, hxb'⟩
        have hnP : x ∉ Ico (-a.1) a.1 := fun h => (not_lt.mpr hxR) h.2
        have hnL : x ∉ Ico (-b.1) (-a.1) := fun h => hxL h.2
        rw [indicator_of_mem hmR, indicator_of_notMem hnP, indicator_of_notMem hnL, add_zero, add_zero]
      · have hmP : x ∈ Ico (-a.1) a.1 := ⟨le_of_not_gt hxL, lt_of_not_ge hxR⟩
        have hnL : x ∉ Ico (-b.1) (-a.1) := fun h => hxL h.2
        have hnR : x ∉ Ico a.1 b.1 := fun h => hxR h.1
        rw [indicator_of_mem hmP, indicator_of_notMem hnL, indicator_of_notMem hnR, zero_add, zero_add]
  · have hnP : x ∉ Ico (-a.1) a.1 := fun h => hx (hPb h)
    have hnL : x ∉ Ico (-b.1) (-a.1) := fun h => hx (hL h)
    have hnR : x ∉ Ico a.1 b.1 := fun h => hx (hR h)
    rw [indicator_of_notMem hnP, indicator_of_notMem hnL, indicator_of_notMem hnR, add_zero, add_zero]
    rw [hs, indicator_of_notMem hx]

#print axioms exists_ccm_interval_decomposition
#print axioms exists_ccm_form_of_sharpInterval
#print axioms hasLogarithmicEnergy_sharpInterval
#print axioms hasLogarithmicEnergy_sharpComplement
#print axioms exists_ccm_form_of_intervalRestriction
#print axioms hasLogarithmicEnergy_intervalRestriction
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
