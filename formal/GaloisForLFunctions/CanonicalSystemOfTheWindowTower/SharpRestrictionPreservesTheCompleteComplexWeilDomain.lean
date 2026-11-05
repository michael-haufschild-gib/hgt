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

#print axioms exists_ccm_form_of_sharpInterval
#print axioms hasLogarithmicEnergy_sharpInterval
#print axioms hasLogarithmicEnergy_sharpComplement
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
