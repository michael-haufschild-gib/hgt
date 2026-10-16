import GaloisForLFunctions.RHTower.CHMDCompactCardinalPairing
import GaloisForLFunctions.RHTower.CHMDCriticalBandReduction

/-!
# Cardinal pairings on the complete original graph

Continuity and the unconditional compact core theorem remove every source
regularity restriction from the mixed pairing. The signed radical therefore
vanishes under every literal cosine sample at an actual Xi zero.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower.CHMDDoobGraph

theorem CardinalGraphFrame.pair_re {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (p : SourceGraph) :
    sourcePair p F.reVector = cardinalOrbitMass a * (graphCosineReadout p a).re := by
  have he : (fun p => sourcePair p F.reVector) =
      (fun p => cardinalOrbitMass a * (graphCosineReadout p a).re) := by
    apply Continuous.ext_on dense_compactTests
      (continuous_sourcePair.comp (continuous_id.prodMk continuous_const))
      (continuous_const.mul (Complex.continuous_re.comp (continuous_graphCosineReadout a)))
    rintro p ⟨v, hv, hc, rfl⟩
    rw [← testLift_phi v hv hc]
    exact (F.compact_pair ha hz (contDiff_phiDoobTest hv) (hasCompactSupport_phiDoobTest hc)).1
  exact congrFun he p

theorem CardinalGraphFrame.pair_im {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (p : SourceGraph) :
    sourcePair p F.imVector = cardinalOrbitMass a * (graphCosineReadout p a).im := by
  have he : (fun p => sourcePair p F.imVector) =
      (fun p => cardinalOrbitMass a * (graphCosineReadout p a).im) := by
    apply Continuous.ext_on dense_compactTests
      (continuous_sourcePair.comp (continuous_id.prodMk continuous_const))
      (continuous_const.mul (Complex.continuous_im.comp (continuous_graphCosineReadout a)))
    rintro p ⟨v, hv, hc, rfl⟩
    rw [← testLift_phi v hv hc]
    exact (F.compact_pair ha hz (contDiff_phiDoobTest hv) (hasCompactSupport_phiDoobTest hc)).2
  exact congrFun he p

theorem CardinalGraphFrame.readout_re {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) {z : ℂ} (hzero : XiC z = 0) :
    graphCosineReadout F.reVector z = cardinalOrbitValue a 1 z := by
  obtain ⟨hs, _, _, he, _⟩ := divisorCardinalSource_regularity ha hz
  rw [graphCosineReadout_of_even_source hs.ofReal_re (fun x => by rw [he x]) F.re_source]
  simpa only [cardinalRealSource, one_mul] using cardinalRealSource_paperFT ha hz 1 hzero

theorem CardinalGraphFrame.readout_im {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) {z : ℂ} (hzero : XiC z = 0) :
    graphCosineReadout F.imVector z = cardinalOrbitValue a (-I) z := by
  obtain ⟨hs, _, _, he, _⟩ := divisorCardinalSource_regularity ha hz
  have hm : ExpMomentSource (fun x => ((divisorCardinalSource a x).im : ℂ)) := by
    simpa [Complex.mul_re] using (hs.const_mul (-I)).ofReal_re
  rw [graphCosineReadout_of_even_source hm (fun x => by rw [he x]) F.im_source]
  simpa [cardinalRealSource, Complex.mul_re] using cardinalRealSource_paperFT ha hz (-I) hzero

theorem CardinalGraphFrame.nonreal_samples {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (hi : a.im ≠ 0) :
    graphCosineReadout F.reVector a = 1/2 ∧ graphCosineReadout F.imVector a = -I/2 := by
  have hA : unsignedOrbitIndicator a a = 1 := by simp [unsignedOrbitIndicator]
  have hB : unsignedOrbitIndicator a (conj a) = 0 := by
    have h := unsignedOrbitIndicators_disjoint ha hi a
    simpa only [hA, one_mul] using h
  rw [F.readout_re ha hz hz, F.readout_im ha hz hz]
  simp [cardinalOrbitValue, hA, hB]

theorem CardinalGraphFrame.real_samples {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (hi : a.im = 0) :
    graphCosineReadout F.reVector a = 1 ∧ graphCosineReadout F.imVector a = 0 := by
  have hc : conj a = a := by apply Complex.ext <;> simp [hi]
  rw [F.readout_re ha hz hz, F.readout_im ha hz hz]
  simp [cardinalOrbitValue, unsignedOrbitIndicator, hc]

theorem CardinalGraphFrame.readouts_outside_orbit {a z : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (hzero : XiC z = 0) (ho : z ∉ cardinalOrbit a) :
    graphCosineReadout F.reVector z = 0 ∧ graphCosineReadout F.imVector z = 0 := by
  rw [F.readout_re ha hz hzero, F.readout_im ha hz hzero]
  exact ⟨cardinalOrbitValue_eq_zero ho, cardinalOrbitValue_eq_zero ho⟩

/-- At a real orbit the null imaginary direction is in the full signed radical. -/
theorem CardinalGraphFrame.real_im_mem_signedRadical {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (hi : a.im = 0) : F.imVector ∈ signedRadical := by
  intro p
  rw [sourcePair_symm, F.pair_im ha hz, graphCosineReadout_real hi, mul_zero]

theorem radical_graphCosineReadout_zero_of_pos {p : SourceGraph} (hp : p ∈ signedRadical)
    {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0) : graphCosineReadout p a = 0 := by
  obtain ⟨F⟩ := exists_cardinalGraphFrame ha hz
  have hR := hp F.reVector
  have hI := hp F.imVector
  rw [F.pair_re ha hz] at hR
  rw [F.pair_im ha hz] at hI
  have hm := (cardinalOrbitMass_pos ha hz).ne'
  apply Complex.ext
  · exact (mul_eq_zero.mp hR).resolve_left hm
  · exact (mul_eq_zero.mp hI).resolve_left hm

/-- Every radical vector has zero even Fourier sample at every centered Xi zero. -/
theorem radical_graphCosineReadout_zero {p : SourceGraph} (hp : p ∈ signedRadical)
    {a : ℂ} (hz : XiC a = 0) : graphCosineReadout p a = 0 := by
  have hn := re_ne_zero_of_XiC_eq_zero hz
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have hza : XiC (-a) = 0 := by rw [XiC_even, hz]
    have h := radical_graphCosineReadout_zero_of_pos hp (a := -a) (by simpa using neg_pos.mpr hneg) hza
    rwa [graphCosineReadout_neg] at h
  · exact radical_graphCosineReadout_zero_of_pos hp hpos hz

end RHTower.CHMDDoobGraph
