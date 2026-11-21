import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.CircularArcRange

/-!
# Two anchors for a covering arc

Distinct anchors for the same enclosure must be separated by at least the
complementary length in both directions. At such a separation their two
excluded arcs are disjoint, so the permitted intersection has constant
Haar length.
-/

open MeasureTheory Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance pairGeometryCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

private def phaseTurn (z : UnitAddCircle) : ℝ := (AddCircle.equivIco (1 : ℝ) 0 z : ℝ)

private theorem phaseTurn_mem (z : UnitAddCircle) : phaseTurn z ∈ Ico (0 : ℝ) 1 := by
  simpa only [phaseTurn, zero_add] using (AddCircle.equivIco (1 : ℝ) 0 z).2

private theorem coe_phaseTurn (z : UnitAddCircle) : (phaseTurn z : UnitAddCircle) = z := AddCircle.coe_equivIco

private theorem eq_of_unitCircle_coe_eq_of_mem_Ico {a b : ℝ} (ha : a ∈ Ico (0 : ℝ) 1) (hb : b ∈ Ico (0 : ℝ) 1)
    (h : (a : UnitAddCircle) = (b : UnitAddCircle)) : a = b :=
  (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := (0 : ℝ))
    (by simpa only [zero_add] using ha) (by simpa only [zero_add] using hb)).mp h

private theorem mem_forwardUnitArc_of_turn {x r : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) (hr : r < 1) :
    (x : UnitAddCircle) ∈ forwardUnitArc r ↔ x ≤ r := by
  constructor
  · rintro ⟨y, hy, he⟩
    have h := eq_of_unitCircle_coe_eq_of_mem_Ico ⟨hy.1, hy.2.trans_lt hr⟩ hx he
    exact h ▸ hy.2
  · intro h
    exact ⟨x, ⟨hx.1, h⟩, rfl⟩

private theorem volume_coe_Icc {a b : ℝ} (hab : a ≤ b) (hw : b - a ≤ 1) :
    volume (((↑) : ℝ → UnitAddCircle) '' Icc a b) = ENNReal.ofReal (b - a) := by
  let r : Icc (0 : ℝ) 1 := ⟨b - a, sub_nonneg.mpr hab, hw⟩
  have hset : (((↑) : ℝ → UnitAddCircle) '' Icc a b) =
      (fun x : UnitAddCircle => x + -(a : UnitAddCircle)) ⁻¹' forwardUnitArc r := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t - a, ⟨sub_nonneg.mpr ht.1, sub_le_sub_right ht.2 a⟩, ?_⟩
      rw [AddCircle.coe_sub, sub_eq_add_neg]
    · rintro ⟨u, hu, he⟩
      refine ⟨u + a, ⟨by linarith only [hu.1], ?_⟩, ?_⟩
      · have h := hu.2
        change u ≤ b - a at h
        linarith only [h]
      · rw [AddCircle.coe_add, he]
        change (x + -(a : UnitAddCircle)) + (a : UnitAddCircle) = x
        rw [← sub_eq_add_neg, sub_add_cancel]
  rw [hset, measure_preimage_add_right, volume_forwardUnitArc_full r]

/-- The nonzero separations at which both points can anchor a covering arc. -/
def unitArcAnchorSeparation (r : ℝ) : Set UnitAddCircle :=
  {z | z ∈ forwardUnitArc r ∧ -z ∈ forwardUnitArc r ∧ z ≠ 0}

/-- The phases admitted by both an anchor at zero and an anchor at `z`. -/
def commonForwardUnitArc (r : ℝ) (z : UnitAddCircle) : Set UnitAddCircle :=
  forwardUnitArc r ∩ (fun x => x - z) ⁻¹' forwardUnitArc r

theorem unitArcAnchorSeparation_eq_image (r : Ico (1 / 2 : ℝ) 1) :
    unitArcAnchorSeparation r = (((↑) : ℝ → UnitAddCircle) '' Icc (1 - (r : ℝ)) (r : ℝ)) := by
  ext z
  have hs : 0 < 1 - (r : ℝ) := sub_pos.mpr r.2.2
  have hneg {a : ℝ} (ha : a ∈ Ico (0 : ℝ) 1) (hap : 0 < a) :
      (-(a : UnitAddCircle)) ∈ forwardUnitArc r ↔ 1 - a ≤ (r : ℝ) := by
    have he : ((1 - a : ℝ) : UnitAddCircle) = -(a : UnitAddCircle) := by
      rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub]
    rw [← he]
    exact mem_forwardUnitArc_of_turn ⟨sub_nonneg.mpr ha.2.le, sub_lt_self _ hap⟩ r.2.2
  constructor
  · rintro ⟨hpos, hanti, hz⟩
    let a := phaseTurn z
    have ha : a ∈ Ico (0 : ℝ) 1 := phaseTurn_mem z
    have he : (a : UnitAddCircle) = z := coe_phaseTurn z
    have hap : 0 < a := by
      refine lt_of_le_of_ne ha.1 fun h => hz ?_
      rw [← he, ← h, AddCircle.coe_zero]
    have hanti' : -(a : UnitAddCircle) ∈ forwardUnitArc r := by rwa [he]
    have hy := (hneg ha hap).mp hanti'
    have hx := (mem_forwardUnitArc_of_turn ha r.2.2).mp (he.symm ▸ hpos)
    exact ⟨a, ⟨by linarith only [hy], hx⟩, he⟩
  · rintro ⟨a, ha, rfl⟩
    have hap : 0 < a := hs.trans_le ha.1
    have haI : a ∈ Ico (0 : ℝ) 1 := ⟨hap.le, ha.2.trans_lt r.2.2⟩
    refine ⟨(mem_forwardUnitArc_of_turn haI r.2.2).mpr ha.2, (hneg haI hap).mpr ?_, ?_⟩
    · linarith only [ha.1]
    · exact fun hz => hap.ne' ((AddCircle.coe_eq_zero_iff_of_mem_Ico (p := (1 : ℝ)) haI).mp hz)

theorem isClosed_unitArcAnchorSeparation (r : Ico (1 / 2 : ℝ) 1) : IsClosed (unitArcAnchorSeparation r) := by
  rw [unitArcAnchorSeparation_eq_image r]
  exact (isCompact_Icc.image (AddCircle.continuous_mk' 1)).isClosed

/-- Two distinct anchors are admissible on a separation window of length `2r - 1`. -/
theorem volume_unitArcAnchorSeparation (r : Ico (1 / 2 : ℝ) 1) :
    volume (unitArcAnchorSeparation r) = ENNReal.ofReal (2 * (r : ℝ) - 1) := by
  rw [unitArcAnchorSeparation_eq_image r, volume_coe_Icc (by linarith only [r.2.1]) (by linarith only [r.2.2])]
  congr 1
  ring

/-- At any admissible separation, the common arc constraint has Haar length `2r - 1`. -/
theorem volume_commonForwardUnitArc (r : Ico (1 / 2 : ℝ) 1) {z : UnitAddCircle}
    (hz : z ∈ unitArcAnchorSeparation r) : volume (commonForwardUnitArc r z) = ENNReal.ofReal (2 * (r : ℝ) - 1) := by
  rw [unitArcAnchorSeparation_eq_image r] at hz
  obtain ⟨t, ht, htZ⟩ := hz
  have htI : t ∈ Ico (0 : ℝ) 1 := ⟨(sub_nonneg.mpr r.2.2.le).trans ht.1, ht.2.trans_lt r.2.2⟩
  let B := forwardUnitArc r
  let T := (fun x : UnitAddCircle => x - z) ⁻¹' B
  have hB : MeasurableSet B := (isClosed_forwardUnitArc r).measurableSet
  have hT : MeasurableSet T := hB.preimage (continuous_id.sub continuous_const).measurable
  have hdisj : Disjoint Bᶜ Tᶜ := by
    refine Set.disjoint_left.mpr ?_
    intro x hx hxz
    let a := phaseTurn x
    let b := phaseTurn (x - z)
    have ha := phaseTurn_mem x
    have hb := phaseTurn_mem (x - z)
    have ha' : (r : ℝ) < a := lt_of_not_ge fun h =>
      hx (coe_phaseTurn x ▸ (mem_forwardUnitArc_of_turn ha r.2.2).mpr h)
    have hb' : (r : ℝ) < b := by
      apply lt_of_not_ge
      intro h
      apply hxz
      change x - z ∈ forwardUnitArc r
      rw [← coe_phaseTurn (x - z)]
      exact (mem_forwardUnitArc_of_turn hb r.2.2).mpr h
    have he : ((a - b : ℝ) : UnitAddCircle) = (t : UnitAddCircle) := by
      change ((phaseTurn x - phaseTurn (x - z) : ℝ) : UnitAddCircle) = _
      rw [AddCircle.coe_sub, coe_phaseTurn, coe_phaseTurn, sub_sub_cancel]
      exact htZ.symm
    by_cases h : 0 ≤ a - b
    · have hI : a - b ∈ Ico (0 : ℝ) 1 := ⟨h, by linarith only [ha.2, hb.1]⟩
      have htEq := eq_of_unitCircle_coe_eq_of_mem_Ico hI htI he
      linarith only [htEq, ht.1, ha.2, hb']
    · have hI : 1 + (a - b) ∈ Ico (0 : ℝ) 1 :=
        ⟨by linarith only [ha.1, hb.2], by linarith only [lt_of_not_ge h]⟩
      have hw : ((1 + (a - b) : ℝ) : UnitAddCircle) = (t : UnitAddCircle) := by
        rw [AddCircle.coe_add, AddCircle.coe_period, zero_add, he]
      have htEq := eq_of_unitCircle_coe_eq_of_mem_Ico hI htI hw
      linarith only [htEq, ht.2, ha', hb.2]
  let r' : Icc (0 : ℝ) 1 := ⟨r, (by positivity : (0 : ℝ) ≤ 1 / 2).trans r.2.1, r.2.2.le⟩
  have hvolB : volume.real B = (r : ℝ) := by
    change (volume (forwardUnitArc r')).toReal = _
    rw [volume_forwardUnitArc_full r', ENNReal.toReal_ofReal r'.2.1]
  have hvolT : volume.real T = (r : ℝ) := by
    have he : T = (fun x : UnitAddCircle => x + -z) ⁻¹' B := by
      ext x
      simp only [T, mem_preimage, sub_eq_add_neg]
    rw [he, Measure.real, measure_preimage_add_right]
    exact hvolB
  have hC : commonForwardUnitArc r z = (Bᶜ ∪ Tᶜ)ᶜ := by simp only [commonForwardUnitArc, B, T, compl_union, compl_compl]
  have hV : volume.real (commonForwardUnitArc r z) = 2 * (r : ℝ) - 1 := by
    rw [hC, probReal_compl_eq_one_sub (hB.compl.union hT.compl), measureReal_union hdisj hT.compl,
      probReal_compl_eq_one_sub hB, probReal_compl_eq_one_sub hT, hvolB, hvolT]
    ring
  rw [← ENNReal.ofReal_toReal (measure_ne_top volume (commonForwardUnitArc r z))]
  exact congrArg ENNReal.ofReal hV

#print axioms unitArcAnchorSeparation_eq_image
#print axioms volume_unitArcAnchorSeparation
#print axioms volume_commonForwardUnitArc

end

end GaloisForLFunctions.HTGeometry
