import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AnchorTripleOccupation

/-!
# Common arc constraints for many anchors

Mutual admissibility makes the forbidden arcs of distinct anchors disjoint
almost everywhere. Their lengths add, leaving one constant allowed volume
for every unmarked coordinate of the packet.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance anchorPackingCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-- All phases admitted by the specified anchors. -/
def commonAnchoredUnitArc {ι : Type*} (z : ι → UnitAddCircle) (s : Finset ι) (r : ℝ) : Set UnitAddCircle :=
  ⋂ i ∈ s, (fun x => x - z i) ⁻¹' forwardUnitArc r

/-- For mutually admissible, distinct anchors, the common allowed length
is one minus the sum of their complementary gaps. -/
theorem measureReal_commonAnchoredUnitArc {ι : Type*} (z : ι → UnitAddCircle) (s : Finset ι)
    (r : Ico (1 / 2 : ℝ) 1)
    (hsep : (s : Set ι).Pairwise (fun i j => z j - z i ∈ unitArcAnchorSeparation r)) :
    volume.real (commonAnchoredUnitArc z s r) = 1 - (s.card : ℝ) * (1 - (r : ℝ)) := by
  let T (i : ι) := (fun x : UnitAddCircle => x - z i) ⁻¹' forwardUnitArc (r : ℝ)
  let R : Icc (0 : ℝ) 1 := ⟨r, (by norm_num : (0 : ℝ) ≤ 1 / 2).trans r.2.1, r.2.2.le⟩
  have hT (i : ι) : MeasurableSet (T i) := (isClosed_forwardUnitArc r).measurableSet.preimage
    (continuous_id.sub continuous_const).measurable
  have hsingle (i : ι) : volume.real (T i) = (r : ℝ) := by
    have he : T i = (fun x : UnitAddCircle => x + -z i) ⁻¹' forwardUnitArc r := by
      ext x
      simp only [T, mem_preimage, sub_eq_add_neg]
    rw [he, Measure.real, measure_preimage_add_right, volume_forwardUnitArc_full R, ENNReal.toReal_ofReal R.2.1]
  have hpair {i j : ι} (hi : i ∈ (s : Set ι)) (hj : j ∈ (s : Set ι)) (hij : i ≠ j) :
      volume.real (T i ∩ T j) = 2 * (r : ℝ) - 1 := by
    have he : T i ∩ T j = (fun x : UnitAddCircle => x + -z i) ⁻¹' commonForwardUnitArc r (z j - z i) := by
      ext x
      simp only [T, commonForwardUnitArc, mem_inter_iff, mem_preimage]
      rw [← sub_eq_add_neg, sub_sub_sub_cancel_right]
    rw [he, Measure.real, measure_preimage_add_right, volume_commonForwardUnitArc r (hsep hi hj hij),
      ENNReal.toReal_ofReal (by linarith only [r.2.1] : 0 ≤ 2 * (r : ℝ) - 1)]
  have hd : (s : Set ι).Pairwise (fun i j => AEDisjoint volume (T i)ᶜ (T j)ᶜ) := by
    intro i hi j hj hij
    have h := measureReal_union_add_inter (μ := volume) (s := (T i)ᶜ) (hT j).compl
    rw [← compl_inter, probReal_compl_eq_one_sub ((hT i).inter (hT j)),
      probReal_compl_eq_one_sub (hT i), probReal_compl_eq_one_sub (hT j), hsingle, hsingle, hpair hi hj hij] at h
    have hzero : volume.real ((T i)ᶜ ∩ (T j)ᶜ) = 0 := by linarith only [h]
    change volume ((T i)ᶜ ∩ (T j)ᶜ) = 0
    rw [← ENNReal.ofReal_toReal (measure_ne_top volume ((T i)ᶜ ∩ (T j)ᶜ)),
      show (volume ((T i)ᶜ ∩ (T j)ᶜ)).toReal = 0 from hzero, ENNReal.ofReal_zero]
  have hM : MeasurableSet (⋃ i ∈ s, (T i)ᶜ) := Finset.measurableSet_biUnion s fun i _ => (hT i).compl
  have hC : commonAnchoredUnitArc z s r = (⋃ i ∈ s, (T i)ᶜ)ᶜ := by
    simp only [commonAnchoredUnitArc, T, compl_iUnion, compl_compl]
  have hcomp (i : ι) : volume.real ((T i)ᶜ) = 1 - (r : ℝ) := by
    rw [probReal_compl_eq_one_sub (hT i), hsingle]
  rw [hC, probReal_compl_eq_one_sub hM, measureReal_biUnion_finset₀ hd (fun i _ => (hT i).compl.nullMeasurableSet)]
  simp only [hcomp, Finset.sum_const, nsmul_eq_mul]

/-- Conditional on mutually admissible anchors, the remaining independent
phases contribute one power of the common allowed length per coordinate. -/
theorem volume_commonAnchoredUnitArc_product {ι J : Type*} [Fintype J] (z : ι → UnitAddCircle) (s : Finset ι)
    (r : Ico (1 / 2 : ℝ) 1)
    (hsep : (s : Set ι).Pairwise (fun i j => z j - z i ∈ unitArcAnchorSeparation r)) :
    volume ((univ : Set J).pi (fun _ => commonAnchoredUnitArc z s r)) =
      ENNReal.ofReal (1 - (s.card : ℝ) * (1 - (r : ℝ))) ^ Fintype.card J := by
  have he : volume (commonAnchoredUnitArc z s r) = ENNReal.ofReal (1 - (s.card : ℝ) * (1 - (r : ℝ))) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top volume (commonAnchoredUnitArc z s r))]
    exact congrArg ENNReal.ofReal (measureReal_commonAnchoredUnitArc z s r hsep)
  rw [volume_pi_pi]
  simp only [he, Finset.prod_const, Finset.card_univ]

/-- Distinct covering anchors spend at most one full turn in complementary gaps. -/
theorem card_mul_complement_le_of_anchoredUnitArcs {ι : Type*} (x : ι → UnitAddCircle) (s : Finset ι)
    (r : Ico (1 / 2 : ℝ) 1) (hinj : Set.InjOn x (s : Set ι))
    (ha : ∀ i ∈ s, x ∈ anchoredUnitArc i r) : (s.card : ℝ) * (1 - (r : ℝ)) ≤ 1 := by
  have hsep : (s : Set ι).Pairwise (fun i j => x j - x i ∈ unitArcAnchorSeparation r) := by
    intro i hi j hj hij
    exact ⟨ha i hi j hij.symm, by simpa only [neg_sub] using ha j hj i hij,
      sub_ne_zero.mpr (fun h => hij (hinj hi hj h.symm))⟩
  have h : 0 ≤ volume.real (commonAnchoredUnitArc x s r) := measureReal_nonneg
  rw [measureReal_commonAnchoredUnitArc x s r hsep] at h
  exact sub_nonneg.mp h

/-- A relative Haar packet has distinct phases almost surely. -/
theorem ae_injective_relativeUnitPhasePacket {ι : Type*} [Fintype ι] [DecidableEq ι] (ref : ι) :
    ∀ᵐ x ∂(volume : Measure ({j : ι // j ≠ ref} → UnitAddCircle)),
      Function.Injective (relativeUnitPhasePacket ref x) := by
  have hp (i j : ι) : ∀ᵐ x ∂(volume : Measure ({k : ι // k ≠ ref} → UnitAddCircle)),
      relativeUnitPhasePacket ref x i = relativeUnitPhasePacket ref x j → i = j := by
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ _ => hij
    · filter_upwards [ae_phaseDifference_avoids_finite ref hij (finite_singleton (0 : UnitAddCircle))] with x hx
      intro he
      exact False.elim (hx (by rw [he, sub_self]; exact mem_singleton _))
  have h : ∀ᵐ x ∂(volume : Measure ({k : ι // k ≠ ref} → UnitAddCircle)),
      ∀ i ∈ (univ : Set ι), ∀ j ∈ (univ : Set ι),
        relativeUnitPhasePacket ref x i = relativeUnitPhasePacket ref x j → i = j :=
    (Filter.eventually_all_finite finite_univ).mpr fun i _ =>
      (Filter.eventually_all_finite finite_univ).mpr fun j _ => hp i j
  exact h.mono fun _ hx _ _ he => hx _ (mem_univ _) _ (mem_univ _) he

/-- Above the gap-packing capacity, the corresponding inclusion–exclusion
term has zero Haar mass. -/
theorem volume_biInter_relativeAnchoredUnitArc_eq_zero_of_capacity {ι : Type*}
    [Fintype ι] [DecidableEq ι] (ref : ι) (s : Finset ι) (r : Ico (1 / 2 : ℝ) 1)
    (hcap : 1 < (s.card : ℝ) * (1 - (r : ℝ))) : volume (⋂ i ∈ s, relativeAnchoredUnitArc ref i r) = 0 := by
  have h : ∀ᵐ x ∂(volume : Measure ({j : ι // j ≠ ref} → UnitAddCircle)),
      x ∉ ⋂ i ∈ s, relativeAnchoredUnitArc ref i r := by
    filter_upwards [ae_injective_relativeUnitPhasePacket ref] with x hx
    intro hm
    exact (not_le_of_gt hcap) (card_mul_complement_le_of_anchoredUnitArcs (relativeUnitPhasePacket ref x) s r
      hx.injOn (fun i hi => mem_iInter.mp (mem_iInter.mp hm i) hi))
  rw [ae_iff] at h
  simpa only [not_not, setOf_mem_eq] using h

#print axioms measureReal_commonAnchoredUnitArc
#print axioms volume_commonAnchoredUnitArc_product
#print axioms card_mul_complement_le_of_anchoredUnitArcs
#print axioms ae_injective_relativeUnitPhasePacket
#print axioms volume_biInter_relativeAnchoredUnitArc_eq_zero_of_capacity

end

end GaloisForLFunctions.HTGeometry
