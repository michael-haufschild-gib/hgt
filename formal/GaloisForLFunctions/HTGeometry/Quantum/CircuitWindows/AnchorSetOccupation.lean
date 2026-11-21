import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AnchorPackingCapacity

/-!
# Conditioning on the marked anchors

Split relative Haar coordinates into the marked anchors and the remaining
phases. A mutually admissible marked packet leaves a constant common arc
length, so the mass of the remaining coordinates factors out exactly.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance anchorSetCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Relative coordinates of the marked anchors, with the base phase omitted. -/
abbrev markedAnchorIndex (s : Finset ι) (base : ι) := {j : {i : ι // i ≠ base} // j.val ∈ s}

/-- Insert the zero phase at the base and read the marked phases at their labels. -/
def markedAnchorPhasePacket (s : Finset ι) (base : ι) (u : markedAnchorIndex s base → UnitAddCircle)
    (i : ι) : UnitAddCircle :=
  if hi : i ≠ base ∧ i ∈ s then u ⟨⟨i, hi.1⟩, hi.2⟩ else 0

omit [Fintype ι] in
private theorem continuous_markedAnchorPhasePacket_at (s : Finset ι) (b i : ι) :
    Continuous (fun u => markedAnchorPhasePacket s b u i) := by
  by_cases hi : i ≠ b ∧ i ∈ s
  · simpa only [markedAnchorPhasePacket, dif_pos hi] using
      (continuous_apply (⟨⟨i, hi.1⟩, hi.2⟩ : markedAnchorIndex s b))
  · simp only [markedAnchorPhasePacket, dif_neg hi]
    exact continuous_const

/-- The separated configurations of the marked anchors that admit the
given radius at every marked starting phase. -/
def admissibleMarkedAnchorPhases (s : Finset ι) (b : ι) (r : ℝ) : Set (markedAnchorIndex s b → UnitAddCircle) :=
  {u | (s : Set ι).Pairwise (fun i j =>
    markedAnchorPhasePacket s b u j - markedAnchorPhasePacket s b u i ∈ unitArcAnchorSeparation r)}

omit [Fintype ι] in
theorem isClosed_admissibleMarkedAnchorPhases (s : Finset ι) (b : ι) (r : Ico (1 / 2 : ℝ) 1) :
    IsClosed (admissibleMarkedAnchorPhases s b r) := by
  have he : admissibleMarkedAnchorPhases s b r = ⋂ i ∈ s, ⋂ j ∈ s, ⋂ (_ : i ≠ j),
      (fun u => markedAnchorPhasePacket s b u j - markedAnchorPhasePacket s b u i) ⁻¹'
        unitArcAnchorSeparation r := by
    ext u
    simp only [admissibleMarkedAnchorPhases, mem_setOf_eq, Set.Pairwise, Finset.mem_coe,
      mem_iInter, mem_preimage]
  rw [he]
  exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_iInter fun _ => (isClosed_unitArcAnchorSeparation r).preimage
      ((continuous_markedAnchorPhasePacket_at s b j).sub (continuous_markedAnchorPhasePacket_at s b i))

/-- Joint anchor occupation factors into the volume of the admissible
marked configurations and the common arc length to the unmarked power. -/
theorem volume_biInter_relativeAnchoredUnitArc_factor (s : Finset ι) {b : ι} (hb : b ∈ s)
    (r : Ico (1 / 2 : ℝ) 1) : volume (⋂ i ∈ s, relativeAnchoredUnitArc b i r) =
      volume (admissibleMarkedAnchorPhases s b r) *
        ENNReal.ofReal (1 - (s.card : ℝ) * (1 - (r : ℝ))) ^ (Fintype.card ι - s.card) := by
  classical
  let J := {i : ι // i ≠ b}
  let M := markedAnchorIndex s b
  let N := {j : J // j.val ∉ s}
  let z := markedAnchorPhasePacket s b
  let W := admissibleMarkedAnchorPhases s b r
  let A := ⋂ i ∈ s, relativeAnchoredUnitArc b i (r : ℝ)
  let split := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : J => UnitAddCircle) (fun j => j.val ∈ s)
  let S : Set ((M → UnitAddCircle) × (N → UnitAddCircle)) :=
    Prod.fst ⁻¹' W ∩ ⋂ j : N, ⋂ i ∈ s, (fun p : (M → UnitAddCircle) × (N → UnitAddCircle) =>
      p.2 j - z p.1 i) ⁻¹' forwardUnitArc r
  have hW : MeasurableSet W := (isClosed_admissibleMarkedAnchorPhases s b r).measurableSet
  have hS : MeasurableSet S := by
    refine (measurable_fst hW).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun i =>
      MeasurableSet.iInter fun _ => ?_)
    exact (((continuous_apply j).comp continuous_snd).sub
      ((continuous_markedAnchorPhasePacket_at s b i).comp continuous_fst)).measurable
      (isClosed_forwardUnitArc r).measurableSet
  have hpre : split ⁻¹' S = A ∩ {x | Set.InjOn (relativeUnitPhasePacket b x) (s : Set ι)} := by
    ext x
    let y := relativeUnitPhasePacket b x
    let u : M → UnitAddCircle := fun j => x j.val
    have hz {i : ι} (hi : i ∈ s) : z u i = y i := by
      by_cases h : i ≠ b
      · have hp : i ≠ b ∧ i ∈ s := ⟨h, hi⟩
        simp only [z, u, y, markedAnchorPhasePacket, dif_pos hp, relativeUnitPhasePacket, dif_pos h]
      · have hp : ¬ (i ≠ b ∧ i ∈ s) := fun e => h e.1
        simp only [z, y, markedAnchorPhasePacket, dif_neg hp, relativeUnitPhasePacket, dif_neg h]
    have hy (j : N) : y j.val.val = x j.val := by
      simp only [y, relativeUnitPhasePacket, dif_pos j.val.property]
      exact congrArg x (Subtype.ext rfl)
    change (x ∈ split ⁻¹' S) ↔ _
    have hs : x ∈ split ⁻¹' S ↔ u ∈ W ∧
        ∀ j : N, ∀ i ∈ s, x j.val - z u i ∈ forwardUnitArc r := by
      simp only [S, mem_preimage, mem_inter_iff, mem_iInter]
      rfl
    rw [hs]
    constructor
    · rintro ⟨hsep, hrest⟩
      change (s : Set ι).Pairwise (fun i j => z u j - z u i ∈ unitArcAnchorSeparation r) at hsep
      refine ⟨?_, ?_⟩
      · refine mem_iInter.mpr fun i => mem_iInter.mpr fun hi => ?_
        change y ∈ anchoredUnitArc i r
        intro j hji
        by_cases hjs : j ∈ s
        · simpa only [hz hi, hz hjs] using (hsep hi hjs hji.symm).1
        · have hjb : j ≠ b := fun he => hjs (he.symm ▸ hb)
          let j' : N := ⟨⟨j, hjb⟩, hjs⟩
          simpa only [hz hi, ← hy j'] using hrest j' i hi
      · change Set.InjOn y (s : Set ι)
        intro i hi j hj he
        by_contra hne
        have h := (hsep hi hj hne).2.2
        apply h
        rw [hz hi, hz hj, he, sub_self]
    · rintro ⟨hA, hinj⟩
      have hanchor (i : ι) (hi : i ∈ s) : y ∈ anchoredUnitArc i r := mem_iInter.mp (mem_iInter.mp hA i) hi
      refine ⟨?_, ?_⟩
      · change (s : Set ι).Pairwise (fun i j => z u j - z u i ∈ unitArcAnchorSeparation r)
        intro i hi j hj hij
        rw [hz hi, hz hj]
        exact ⟨hanchor i hi j hij.symm, by simpa only [neg_sub] using hanchor j hj i hij,
          sub_ne_zero.mpr (fun e => hij (hinj hi hj e.symm))⟩
      · intro j i hi
        have hji : j.val.val ≠ i := fun he => j.property (he.symm ▸ hi)
        rw [← hy j, hz hi]
        exact hanchor i hi j.val.val hji
  have hne : (A ∩ {x | Set.InjOn (relativeUnitPhasePacket b x) (s : Set ι)} : Set (J → UnitAddCircle)) =ᵐ[volume] A := by
    filter_upwards [ae_injective_relativeUnitPhasePacket b] with x hx
    exact propext ⟨fun h => h.1, fun h => ⟨h, hx.injOn⟩⟩
  have hcard : Fintype.card N = Fintype.card ι - s.card := by
    let e : N ≃ {i : ι // i ∉ s} :=
      { toFun := fun j => ⟨j.val.val, j.property⟩
        invFun := fun j => ⟨⟨j.val, fun h => j.property (h.symm ▸ hb)⟩, j.property⟩
        left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
        right_inv := fun _ => Subtype.ext rfl }
    rw [Fintype.card_congr e, Fintype.card_subtype_compl (fun i => i ∈ s), Fintype.card_coe]
  let q := ENNReal.ofReal (1 - (s.card : ℝ) * (1 - (r : ℝ))) ^ (Fintype.card ι - s.card)
  have hslice (u : M → UnitAddCircle) : volume (Prod.mk u ⁻¹' S) = W.indicator (fun _ => q) u := by
    by_cases hu : u ∈ W
    · have he : Prod.mk u ⁻¹' S = (univ : Set N).pi (fun _ => commonAnchoredUnitArc (z u) s r) := by
        ext v
        simp only [S, commonAnchoredUnitArc, mem_preimage, mem_inter_iff, hu, true_and, mem_iInter,
          Set.mem_pi, mem_univ, true_implies]
      rw [he, volume_commonAnchoredUnitArc_product (z u) s r hu, hcard, indicator_of_mem hu]
    · have he : Prod.mk u ⁻¹' S = ∅ := by
        ext v
        simp only [S, mem_preimage, mem_inter_iff, hu, false_and, mem_empty_iff_false]
      rw [he, measure_empty, indicator_of_notMem hu]
  have hm : MeasurePreserving split volume
      ((volume : Measure (M → UnitAddCircle)).prod (volume : Measure (N → UnitAddCircle))) :=
    volume_preserving_piEquivPiSubtypeProd (fun _ : J => UnitAddCircle) (fun j => j.val ∈ s)
  change volume A = volume W * q
  rw [← measure_congr hne, ← hpre, hm.measure_preimage hS.nullMeasurableSet, Measure.prod_apply hS]
  simp only [hslice]
  rw [lintegral_indicator hW, lintegral_const, Measure.restrict_apply_univ, mul_comm]

/-- The factorization holds in any reference coordinates, using any marked
anchor as the zero phase in the marked packet. -/
theorem volume_biInter_relativeAnchoredUnitArc_factor_of_reference (ref : ι) (s : Finset ι)
    {b : ι} (hb : b ∈ s) (r : Ico (1 / 2 : ℝ) 1) :
    volume (⋂ i ∈ s, relativeAnchoredUnitArc ref i r) =
      volume (admissibleMarkedAnchorPhases s b r) *
        ENNReal.ofReal (1 - (s.card : ℝ) * (1 - (r : ℝ))) ^ (Fintype.card ι - s.card) := by
  have he : relativeUnitPhaseRebase ref b ⁻¹' (⋂ i ∈ s, relativeAnchoredUnitArc b i r) =
      ⋂ i ∈ s, relativeAnchoredUnitArc ref i r := by
    ext x
    simp only [mem_preimage, mem_iInter, relativeAnchoredUnitArc, anchoredUnitArc, mem_setOf_eq,
      relativeUnitPhasePacket_rebase, sub_sub_sub_cancel_right]
  have hM : IsClosed (⋂ i ∈ s, relativeAnchoredUnitArc b i r) :=
    isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_relativeAnchoredUnitArc b i r
  rw [← he, (measurePreserving_relativeUnitPhaseRebase ref b).measure_preimage hM.measurableSet.nullMeasurableSet,
    volume_biInter_relativeAnchoredUnitArc_factor s hb r]

/-- At exact packing capacity, even one unmarked phase forces the joint
anchor event to have measure zero. -/
theorem volume_biInter_relativeAnchoredUnitArc_eq_zero_of_capacity_le (ref : ι) (s : Finset ι)
    (r : Ico (1 / 2 : ℝ) 1) (hD : s.card < Fintype.card ι)
    (hcap : 1 ≤ (s.card : ℝ) * (1 - (r : ℝ))) :
    volume (⋂ i ∈ s, relativeAnchoredUnitArc ref i r) = 0 := by
  have hs : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.card_empty, Nat.cast_zero, zero_mul] at hcap
    exact (not_le_of_gt zero_lt_one) hcap
  obtain ⟨b, hb⟩ := hs
  rw [volume_biInter_relativeAnchoredUnitArc_factor_of_reference ref s hb r,
    ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr hcap), zero_pow (Nat.sub_pos_of_lt hD).ne', mul_zero]

#print axioms isClosed_admissibleMarkedAnchorPhases
#print axioms volume_biInter_relativeAnchoredUnitArc_factor
#print axioms volume_biInter_relativeAnchoredUnitArc_factor_of_reference
#print axioms volume_biInter_relativeAnchoredUnitArc_eq_zero_of_capacity_le

end

end GaloisForLFunctions.HTGeometry
