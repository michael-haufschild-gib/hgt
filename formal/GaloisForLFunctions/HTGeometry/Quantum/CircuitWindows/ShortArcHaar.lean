import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Haar probability of a short enclosing phase arc

An enclosing arc can start at one of the sampled phases. Relative to that
phase the other coordinates are independent uniform phases. For arcs of
length at most half a turn, two different starting phases can work only
on a null set of coincident or antipodal pairs.
-/

open MeasureTheory Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

local instance : NullSingletonClass (volume : Measure UnitAddCircle) :=
  ⟨fun x => by rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]; simp⟩

/-- The forward arc from zero, with length measured in turns. -/
def forwardUnitArc (r : ℝ) : Set UnitAddCircle :=
  ((↑) : ℝ → UnitAddCircle) '' Icc 0 r

theorem isClosed_forwardUnitArc (r : ℝ) : IsClosed (forwardUnitArc r) :=
  (isCompact_Icc.image (AddCircle.continuous_mk' 1)).isClosed

theorem volume_forwardUnitArc (r : Icc (0 : ℝ) (1 / 2)) :
    volume (forwardUnitArc r) = ENNReal.ofReal (r : ℝ) := by
  rw [AddCircle.add_projection_respects_measure 1 (-(1 / 2 : ℝ))
    (isClosed_forwardUnitArc r).measurableSet, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
  have hset : (((↑) : ℝ → UnitAddCircle) ⁻¹' forwardUnitArc r) ∩
      Ioc (-(1 / 2 : ℝ)) (1 / 2) = Icc 0 (r : ℝ) := by
    have hsub : Icc 0 (r : ℝ) ⊆ Ioc (-(1 / 2 : ℝ)) (-(1 / 2) + 1) := by
      intro x hx
      exact ⟨by linarith only [hx.1], by linarith only [hx.2, r.2.2]⟩
    ext x
    constructor
    · rintro ⟨⟨y, hy, he⟩, hx⟩
      have hx' : x ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2) + 1) := by
        exact ⟨hx.1, by linarith only [hx.2]⟩
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc (hsub hy) hx').mp he ▸ hy
    · intro hx
      exact ⟨⟨x, hx, rfl⟩, ⟨(hsub hx).1, by linarith only [(hsub hx).2]⟩⟩
  rw [hset, Real.volume_Icc, sub_zero]

variable {ι : Type*} [Fintype ι]

/-- Phase packets whose forward arc of length `r` can begin at coordinate `i`. -/
def anchoredUnitArc (i : ι) (r : ℝ) : Set (ι → UnitAddCircle) :=
  {x | ∀ j, j ≠ i → x j - x i ∈ forwardUnitArc r}

/-- Phase packets covered by a forward arc beginning at some coordinate. -/
def enclosingUnitArc (r : ℝ) : Set (ι → UnitAddCircle) := ⋃ i : ι, anchoredUnitArc i r

omit [Fintype ι] in
theorem isClosed_anchoredUnitArc (i : ι) (r : ℝ) : IsClosed (anchoredUnitArc i r) := by
  have hset : anchoredUnitArc i r =
      ⋂ j : {j : ι // j ≠ i}, (fun x : ι → UnitAddCircle => x j - x i) ⁻¹' forwardUnitArc r := by
    ext x
    simp only [anchoredUnitArc, mem_setOf_eq, mem_iInter, mem_preimage, Subtype.forall]
  rw [hset]
  exact isClosed_iInter fun j => (isClosed_forwardUnitArc r).preimage
    ((continuous_apply (j : ι)).sub (continuous_apply i))

private def anchorShear [DecidableEq ι] (i : ι) :
    (ι → UnitAddCircle) ≃+ (ι → UnitAddCircle) where
  toFun x j := if j = i then x j else x j - x i
  invFun x j := if j = i then x j else x j + x i
  left_inv x := by
    funext j
    by_cases h : j = i <;> simp [h]
  right_inv x := by
    funext j
    by_cases h : j = i <;> simp [h]
  map_add' x y := by
    funext j
    by_cases h : j = i
    · simp [h]
    · simp only [Pi.add_apply, if_neg h]
      abel

private theorem measurePreserving_anchorShear [DecidableEq ι] (i : ι) :
    MeasurePreserving (anchorShear i) volume volume := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (ι → UnitAddCircle)) := {}
  refine (anchorShear i).toAddMonoidHom.measurePreserving ?_ (anchorShear i).surjective rfl
  refine continuous_pi fun j => ?_
  change Continuous fun x : ι → UnitAddCircle => if j = i then x j else x j - x i
  by_cases h : j = i
  · simpa only [if_pos h] using (continuous_apply j : Continuous fun x : ι → UnitAddCircle => x j)
  · simp only [if_neg h]
    exact (continuous_apply j).sub (continuous_apply i)

/-- Each possible starting phase contributes one independent arc constraint
per remaining coordinate. -/
theorem volume_anchoredUnitArc (i : ι) (r : Icc (0 : ℝ) (1 / 2)) :
    volume (anchoredUnitArc i r) = ENNReal.ofReal (r : ℝ) ^ (Fintype.card ι - 1) := by
  classical
  let s : ι → Set UnitAddCircle := fun j => if j = i then univ else forwardUnitArc r
  have hs : ∀ j, MeasurableSet (s j) := by
    intro j
    by_cases h : j = i <;> simp [s, h, (isClosed_forwardUnitArc r).measurableSet]
  have hset : anchoredUnitArc i r = anchorShear i ⁻¹' (univ.pi s) := by
    ext x
    change (∀ j, j ≠ i → x j - x i ∈ forwardUnitArc r) ↔
      (∀ j, j ∈ (univ : Set ι) → anchorShear i x j ∈ s j)
    constructor
    · intro h j _
      change (if j = i then x j else x j - x i) ∈ s j
      by_cases hj : j = i
      · simp [s, hj]
      · simpa only [s, if_neg hj] using h j hj
    · intro h j hj
      have hj' := h j (mem_univ j)
      change (if j = i then x j else x j - x i) ∈ s j at hj'
      simpa only [s, if_neg hj] using hj'
  rw [hset, (measurePreserving_anchorShear i).measure_preimage
    (MeasurableSet.univ_pi hs).nullMeasurableSet, volume_pi_pi,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have hi : volume (s i) = 1 := by simp [s]
  rw [hi, mul_one]
  calc
    _ = ∏ j ∈ Finset.univ.erase i, ENNReal.ofReal (r : ℝ) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [show s j = forwardUnitArc r from if_neg (Finset.ne_of_mem_erase hj), volume_forwardUnitArc]
    _ = _ := by rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]

private theorem measurePreserving_phaseDifference (i j : ι) (hne : j ≠ i) :
    MeasurePreserving (fun x : ι → UnitAddCircle => x j - x i) volume volume := by
  classical
  have h := (measurePreserving_eval (fun _ : ι => (volume : Measure UnitAddCircle)) j).comp
    (measurePreserving_anchorShear i)
  have hf : (fun x : ι → UnitAddCircle => x j - x i) =
      Function.eval j ∘ anchorShear i := by
    funext x
    change x j - x i = if j = i then x j else x j - x i
    exact (if_neg hne).symm
  rw [hf]
  exact h

private theorem sub_mem_arc_ties (r : Icc (0 : ℝ) (1 / 2)) {x y : UnitAddCircle}
    (hxy : x - y ∈ forwardUnitArc r) (hyx : y - x ∈ forwardUnitArc r) :
    x - y ∈ ({0, ((1 / 2 : ℝ) : UnitAddCircle)} : Set UnitAddCircle) := by
  obtain ⟨a, ha, hax⟩ := hxy
  obtain ⟨b, hb, hby⟩ := hyx
  have hsum : (↑(a + b) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_add, hax, hby]
    abel
  by_cases h : a + b < 1
  · have hz := (AddCircle.coe_eq_zero_iff_of_mem_Ico
        (p := (1 : ℝ)) ⟨add_nonneg ha.1 hb.1, h⟩).mp hsum
    have haz : a = 0 := by linarith only [hz, ha.1, hb.1]
    rw [← hax, haz, AddCircle.coe_zero]
    exact Or.inl rfl
  · have har : a = 1 / 2 := by linarith only [not_lt.mp h, ha.2, hb.2, r.2.2]
    rw [← hax, har]
    exact Or.inr rfl

/-- For lengths at most half a turn, the possible starting phases have
pairwise null overlap. -/
theorem pairwise_aeDisjoint_anchoredUnitArc (r : Icc (0 : ℝ) (1 / 2)) :
    Pairwise (fun i j : ι => AEDisjoint volume (anchoredUnitArc i r) (anchoredUnitArc j r)) := by
  intro i j hij
  let ties : Set UnitAddCircle := {0, ((1 / 2 : ℝ) : UnitAddCircle)}
  have hnull : volume ((fun x : ι → UnitAddCircle => x j - x i) ⁻¹' ties) = 0 := by
    have hm : MeasurableSet ties := (measurableSet_singleton _).insert _
    rw [(measurePreserving_phaseDifference i j hij.symm).measure_preimage hm.nullMeasurableSet]
    exact ((finite_singleton _).insert _).measure_zero _
  refine le_antisymm ((measure_mono ?_).trans_eq hnull) bot_le
  intro x hx
  exact sub_mem_arc_ties r (hx.1 j hij.symm) (hx.2 i hij)

/-- The Haar probability of an enclosing arc of length at most half a turn
is the number of phases times the single-anchor probability. -/
theorem volume_enclosingUnitArc (r : Icc (0 : ℝ) (1 / 2)) :
    volume (enclosingUnitArc (ι := ι) r) =
      (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (r : ℝ) ^ (Fintype.card ι - 1) := by
  classical
  rw [enclosingUnitArc, measure_iUnion₀ (pairwise_aeDisjoint_anchoredUnitArc r)
    (fun i => (isClosed_anchoredUnitArc i r).measurableSet.nullMeasurableSet), tsum_fintype]
  simp only [volume_anchoredUnitArc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem isClosed_enclosingUnitArc (r : ℝ) : IsClosed (enclosingUnitArc (ι := ι) r) :=
  isClosed_iUnion_of_finite (fun i => isClosed_anchoredUnitArc i r)

private def strictEnclosingUnitArc (r : ℝ) : Set (ι → UnitAddCircle) :=
  ⋃ i : ι, ⋂ j : {j : ι // j ≠ i}, (fun x : ι → UnitAddCircle => x j - x i) ⁻¹'
    (((↑) : ℝ → UnitAddCircle) '' Ioo 0 r)

private theorem isOpen_strictEnclosingUnitArc (r : ℝ) :
    IsOpen (strictEnclosingUnitArc (ι := ι) r) := by
  have ho : IsOpen (((↑) : ℝ → UnitAddCircle) '' Ioo 0 r) :=
    QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  exact isOpen_iUnion fun i => isOpen_iInter_of_finite fun j =>
    ho.preimage ((continuous_apply (j : ι)).sub (continuous_apply i))

private theorem strictEnclosingUnitArc_subset (r : ℝ) :
    strictEnclosingUnitArc (ι := ι) r ⊆ enclosingUnitArc r := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨i, fun j hj =>
    image_mono Ioo_subset_Icc_self (mem_iInter.mp hi ⟨j, hj⟩)⟩

private theorem volume_enclosingUnitArc_sdiff_strict (r : ℝ) :
    volume (enclosingUnitArc (ι := ι) r \ strictEnclosingUnitArc r) = 0 := by
  classical
  let ends : Set UnitAddCircle := {0, (r : UnitAddCircle)}
  let hits := fun (i : ι) (j : {j : ι // j ≠ i}) =>
    (fun x : ι → UnitAddCircle => x j - x i) ⁻¹' ends
  have hn : volume (⋃ i, ⋃ j, hits i j) = 0 := by
    refine measure_iUnion_null fun i => measure_iUnion_null fun j => ?_
    have hm : MeasurableSet ends := (measurableSet_singleton _).insert _
    change volume ((fun x : ι → UnitAddCircle => x j - x i) ⁻¹' ends) = 0
    rw [(measurePreserving_phaseDifference i j j.2).measure_preimage hm.nullMeasurableSet]
    exact ((finite_singleton _).insert _).measure_zero _
  refine le_antisymm ((measure_mono ?_).trans_eq hn) bot_le
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx.1
  by_contra hno
  apply hx.2
  refine mem_iUnion.mpr ⟨i, mem_iInter.mpr fun j => ?_⟩
  obtain ⟨a, ha, he⟩ := hi j j.2
  have hne : x j - x i ∉ ends := fun h =>
    hno (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, h⟩⟩)
  have h0 : a ≠ 0 := by
    intro h
    apply hne
    rw [← he, h, AddCircle.coe_zero]
    exact Or.inl rfl
  have hr : a ≠ r := by
    intro h
    apply hne
    rw [← he, h]
    exact Or.inr rfl
  exact ⟨a, ⟨lt_of_le_of_ne ha.1 (Ne.symm h0), lt_of_le_of_ne ha.2 hr⟩, he⟩

/-- Insert the reference coordinate as the zero phase. -/
def relativeUnitPhasePacket (i : ι) (x : {j : ι // j ≠ i} → UnitAddCircle) : ι → UnitAddCircle := by
  classical
  exact fun j => if hj : j ≠ i then x ⟨j, hj⟩ else 0

private theorem continuous_relativeUnitPhasePacket (i : ι) : Continuous (relativeUnitPhasePacket i) := by
  classical
  refine continuous_pi fun j => ?_
  change Continuous fun x : {j : ι // j ≠ i} → UnitAddCircle => if hj : j ≠ i then x ⟨j, hj⟩ else 0
  by_cases h : j ≠ i
  · simpa only [dif_pos h] using (continuous_apply (⟨j, h⟩ : {j : ι // j ≠ i}))
  · simp only [dif_neg h]
    exact continuous_const

/-- The short-arc event in relative coordinates, with the reference phase at zero. -/
def relativeEnclosingUnitArc (i : ι) (r : ℝ) : Set ({j : ι // j ≠ i} → UnitAddCircle) :=
  relativeUnitPhasePacket i ⁻¹' enclosingUnitArc r

theorem isClosed_relativeEnclosingUnitArc (i : ι) (r : ℝ) : IsClosed (relativeEnclosingUnitArc i r) :=
  (isClosed_enclosingUnitArc r).preimage (continuous_relativeUnitPhasePacket i)

private theorem measurePreserving_relativeUnitPhases (i : ι) :
    MeasurePreserving (fun (x : ι → UnitAddCircle) (j : {j : ι // j ≠ i}) => x j - x i)
      volume volume := by
  classical
  let p := fun j : ι => j ≠ i
  have hsplit := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => UnitAddCircle) p
  have hπ : MeasurePreserving (β := {j : ι // p j} → UnitAddCircle)
      (Prod.fst : (({j : ι // p j} → UnitAddCircle) × ({j : ι // ¬p j} → UnitAddCircle)) → _)
      volume volume := measurePreserving_fst
  have hf : (fun (x : ι → UnitAddCircle) (j : {j : ι // j ≠ i}) => x j - x i) =
      Prod.fst ∘ MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => UnitAddCircle) p ∘ anchorShear i := by
    funext x j
    change x j - x i = if (j : ι) = i then x j else x j - x i
    exact (if_neg j.2).symm
  rw [hf]
  exact hπ.comp (hsplit.comp (measurePreserving_anchorShear i))

private theorem relativeUnitPhasePacket_of_sub (i : ι) (x : ι → UnitAddCircle) (j : ι) :
    relativeUnitPhasePacket i (fun k => x k - x i) j = x j - x i := by
  classical
  by_cases h : j = i
  · subst j
    simp [relativeUnitPhasePacket]
  · simp [relativeUnitPhasePacket, h]

/-- Taking relative phases preserves the exact short-arc probability. -/
theorem volume_relativeEnclosingUnitArc (i : ι) (r : Icc (0 : ℝ) (1 / 2)) :
    volume (relativeEnclosingUnitArc i r) =
      (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (r : ℝ) ^ (Fintype.card ι - 1) := by
  have hpre : (fun (x : ι → UnitAddCircle) (j : {j : ι // j ≠ i}) => x j - x i) ⁻¹'
      relativeEnclosingUnitArc i r = enclosingUnitArc r := by
    ext x
    simp only [relativeEnclosingUnitArc, mem_preimage, enclosingUnitArc, mem_iUnion, anchoredUnitArc,
      mem_setOf_eq, relativeUnitPhasePacket_of_sub, sub_sub_sub_cancel_right]
  rw [← (measurePreserving_relativeUnitPhases i).measure_preimage
    (isClosed_relativeEnclosingUnitArc i r).measurableSet.nullMeasurableSet, hpre, volume_enclosingUnitArc]

/-- A short-arc event is a continuity set for relative Haar measure. -/
theorem volume_frontier_relativeEnclosingUnitArc (i : ι) (r : ℝ) :
    volume (frontier (relativeEnclosingUnitArc i r)) = 0 := by
  let V := relativeUnitPhasePacket i ⁻¹' strictEnclosingUnitArc r
  have hV : IsOpen V := (isOpen_strictEnclosingUnitArc r).preimage (continuous_relativeUnitPhasePacket i)
  have hsub : V ⊆ relativeEnclosingUnitArc i r := preimage_mono (strictEnclosingUnitArc_subset r)
  have hv : volume (relativeEnclosingUnitArc i r \ V) = 0 := by
    have hpre : (fun (x : ι → UnitAddCircle) (j : {j : ι // j ≠ i}) => x j - x i) ⁻¹'
        (relativeEnclosingUnitArc i r \ V) = enclosingUnitArc r \ strictEnclosingUnitArc r := by
      ext x
      simp only [V, relativeEnclosingUnitArc, mem_preimage, mem_sdiff, enclosingUnitArc, mem_iUnion,
        anchoredUnitArc, mem_setOf_eq, strictEnclosingUnitArc, mem_iInter,
        relativeUnitPhasePacket_of_sub, sub_sub_sub_cancel_right]
    have hm := (isClosed_relativeEnclosingUnitArc i r).measurableSet.diff hV.measurableSet
    rw [← (measurePreserving_relativeUnitPhases i).measure_preimage hm.nullMeasurableSet, hpre]
    exact volume_enclosingUnitArc_sdiff_strict r
  refine le_antisymm ((measure_mono ?_).trans_eq hv) bot_le
  rw [frontier, (isClosed_relativeEnclosingUnitArc i r).closure_eq]
  exact sdiff_subset_sdiff_right (interior_maximal hsub hV)

#print axioms isClosed_enclosingUnitArc
#print axioms volume_forwardUnitArc
#print axioms volume_anchoredUnitArc
#print axioms pairwise_aeDisjoint_anchoredUnitArc
#print axioms volume_enclosingUnitArc
#print axioms volume_relativeEnclosingUnitArc
#print axioms volume_frontier_relativeEnclosingUnitArc

end

end GaloisForLFunctions.HTGeometry
