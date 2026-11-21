import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

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
  letI : Measure.IsAddHaarMeasure (volume : Measure (ι → UnitAddCircle)) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  refine (anchorShear i).toAddMonoidHom.measurePreserving ?_ (anchorShear i).surjective rfl
  refine continuous_pi fun j => ?_
  change Continuous fun x : ι → UnitAddCircle => if j = i then x j else x j - x i
  by_cases h : j = i
  · simpa only [if_pos h] using (continuous_apply j : Continuous fun x : ι → UnitAddCircle => x j)
  · simpa only [if_neg h] using
      ((continuous_apply j).sub (continuous_apply i) : Continuous fun x : ι → UnitAddCircle => x j - x i)

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
  convert h using 1
  funext x
  change x j - x i = if j = i then x j else x j - x i
  exact (if_neg hne).symm

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
    simp [ties]
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

#print axioms volume_forwardUnitArc
#print axioms volume_anchoredUnitArc
#print axioms pairwise_aeDisjoint_anchoredUnitArc
#print axioms volume_enclosingUnitArc

end

end GaloisForLFunctions.HTGeometry
