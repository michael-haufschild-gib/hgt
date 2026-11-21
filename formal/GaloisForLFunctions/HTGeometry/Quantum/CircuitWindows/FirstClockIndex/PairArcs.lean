import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortArcHaar

/-! # Two nearby harmonics of a uniform circle phase -/
open Set MeasureTheory
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FirstClockIndex
noncomputable section

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

private abbrev CirclePair := UnitAddCircle × UnitAddCircle

private def liftTurn (x : UnitAddCircle) : ℝ := (AddCircle.measurableEquivIoc 1 0 x).val

private theorem coe_liftTurn (x : UnitAddCircle) : (liftTurn x : UnitAddCircle) = x :=
  AddCircle.coe_equivIoc

private def smallShift (q : ℕ) (z : UnitAddCircle) : UnitAddCircle := ((liftTurn z/(q:ℝ) : ℝ) : UnitAddCircle)

private theorem multiple_shift (q h : ℕ) (z : UnitAddCircle) :
    h • smallShift q z = (((h:ℝ)*(liftTurn z/(q:ℝ)):ℝ):UnitAddCircle) := by
  rw [←nsmul_eq_mul,AddCircle.coe_nsmul]
  rfl

private theorem exact_shift {q : ℕ} (hq : 0 < q) (z : UnitAddCircle) : q • smallShift q z = z := by
  rw [multiple_shift,mul_comm (q:ℝ),div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hq.ne'),coe_liftTurn]

/-- A positive integer multiple of a uniform phase is uniform. -/
theorem multiple_preserves {q : ℕ} (hq : 0 < q) :
    MeasurePreserving (fun θ : UnitAddCircle => q • θ) volume volume := by
  let f : UnitAddCircle →+ UnitAddCircle :=
    { toFun := fun θ => q • θ
      map_zero' := nsmul_zero _
      map_add' := fun a b => nsmul_add a b q }
  exact f.measurePreserving (continuous_nsmul q) (fun z => ⟨_,exact_shift hq z⟩) rfl

/-- With an auxiliary independent phase z the two outputs qθ−z and
(q+h)θ−z are independent uniform phases whenever h>0. -/
private theorem linear_pair_preserves (q h : ℕ) (hh : 0 < h) :
    MeasurePreserving (fun p : CirclePair => (q • p.2-p.1,(q+h) • p.2-p.1))
      (volume : Measure CirclePair) volume := by
  let f : CirclePair →+ CirclePair :=
    { toFun := fun p => (q • p.2-p.1,(q+h) • p.2-p.1)
      map_zero' := by simp
      map_add' := by intro a b; ext <;> simp only [Prod.fst_add,Prod.snd_add,nsmul_add] <;> abel }
  have hs : Function.Surjective f := by
    rintro ⟨a,b⟩
    let t := smallShift h (b-a)
    refine ⟨(q • t-a,t),?_⟩
    have ht : h • t = b-a := exact_shift hh _
    apply Prod.ext
    · change q • t-(q • t-a)=a
      abel
    · change (q+h) • t-(q • t-a)=b
      rw [add_nsmul,ht]
      abel
  letI : Measure.IsAddHaarMeasure (volume : Measure CirclePair) :=
    inferInstanceAs (Measure.IsAddHaarMeasure ((volume : Measure UnitAddCircle).prod volume))
  apply f.measurePreserving _ hs rfl
  exact (((continuous_nsmul q).comp continuous_snd).sub continuous_fst).prodMk
    (((continuous_nsmul (q+h)).comp continuous_snd).sub continuous_fst)

/-- A shared shift of less than 1/q gives independent test phases at the
price of enlarging only the second arc, by h/q. -/
theorem pair_arc_mass {q h : ℕ} (hq : 0 < q) (hh : 0 < h) {x : ℝ} (hx : 0 ≤ x)
    (hshort : x+(h:ℝ)/q ≤ 1/2) :
    volume.real {θ : UnitAddCircle | q • θ ∈ forwardUnitArc x ∧
      (q+h) • θ ∈ forwardUnitArc x} ≤ x*(x+(h:ℝ)/q) := by
  let A := forwardUnitArc x
  let y := x+(h:ℝ)/q
  let B := forwardUnitArc y
  let S := {θ : UnitAddCircle | q • θ ∈ A ∧ (q+h) • θ ∈ A}
  let μ := (volume : Measure UnitAddCircle)
  have hqm : 0 < (q:ℝ) := Nat.cast_pos.mpr hq
  have hxhalf : x ≤ 1/2 := (le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) hqm.le)).trans hshort
  have hy : 0 ≤ y := add_nonneg hx (by positivity)
  have hmA := (isClosed_forwardUnitArc x).measurableSet
  have hmB := (isClosed_forwardUnitArc y).measurableSet
  have hmS : MeasurableSet S := (hmA.preimage ((continuous_nsmul q).measurable)).inter
    (hmA.preimage ((continuous_nsmul (q+h)).measurable))
  let f (p : CirclePair) := p.2-smallShift q p.1
  let l (p : CirclePair) := (q • p.2-p.1,(q+h) • p.2-p.1)
  have hmshift : Measurable (smallShift q) := (AddCircle.continuous_mk' 1).measurable.comp
    ((measurable_subtype_coe.comp (AddCircle.measurableEquivIoc 1 0).measurable).div_const _)
  have hf : MeasurePreserving f (μ.prod μ) μ := by
    have hs : MeasurePreserving (fun p : CirclePair => (p.1,p.2-smallShift q p.1)) (μ.prod μ) (μ.prod μ) :=
      (MeasurePreserving.id μ).skew_product (g := fun z θ => θ-smallShift q z)
        (measurable_snd.sub (hmshift.comp measurable_fst))
        (Filter.Eventually.of_forall fun z => (measurePreserving_sub_right μ (smallShift q z)).map_eq)
    exact (measurePreserving_snd (μ := μ) (ν := μ)).comp hs
  have sub : f ⁻¹' S ⊆ l ⁻¹' (A ×ˢ B) := by
    rintro ⟨z,θ⟩ ⟨h₁,h₂⟩
    change q • (θ-smallShift q z) ∈ A at h₁
    change (q+h) • (θ-smallShift q z) ∈ A at h₂
    rw [nsmul_sub,exact_shift hq] at h₁
    refine ⟨h₁,?_⟩
    obtain ⟨v,hv,hev⟩ := h₂
    have hz := (AddCircle.measurableEquivIoc 1 0 z).property
    have hz1 : liftTurn z ≤ 1 := by simpa only [liftTurn,zero_add] using hz.2
    have h₀ : 0 ≤ liftTurn z := hz.1.le
    let w := (h:ℝ)*(liftTurn z/q)
    have hw : w ≤ (h:ℝ)/q := by
      dsimp only [w]
      rw [←mul_div_assoc]
      exact div_le_div_of_nonneg_right (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz1 (Nat.cast_nonneg h)) hqm.le
    refine ⟨v+w,⟨add_nonneg hv.1 (mul_nonneg (Nat.cast_nonneg _) (div_nonneg h₀ hqm.le)),
      add_le_add hv.2 hw⟩,?_⟩
    change ((v+w:ℝ):UnitAddCircle) = (q+h) • θ-z
    rw [AddCircle.coe_add,hev,nsmul_sub,add_nsmul (smallShift q z) q h,exact_shift hq,
      show (w:UnitAddCircle)=h • smallShift q z from (multiple_shift q h z).symm]
    abel
  have hl : MeasurePreserving l (μ.prod μ) (μ.prod μ) := linear_pair_preserves q h hh
  have hle := (measure_mono (μ := μ.prod μ) sub)
  rw [hf.measure_preimage hmS.nullMeasurableSet,
    hl.measure_preimage (hmA.prod hmB).nullMeasurableSet,
    Measure.prod_prod] at hle
  have h := ENNReal.toReal_mono (by finiteness) hle
  simpa only [μ,Measure.real,A,B,ENNReal.toReal_mul,
    volume_forwardUnitArc (⟨x,hx,hxhalf⟩ : Icc (0:ℝ) (1/2)),
    volume_forwardUnitArc (⟨y,hy,hshort⟩ : Icc (0:ℝ) (1/2)),
    ENNReal.toReal_ofReal hx,ENNReal.toReal_ofReal hy] using h

#print axioms pair_arc_mass
end
end GaloisForLFunctions.HTGeometry.FirstClockIndex
