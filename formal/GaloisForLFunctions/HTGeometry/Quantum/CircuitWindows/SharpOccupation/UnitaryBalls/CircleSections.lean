import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Expansion of a proper circle section by an arc -/
open MeasureTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
noncomputable section

/-- A segment of length g about each point of A lies in B. If B omits
one point, dilation about the cut bounds the Haar mass of A by (1-g)|B|. -/
theorem circle_section_bound {A B : Set UnitAddCircle} (hA : MeasurableSet A)
    (hB : MeasurableSet B) {g : ℝ} (hg : 0≤g) (hg' : g<1)
    (cut : UnitAddCircle) (hcut : cut ∉ B)
    (hseg : ∀ x∈A, ∀ t∈Icc (0:ℝ) g, x+(t:UnitAddCircle)∈B) :
    volume A ≤ ENNReal.ofReal (1-g)*volume B := by
  let lift (S : Set UnitAddCircle) := ((fun v : ℝ => (v:UnitAddCircle)+cut) ⁻¹' S) ∩ Ioc 0 1
  have hm (S : Set UnitAddCircle) (hs : MeasurableSet S) : volume S=volume (lift S) := by
    let e (v : ℝ) : UnitAddCircle := (v:UnitAddCircle)+cut
    have hp : MeasurePreserving e (volume.restrict (Ioc 0 1)) volume := by
      have h := (measurePreserving_add_right (volume : Measure UnitAddCircle) cut).comp (UnitAddCircle.measurePreserving_mk 0)
      rw [zero_add] at h
      convert h using 1
      funext v
      rfl
    have hh := hp.measure_preimage hs.nullMeasurableSet
    rw [Measure.restrict_apply (hs.preimage hp.measurable)] at hh
    exact hh.symm
  let a := 1-g
  have ha : 0<a := sub_pos.mpr hg'
  have hsub : lift A ⊆ (a⁻¹ * ·) ⁻¹' lift B := by
    intro v hv
    obtain ⟨hmem,hpos,hv₁⟩ := hv
    have hmove (t : ℝ) (ht : t∈Icc (0:ℝ) g) : ((v+t:ℝ):UnitAddCircle)+cut ∈ B := by
      rw [AddCircle.coe_add,add_right_comm]
      exact hseg _ hmem t ht
    have hvmax : v<a := by
      by_contra! h
      have ht : 1-v ∈ Icc (0:ℝ) g := ⟨sub_nonneg.mpr hv₁,by dsimp only [a] at h; linarith only [h]⟩
      have hc := hmove _ ht
      rw [show v+(1-v)=(1:ℝ) by ring,AddCircle.coe_period,zero_add] at hc
      exact hcut hc
    let w := a⁻¹*v
    have hw : 0<w := mul_pos (inv_pos.mpr ha) hpos
    have hwa : w*a=v := by dsimp only [w]; field_simp [ha.ne']
    have hw₁ : w≤1 := (mul_le_mul_iff_left₀ ha).mp (by rw [hwa,one_mul]; exact hvmax.le)
    have he : w-v=g*w := by rw [←hwa]; dsimp only [a]; ring
    have ht : w-v∈Icc (0:ℝ) g := by
      rw [he]
      exact ⟨mul_nonneg hg hw.le,mul_le_of_le_one_right hg hw₁⟩
    refine ⟨?_,hw,hw₁⟩
    change (w:UnitAddCircle)+cut ∈ B
    simpa only [add_sub_cancel] using hmove (w-v) ht
  rw [hm A hA,hm B hB]
  apply (measure_mono hsub).trans_eq
  rw [Real.volume_preimage_mul_left (inv_ne_zero ha.ne'),inv_inv,abs_of_pos ha]

#print axioms circle_section_bound
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
