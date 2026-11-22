import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.CrossingWindows
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.IntervalPacking

/-! # Occupation of an arbitrary event on disjoint bands after scalar entries -/
open Filter MeasureTheory Set Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.SpanningOccupation
noncomputable section
open EmptyVisitFlux

private theorem band_measure (A : Set ℝ) (F : Finset ℝ) (a T h : ℝ) (hh : 0≤h)
    (ht : ∀ v∈F, a≤v ∧ v+h≤T) (hg : ∀ v∈F, ∀ w∈F, v<w → v+h≤w)
    (hA : ∀ v∈F, ∀ t∈Icc (h/2) h, v+t∈A) :
    (F.card:ℝ)*(h/2) ≤ volume.real (A∩Icc a T) := by
  classical
  let I (v : F) := Ico (v.val+h/2) (v.val+h)
  have hle {i j : F} (hij : i.val<j.val) : Disjoint (I i) (I j) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have h := hg i i.property j j.property hij
    change _≤x ∧ x<i.val+h at hx
    change j.val+h/2≤x ∧ _ at hy
    linarith only [h,hx.2,hy.1,hh]
  have hd : Pairwise (fun i j : F => Disjoint (I i) (I j)) := by
    intro i j h
    exact (lt_or_gt_of_ne (Subtype.coe_injective.ne h)).elim hle (fun hh => (hle hh).symm)
  have hsub : (⋃ v : F, I v) ⊆ A∩Icc a T := by
    rintro x hx
    obtain ⟨v,hv⟩ := mem_iUnion.mp hx
    change v.val+h/2≤x ∧ x<v.val+h at hv
    obtain ⟨h₁,h₂⟩ := ht v v.property
    have h := hA v v.property (x-v.val) ⟨by linarith only [hv.1],by linarith only [hv.2]⟩
    rw [show (v:ℝ)+(x-v)=x by ring] at h
    exact ⟨h,by linarith only [h₁,hv.1,hh],hv.2.le.trans h₂⟩
  have h := measureReal_mono (μ:=volume) hsub (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  rw [measureReal_iUnion_fintype hd (fun _ => measurableSet_Ico) (fun _ => measure_Ico_lt_top.ne)] at h
  simpa only [I,Real.volume_real_Ico,show ∀ x : ℝ, x+h-(x+h/2)=h/2 by intro x; ring,
    max_eq_left (half_nonneg hh),Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] using h

/-- If an event persists through the second half of a length-h band
after every entry, its eventual time share is at least one eighth of
the entry intensity times h. The observation origin is arbitrary. -/
theorem event_fraction_of_entries {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (E : I→ℝ) (hi : MaximallyProjectiveEnergy E) (A : Set ℝ) {x h : ℝ}
    (hx : 0<x) (hs : x<1/2) (hh : 0<h) (hR : 0<pairTurnRate E)
    (hgap : ∀ v w : ℝ, v<w → visitEntry (fun i => E i/(2*π)) x v →
      visitEntry (fun i => E i/(2*π)) x w → v+h≤w)
    (hA : ∀ v : ℝ, visitEntry (fun i => E i/(2*π)) x v → ∀ t∈Icc (h/2) h, v+t∈A)
    (a : ℝ) : ∀ᶠ T : ℝ in atTop,
      h*(x^(Fintype.card I-2)*pairTurnRate E)/8 ≤ volume.real (A∩Icc a T)/(T-a) := by
  classical
  let R := x^(Fintype.card I-2)*pairTurnRate E
  have hpos : 0<R := mul_pos (pow_pos hx _) hR
  have hc := (entries_after_rate E hi hx hs a).eventually_const_lt (half_lt_self hpos)
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp hc
  filter_upwards [eventually_ge_atTop (max T₀ a+2*h+1)] with T hT
  have htime : T₀≤T-h := by linarith only [hT,le_max_left T₀ a,hh]
  have ha : 0<T-h-a := by linarith only [hT,le_max_right T₀ a,hh]
  have hhalf : (T-a)/2≤T-h-a := by linarith only [hT,le_max_right T₀ a]
  let F := entriesAfter E x a (T-h)
  have hcount : R/2*(T-h-a)<(F.card:ℝ) := (lt_div_iff₀ ha).mp (hT₀ _ htime)
  have mark (v : ℝ) (hv : v∈F) : a<v ∧ v≤T-h ∧ visitEntry (fun i => E i/(2*π)) x v := by
    obtain ⟨hv',hn⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨h0,hb,he⟩ := (mem_entryDates E hx.le hs v (T-h)).mp hv'
    exact ⟨lt_of_not_ge (fun hl => hn ((mem_entryDates E hx.le hs v a).mpr ⟨h0,hl,he⟩)),hb,he⟩
  have hpack := band_measure A F a T h hh.le
    (fun v hv => ⟨(mark v hv).1.le,by linarith only [(mark v hv).2.1]⟩)
    (fun v hv w hw hlt => hgap v w hlt (mark v hv).2.2 (mark w hw).2.2)
    (fun v hv => hA v (mark v hv).2.2)
  apply (le_div_iff₀ (show 0<T-a by linarith only [ha,hh])).mpr
  have h₁ := mul_le_mul_of_nonneg_left hhalf (half_pos hpos).le
  have h₂ := mul_le_mul_of_nonneg_right (h₁.trans hcount.le) (half_pos hh).le
  linarith only [h₂,hpack]

end
end GaloisForLFunctions.HTGeometry.SpanningOccupation
