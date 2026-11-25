import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.CoarseVisits.PrecisionFloor

/-! # Measurability of the first physical visit with variable tolerance -/

open Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels
open PrescribedTimes PrecisionReturns ExactContacts.CoarseVisits
noncomputable section

/-- First-visit date as a jointly measurable function of the couplings
and the positive tolerance, extended by its origin at nonpositive errors. -/
def visitParameter (n s : ℕ) (a : ℝ) (p : (PrefixIndex n → ℝ) × ℝ) : ℝ :=
  if 0 < p.2 then firstVisit (prefixGenerator n p.1) a s p.2 else a

private theorem closed_visit_before {X : Type*} [TopologicalSpace X] (f : X × ℝ → ℝ)
    (hf : Continuous f) (a c : ℝ) :
    IsClosed {p : X × ℝ | ∃ t∈Icc a c, f (p.1,t)≤p.2} := by
  let K := Icc a c
  letI : CompactSpace ↥K := inferInstanceAs (CompactSpace ↥(Icc a c))
  let Z := {p : (X × ℝ) × ↥K | f (p.1.1,p.2.val)≤p.1.2}
  have hz : IsClosed Z := isClosed_le (hf.comp
    ((continuous_fst.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)))
    (continuous_snd.comp continuous_fst)
  have he : Prod.fst '' Z = {p : X × ℝ | ∃ t∈Icc a c, f (p.1,t)≤p.2} := by
    ext p
    constructor
    · rintro ⟨⟨_,t⟩,ht,rfl⟩
      exact ⟨t.val,t.property,ht⟩
    · rintro ⟨t,ht,hf⟩
      exact ⟨(p,⟨t,ht⟩),hf,rfl⟩
  rw [←he]
  exact isClosedMap_fst_of_compactSpace _ hz

private theorem first_le_iff (n s : ℕ) (x : PrefixIndex n → ℝ) (a c : ℝ) {e : ℝ} (he : 0<e) :
    firstVisit (prefixGenerator n x) a s e≤c ↔ ∃ t∈Icc a c, pathGateDistance n s x t≤e := by
  let H := prefixGenerator n x
  have hv := firstVisit_isLeast H a s he
  have hfit (t : ℝ) : HasProjectiveCircuitApproximation (n+2) e s (unitaryEvolution H.val t) ↔
      pathGateDistance n s x t≤e := hasProjectiveCircuitApproximation_iff_infDist _ s e
  constructor
  · intro hc
    exact ⟨_,⟨hv.1.1,hc⟩,(hfit _).mp hv.1.2⟩
  · rintro ⟨t,ht,hw⟩
    exact (hv.2 ⟨ht.1,(hfit t).mpr hw⟩).trans ht.2

theorem measurable_visitParameter (n s : ℕ) (a : ℝ) : Measurable (visitParameter n s a) := by
  apply measurable_of_Iic
  intro c
  let X := (PrefixIndex n → ℝ) × ℝ
  let A := {p : X | 0<p.2}
  let B := {p : X | ∃ t∈Icc a c, pathGateDistance n s p.1 t≤p.2}
  have hA : MeasurableSet A := measurableSet_lt measurable_const measurable_snd
  have hB : MeasurableSet B := (closed_visit_before _ (continuous_distance n s) a c).measurableSet
  have he : visitParameter n s a ⁻¹' Iic c=(A ∩ B) ∪ (Aᶜ ∩ {p : X | a≤c}) := by
    ext p
    change (if 0<p.2 then firstVisit (prefixGenerator n p.1) a s p.2 else a)≤c ↔
      (0<p.2 ∧ ∃ t∈Icc a c, pathGateDistance n s p.1 t≤p.2) ∨ (¬0<p.2) ∧ a≤c
    by_cases hp : 0<p.2
    · rw [if_pos hp]
      simpa only [hp,true_and,not_true_eq_false,false_and,or_false] using first_le_iff n s p.1 a c hp
    · rw [if_neg hp]
      simp only [hp,false_and,not_false_eq_true,true_and,false_or]
  rw [he]
  exact (hA.inter hB).union (hA.compl.inter (MeasurableSet.const _))

/-- A first visit from outside the closed tube is already the first
visit from some rational point in the open excursion preceding it. -/
theorem rational_visit_origin {N : ℕ} (H : selfAdjoint (PrecisionReturns.Register N))
    (a : ℝ) (s : ℕ) {e : ℝ} (he : 0 < e) (hout : e < orbitCircuitDistance H s a) :
    ∃ q : ℚ, e < orbitCircuitDistance H s q ∧ firstVisit H (q:ℝ) s e=firstVisit H a s e := by
  let v := firstVisit H a s e
  have hl := firstVisit_isLeast H a s he
  have hv : orbitCircuitDistance H s v=e := firstVisit_distance H a s he hout
  have hav : a < v := lt_of_le_of_ne hl.1.1 (fun h =>
    hout.ne' ((congrArg (orbitCircuitDistance H s) h).trans hv))
  obtain ⟨q,hq,hqv⟩ := exists_rat_btwn hav
  have hqfar : e < orbitCircuitDistance H s q := by
    by_contra! hn
    exact hqv.not_ge (hl.2 ⟨hq.le,(hasProjectiveCircuitApproximation_iff_infDist ..).mpr hn⟩)
  have hqleast := firstVisit_isLeast H (q:ℝ) s he
  exact ⟨q,hqfar,le_antisymm (hqleast.2 ⟨hqv.le,hl.1.2⟩)
    (hl.2 ⟨hq.le.trans hqleast.1.1,hqleast.1.2⟩)⟩

#print axioms measurable_visitParameter
#print axioms rational_visit_origin
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels
