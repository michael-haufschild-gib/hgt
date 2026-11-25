import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.FirstVisitSchedule

/-! # The first complete expensive interval following an exit at the same tolerance -/

open Set Metric Filter Topology Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
open PrecisionReturns
noncomputable section

/-- If expensive times accumulate from the right, the next affordable
date strictly after the origin is attained. The entire intervening open
interval exceeds the prescribed error, even when the origin is affordable. -/
theorem first_episode_end {N : ℕ} (H : selfAdjoint (Square (Bits N))) (s : ℕ) {ε : ℝ}
    (hε : 0<ε) (a : ℝ) (hout : ∀ b>a, ∃ t∈Ioo a b, ε<orbitCircuitDistance H s t) :
    ∃ v>a, orbitCircuitDistance H s v=ε ∧
      IsLeast {t | a<t ∧ orbitCircuitDistance H s t≤ε} v ∧
      ∀ t∈Ioo a v, ε<orbitCircuitDistance H s t := by
  let S := {v | ∃ t∈Ioo a (a+1), ε<orbitCircuitDistance H s t ∧ firstVisit H t s ε=v}
  have hfin : S.Finite := (finite_firstVisit_schedule H s hε a (a+1)).subset (by
    rintro v ⟨t,ht,hhigh,hv⟩
    exact ⟨s,le_rfl,t,⟨ht.1.le,ht.2.le⟩,hhigh,hv⟩)
  have hex : S.Nonempty := by
    obtain ⟨t,ht,hhigh⟩ := hout (a+1) (by linarith)
    exact ⟨_,t,ht,hhigh,rfl⟩
  obtain ⟨v,hv,hmin⟩ := hfin.isCompact.exists_isMinOn hex continuous_id.continuousOn
  obtain ⟨t,ht,hh,rfl⟩ := hv
  obtain ⟨htv,he,_⟩ := firstVisit_left_contact H s t hε hh
  have hav := ht.1.trans htv
  have bound (z : ℝ) (haz : a<z) (hz : orbitCircuitDistance H s z≤ε) : firstVisit H t s ε≤z := by
    obtain ⟨u,hu,hh'⟩ := hout (min z (a+1)) (lt_min haz (by linarith))
    have hu' := hu.2.trans_le (min_le_right ..)
    have hl := firstVisit_isLeast H u s hε
    have hb : firstVisit H u s ε≤z := hl.2 ⟨hu.2.le.trans (min_le_left ..),
      (hasProjectiveCircuitApproximation_iff_infDist ..).mpr hz⟩
    exact (hmin (show firstVisit H u s ε∈S from ⟨u,⟨hu.1,hu'⟩,hh',rfl⟩)).trans hb
  exact ⟨_,hav,he,⟨⟨hav,he.le⟩,fun _ h => bound _ h.1 h.2⟩,
    fun z hz => lt_of_not_ge fun h => hz.2.not_ge (bound z hz.1 h)⟩

/-- Every positive-error physical gate budget is either affordable
throughout some right neighborhood or has an attained first return
separated from the origin by a wholly expensive open interval. -/
theorem affordable_or_expensive_right {N : ℕ} (H : selfAdjoint (Square (Bits N))) (s : ℕ)
    {ε : ℝ} (hε : 0<ε) (a : ℝ) :
    (∃ b>a, ∀ t∈Ioo a b, orbitCircuitDistance H s t≤ε) ∨
      ∃ v>a, orbitCircuitDistance H s v=ε ∧
        IsLeast {t | a<t ∧ orbitCircuitDistance H s t≤ε} v ∧
        ∀ t∈Ioo a v, ε<orbitCircuitDistance H s t := by
  by_cases h : ∃ b>a, ∀ t∈Ioo a b, orbitCircuitDistance H s t≤ε
  · exact Or.inl h
  push Not at h
  exact Or.inr (first_episode_end H s hε a h)

#print axioms affordable_or_expensive_right
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
