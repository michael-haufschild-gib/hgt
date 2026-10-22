import GaloisForLFunctions.RHTower.CCM.CCMSoninFiniteWordFaithfulness

noncomputable section

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace


local infixl:70 " ⋆ " => composeSoninWindowStates

/-- Every idempotent canonical state is fixed by the canonical involution. -/
theorem SoninWindowState.inverse_eq_self_of_idempotent
    {a : ℝ} (s : SoninWindowState a)
    (h : composeSoninWindowStates s s = s) : s.inverse = s := by
  cases s with
  | zero => rfl
  | live d =>
      have hcompose : composeSoninLiveWindows d d = SoninWindowState.live d := by
        simpa only [composeSoninWindowStates] using h
      have hscaleSq : d.scale * d.scale = d.scale := by
        by_cases hlt : soninLiveComposeFloor d d < soninLiveComposeCeiling d d
        · rw [composeSoninLiveWindows, dif_pos hlt] at hcompose
          have hdatum := SoninWindowState.live.inj hcompose
          have hscale := congrArg SoninLiveWindow.scale hdatum
          simpa only [soninLiveComposeScale] using hscale
        · rw [composeSoninLiveWindows, dif_neg hlt] at hcompose
          cases hcompose
      have hx : d.scale = 1 := by
        nlinarith [d.scale_pos]
      change SoninWindowState.live d.inverse = SoninWindowState.live d
      congr 1
      apply SoninLiveWindow.ext_coordinates
      · simp [SoninLiveWindow.inverse, hx]
      · simp [SoninLiveWindow.inverse, hx]
      · simp [SoninLiveWindow.inverse, hx]

/-- All idempotents of the canonical Sonin state semigroup commute. -/
theorem composeSoninWindowStates_idempotents_comm
    {a : ℝ} (ha : 0 < a) (e f : SoninWindowState a)
    (he : composeSoninWindowStates e e = e)
    (hf : composeSoninWindowStates f f = f) :
    composeSoninWindowStates e f = composeSoninWindowStates f e := by
  have heInv : e.inverse = e := e.inverse_eq_self_of_idempotent he
  have hfInv : f.inverse = f := f.inverse_eq_self_of_idempotent hf
  have hcomm := composeSoninWindowStates_range_comm ha e f
  rw [heInv, hfInv, he, hf] at hcomm
  exact hcomm

/-- The canonical involution gives the unique algebraic inverse of every state. -/
theorem SoninWindowState.inverse_unique
    {a : ℝ} (ha : 0 < a) (s t : SoninWindowState a)
    (hsts : (s ⋆ t) ⋆ s = s)
    (htst : (t ⋆ s) ⋆ t = t) : t = s.inverse := by
  let z := s.inverse
  have hszs : (s ⋆ z) ⋆ s = s := by
    exact composeSoninWindowStates_inverse_regular ha s
  have hzsz : (z ⋆ s) ⋆ z = z := by
    exact composeSoninWindowStates_inverse_regular' ha s
  have htsIdem : (t ⋆ s) ⋆ (t ⋆ s) = t ⋆ s := by
    rw [← composeSoninWindowStates_assoc ha (t ⋆ s) t s, htst]
  have hzsIdem : (z ⋆ s) ⋆ (z ⋆ s) = z ⋆ s := by
    simpa [z] using composeSoninWindowStates_source_idempotent ha s
  have hstIdem : (s ⋆ t) ⋆ (s ⋆ t) = s ⋆ t := by
    rw [← composeSoninWindowStates_assoc ha (s ⋆ t) s t, hsts]
  have hszIdem : (s ⋆ z) ⋆ (s ⋆ z) = s ⋆ z := by
    simpa [z] using composeSoninWindowStates_range_idempotent ha s
  have hleftComm : (t ⋆ s) ⋆ (z ⋆ s) = (z ⋆ s) ⋆ (t ⋆ s) :=
    composeSoninWindowStates_idempotents_comm ha (t ⋆ s) (z ⋆ s)
      htsIdem hzsIdem
  have hrightComm : (s ⋆ t) ⋆ (s ⋆ z) = (s ⋆ z) ⋆ (s ⋆ t) :=
    composeSoninWindowStates_idempotents_comm ha (s ⋆ t) (s ⋆ z)
      hstIdem hszIdem
  have htCommon : t = (z ⋆ s) ⋆ t := by
    calc
      t = (t ⋆ s) ⋆ t := htst.symm
      _ = (t ⋆ ((s ⋆ z) ⋆ s)) ⋆ t := by rw [hszs]
      _ = ((t ⋆ s) ⋆ (z ⋆ s)) ⋆ t := by
        simp only [composeSoninWindowStates_assoc ha]
      _ = ((z ⋆ s) ⋆ (t ⋆ s)) ⋆ t := by rw [hleftComm]
      _ = (z ⋆ ((s ⋆ t) ⋆ s)) ⋆ t := by
        simp only [composeSoninWindowStates_assoc ha]
      _ = (z ⋆ s) ⋆ t := by rw [hsts]
  have hzCommon : z = (z ⋆ s) ⋆ t := by
    calc
      z = (z ⋆ s) ⋆ z := hzsz.symm
      _ = (z ⋆ ((s ⋆ t) ⋆ s)) ⋆ z := by rw [hsts]
      _ = z ⋆ ((s ⋆ t) ⋆ (s ⋆ z)) := by
        simp only [composeSoninWindowStates_assoc ha]
      _ = z ⋆ ((s ⋆ z) ⋆ (s ⋆ t)) := by rw [hrightComm]
      _ = ((z ⋆ s) ⋆ z) ⋆ (s ⋆ t) := by
        simp only [composeSoninWindowStates_assoc ha]
      _ = z ⋆ (s ⋆ t) := by rw [hzsz]
      _ = (z ⋆ s) ⋆ t := by
        rw [composeSoninWindowStates_assoc ha]
  exact htCommon.trans hzCommon.symm

/-- Every canonical state has a unique semigroup inverse. -/
theorem SoninWindowState.existsUnique_inverse
    {a : ℝ} (ha : 0 < a) (s : SoninWindowState a) :
    ∃! t : SoninWindowState a,
      (s ⋆ t) ⋆ s = s ∧ (t ⋆ s) ⋆ t = t := by
  refine ⟨s.inverse, ?_, ?_⟩
  · exact ⟨composeSoninWindowStates_inverse_regular ha s,
      composeSoninWindowStates_inverse_regular' ha s⟩
  · intro t ht
    exact s.inverse_unique ha t ht.1 ht.2

/-- **Exact CCM Sonin inverse-semigroup theorem.**  For each positive aperture the canonical
zero/live states form an inverse semigroup: composition is associative, zero is absorbing, every
state has the displayed unique inverse, and all idempotents commute.  Its operator realization is
faithful modulo compact operators and carries inversion to Hilbert-space adjunction. -/
theorem ccmSoninWindowState_inverseSemigroup
    {a : ℝ} (ha : 0 < a) :
    (∀ r s t : SoninWindowState a, (r ⋆ s) ⋆ t = r ⋆ (s ⋆ t)) ∧
    (∀ s : SoninWindowState a,
      SoninWindowState.zero ⋆ s = SoninWindowState.zero ∧
        s ⋆ SoninWindowState.zero = SoninWindowState.zero) ∧
    (∀ s : SoninWindowState a, ∃! t : SoninWindowState a,
      (s ⋆ t) ⋆ s = s ∧ (t ⋆ s) ⋆ t = t) ∧
    (∀ e f : SoninWindowState a,
      e ⋆ e = e → f ⋆ f = f → e ⋆ f = f ⋆ e) ∧
    (∀ s t : SoninWindowState a, (s.operator =ₖ t.operator ↔ s = t)) ∧
    (∀ s : SoninWindowState a, s.inverse.operator = s.operator†) := by
  exact ⟨composeSoninWindowStates_assoc ha,
    fun s => ⟨composeSoninWindowStates_zero_left s,
      composeSoninWindowStates_zero_right s⟩,
    SoninWindowState.existsUnique_inverse ha,
    fun e f => composeSoninWindowStates_idempotents_comm ha e f,
    fun s t => s.operator_compactEq_iff ha t,
    SoninWindowState.inverse_operator⟩

end RHTower
