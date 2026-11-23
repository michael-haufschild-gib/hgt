import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.WindowSignal

/-! # A measurable local certificate for detection on the full physical path -/
open MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

def windowLaw (L : ℕ) : Measure (WindowRows L) := Measure.infinitePi fun _ => gaussianReal 0 1
instance (L : ℕ) : IsProbabilityMeasure (windowLaw L) := by unfold windowLaw; infer_instance

theorem readWindow_preserving (j L : ℕ) :
    MeasurePreserving (readWindow j L) pathPauliDisorderLaw (windowLaw L) := by
  let g (q : Fin L × PathPauliDirections) := (j+q.1.val,q.2)
  have hg : Function.Injective g := by
    rintro ⟨i,d⟩ ⟨k,d'⟩ h
    obtain ⟨hh,hd⟩ := Prod.mk.inj h
    exact Prod.ext (Fin.ext (Nat.add_left_cancel hh)) hd
  exact ⟨measurable_pi_lambda _ fun _ => measurable_pi_apply _,
    Measure.map_infinitePi_infinitePi_of_inj hg⟩

/-- A local test fails when a guard strip is missing or the signal of
the zero-extended sample falls below its threshold. -/
def windowFailure {n : ℕ} (e : Fin (n+1)) (R : ℕ) (γ r t : ℝ) : Set (WindowRows (2*R+2)) :=
  {x | let ω := extendWindow (e.val-R) x
    ω∈failedStrips γ R e.val ∨ |bondSignal e (pathPauliDisorderShell ω n) t|≤2*r}

theorem measurable_windowFailure {n : ℕ} (e : Fin (n+1)) (R : ℕ) (γ r t : ℝ) :
    MeasurableSet (windowFailure e R γ r t) := by
  have hs : MeasurableSet (failedStrips γ R e.val) :=
    (measurable_absentStrip ..).union (measurable_absentStrip ..)
  exact (measurable_extendWindow _ hs).union
    (measurableSet_le ((measurable_bondSignal e t).comp (measurable_extendWindow _)).abs measurable_const)

private theorem window_guards (ω : PathPauliDisorder) (R e : ℕ) (γ : ℝ) (he : R≤e) :
    extendWindow (e-R) (readWindow (e-R) (2*R+2) ω)∈failedStrips γ R e ↔
      ω∈failedStrips γ R e := by
  let v := extendWindow (e-R) (readWindow (e-R) (2*R+2) ω)
  have hrow (k : ℕ) (hl : e-R≤k) (hr : k<e-R+(2*R+2)) : weakRow γ v k ↔ weakRow γ ω k := by
    simp only [weakRow,bondRow,v,recover_window ω hl hr]
  have h₁ (i : Fin R) := hrow (e-R+i.val) (by omega) (by have := i.isLt; omega)
  have h₂ (i : Fin R) := hrow (e+1+i.val) (by omega) (by have := i.isLt; omega)
  change ((∀ i : Fin R, ¬weakRow γ v (e-R+i.val)) ∨ (∀ i : Fin R, ¬weakRow γ v (e+1+i.val))) ↔ _
  simp only [h₁,h₂]
  rfl

/-- Passing the test certifies both physical guard strips and a signal
on the full chain, for every exterior compatible with the window. -/
theorem signal_of_passing_window {n R : ℕ} (ω : PathPauliDisorder) (e : Fin (n+1))
    {γ r t : ℝ} (hl : R≤e.val) (hr : e.val+R≤n) (herr : 72*|t| *γ≤r)
    (h : readWindow (e.val-R) (2*R+2) ω∉windowFailure e R γ r t) :
    ω∉failedStrips γ R e.val ∧ r < |bondSignal e (pathPauliDisorderShell ω n) t| := by
  have hs : ω∉failedStrips γ R e.val := fun hh => h (Or.inl ((window_guards ω R e.val γ hl).mpr hh))
  refine ⟨hs,?_⟩
  let v := extendWindow (e.val-R) (readWindow (e.val-R) (2*R+2) ω)
  have hbig : 2*r < |bondSignal e (pathPauliDisorderShell v n) t| := lt_of_not_ge fun hh => h (Or.inr hh)
  have hd := (masked_signal_error ω e t γ hl hr hs).trans herr
  have hgap := abs_sub_abs_le_abs_sub (bondSignal e (pathPauliDisorderShell v n) t)
    (bondSignal e (pathPauliDisorderShell ω n) t)
  linarith only [hbig,hgap.trans hd]

/-- The marginal failure probability is bounded by the two strip tails
and the physical small-signal probability. This bound is uniform in the
ambient prefix and the location of its interior bond. -/
theorem window_failure_probability {n R : ℕ} (e : Fin (n+1)) {γ r t p q : ℝ}
    (hl : R≤e.val) (hr : e.val+R≤n) (herr : 72*|t| *γ≤r)
    (hs : ∀ j, pathPauliDisorderLaw.real (absentStrip γ R j)≤q)
    (hp : pathPauliDisorderLaw.real {ω | |bondSignal e (pathPauliDisorderShell ω n) t|≤3*r} ≤ p) :
    (windowLaw (2*R+2)).real (windowFailure e R γ r t) ≤ 2*q+p := by
  let A := failedStrips γ R e.val
  let B := {ω | |bondSignal e (pathPauliDisorderShell ω n) t|≤3*r}
  have hA : pathPauliDisorderLaw.real A≤2*q :=
    (measureReal_union_le _ _).trans ((add_le_add (hs _) (hs _)).trans_eq (two_mul q).symm)
  rw [←(readWindow_preserving (e.val-R) (2*R+2)).measureReal_preimage
    (measurable_windowFailure ..).nullMeasurableSet]
  apply (measureReal_mono (s₂:=A∪B) ?_ (measure_ne_top _ _)).trans
    ((measureReal_union_le A B).trans (add_le_add hA hp))
  intro ω hw
  by_cases h : ω∈A
  · exact Or.inl h
  · right
    let v := extendWindow (e.val-R) (readWindow (e.val-R) (2*R+2) ω)
    rcases hw with hc|hc
    · exact (h ((window_guards ω R e.val γ hl).mp hc)).elim
    · have hd := (masked_signal_error ω e t γ hl hr h).trans herr
      have ht := abs_sub_abs_le_abs_sub (bondSignal e (pathPauliDisorderShell ω n) t)
        (bondSignal e (pathPauliDisorderShell v n) t)
      rw [abs_sub_comm (bondSignal e (pathPauliDisorderShell ω n) t)] at ht
      change |bondSignal e (pathPauliDisorderShell v n) t|≤2*r at hc
      change |bondSignal e (pathPauliDisorderShell ω n) t|≤3*r
      linarith only [hc,ht.trans hd]

#print axioms window_failure_probability
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
