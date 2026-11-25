import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.JointActions
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.ConditionalEntries

/-! # Countable ordered-energy formulas for every genuine scalar entry date -/

open MeasureTheory Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes.JointDates
open PrecisionReturns
noncomputable section

abbrev generator (k : ℕ) (ω : PathPauliDisorder) : selfAdjoint (Register (k+3)) :=
  ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩

def candidate (k : ℕ) (e : ℝ) (n : ℤ) (m : Config k → ℤ) (ω : PathPauliDisorder) : ℝ :=
  (2*π)*((n:ℝ)+SharpOccupation.physicalArc e)/action k m ω

theorem measurable_candidate (k : ℕ) (e : ℝ) (n : ℤ) (m : Config k → ℤ) :
    Measurable (candidate k e n m) :=
  measurable_const.div (continuous_action k m).measurable

theorem candidate_before {j k : ℕ} (h : j<k) (e : ℝ) (n : ℤ) (m : Config j → ℤ) (ω) :
    candidate j e n m (eraseTerminal k ω)=candidate j e n m ω := by
  simp only [candidate,action,energy_before h]

/-- Each genuine entry realizes one of these measurable dates, even when
the exterior origin was chosen after inspecting every coupling. -/
theorem entry_candidate (k : ℕ) (ω : PathPauliDisorder) {a e : ℝ} (ha : 0<a)
    (he : e∈Ioo (0:ℝ) (sqrt 2)) (hout : e<orbitCircuitDistance (generator k ω) 0 a) :
    ∃ (n : ℤ) (q : Config k → ℤ), candidate k e n q ω=firstVisit (generator k ω) a 0 e := by
  let H := generator k ω
  let v := firstVisit H a 0 e
  obtain ⟨hv,m,n,_,_,hm⟩ := first_entry_action H ha he.1 he.2 hout
  obtain ⟨b,hb⟩ := ordered_at_zero k ω
  let q := m ∘ b
  have hA : action k q ω=(2*π)*((n:ℝ)+SharpOccupation.physicalArc e)/v := by
    unfold action
    rw [hb]
    exact (Equiv.sum_comp b (fun i => (m i:ℝ)*H.2.isHermitian.eigenvalues i)).trans hm
  have hx := (SharpOccupation.physicalArc_spec he.1 he.2).1
  have hZ : (n:ℝ)+SharpOccupation.physicalArc e≠0 := by
    by_cases hn : 0≤n
    · exact (add_pos_of_nonneg_of_pos (by exact_mod_cast hn : (0:ℝ)≤n) hx.1).ne'
    · have hh : (n:ℝ)≤-1 := by exact_mod_cast (show n≤-1 by omega)
      linarith only [hh,hx.2]
  have hc := mul_ne_zero (mul_ne_zero (by norm_num : (2:ℝ)≠0) pi_ne_zero) hZ
  refine ⟨n,q,?_⟩
  rw [candidate,hA]
  change _=v
  field_simp [hc,hv.ne']

#print axioms entry_candidate
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes.JointDates
