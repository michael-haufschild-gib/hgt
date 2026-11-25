import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FrequencyAvoidance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.FirstVisit

/-! # A single boundary field avoids prescribed first empty-return dates -/
open Matrix MeasureTheory Real Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section
open EmptyVisitFlux PrecisionReturns
private abbrev Basis (k : ℕ) := Fin (k+3)→Bool
private abbrev Reg (k : ℕ) := Matrix (Basis k) (Basis k) ℂ

/-- An ordered difference of two distinct levels is a nonzero balanced integer action. -/
theorem gap_packet {I : Type*} [Fintype I] [DecidableEq I] (E : I→ℝ) {i j : I} (hij : i≠j) :
    ∃ m : I→ℤ, m≠0 ∧ (∑ l, m l)=0 ∧ (∑ l, (m l:ℝ)*E l)=E i-E j := by
  let δ (a l : I) : ℤ := if a=l then 1 else 0
  let m (l : I) := δ i l-δ j l
  have hw (a : I) : (∑ l, (δ a l:ℝ)*E l)=E a := by
    simp [δ,apply_ite,ite_mul]
  have hb (a : I) : (∑ l, δ a l)=1 := by simp [δ]
  refine ⟨m,?_,?_,?_⟩
  · intro he
    have h := congrFun he i
    simp [m,δ,hij.symm] at h
  · simp only [m,Finset.sum_sub_distrib,hb,sub_self]
  · simp only [m,Int.cast_sub,sub_mul,Finset.sum_sub_distrib,hw]

private theorem face_gap {I : Type*} (E : I→ℝ) {r v : ℝ} (hv : 0<v) {i j : I}
    (hf : pairFace (forwardUnitArc r) (fun a => -E a/(2*π)) r v i j) :
    ∃ m : ℤ, E i-E j=(2*π)*((m:ℝ)+r)/v := by
  let b := v*(E i-E j)/(2*π)
  have hb : (b:UnitAddCircle)=(r:UnitAddCircle) := by
    rw [←hf.2.1,flow,flow,←AddCircle.coe_sub]
    congr 1
    dsimp only [b]
    ring
  have h0 : ((b-r:ℝ):UnitAddCircle)=0 := by rw [AddCircle.coe_sub,hb,sub_self]
  obtain ⟨m,hm⟩ := (AddCircle.coe_eq_zero_iff 1).mp h0
  rw [zsmul_eq_mul,mul_one] at hm
  refine ⟨m,?_⟩
  rw [show (m:ℝ)+r=b by linarith only [hm]]
  dsimp only [b]
  field_simp

/-- The gap of the closing pair at a first scalar entry fixes the
absolute date up to its integer winding number. -/
theorem first_entry_gap {I : ℕ} (H : selfAdjoint (Matrix (Fin I→Bool) (Fin I→Bool) ℂ))
    {A ε : ℝ} (hA : 0<A) (hε : 0<ε) (hs : ε<sqrt 2) (hfar : ε<orbitCircuitDistance H 0 A) :
    let v := firstVisit H A 0 ε
    let E := H.property.isHermitian.eigenvalues
    0<v ∧ ∃ (i j : Fin I→Bool) (n : ℤ), i≠j ∧ E i-E j=(2*π)*((n:ℝ)+SharpOccupation.physicalArc ε)/v := by
  intro v E
  have hr := (SharpOccupation.physicalArc_spec hε hs).1
  obtain ⟨hv,he⟩ := FirstGate.first_empty_entry_of_outside H hε hs hfar
  obtain ⟨i,j,hf⟩ := (entry_iff_closed_face _ hr.1.le hr.2).mp he
  have hij : i≠j := by rintro rfl; exact (lt_irrefl _ hf.1)
  obtain ⟨n,hn⟩ := face_gap E (hA.trans hv) hf
  exact ⟨hA.trans hv,i,j,n,hij,hn⟩

/-- The absolute first entry is witnessed by one winding number and the
balanced gap of its two endpoint levels. -/
theorem first_entry_action {I : ℕ} (H : selfAdjoint (Matrix (Fin I→Bool) (Fin I→Bool) ℂ))
    {A ε : ℝ} (hA : 0<A) (hε : 0<ε) (hs : ε<sqrt 2) (hfar : ε<orbitCircuitDistance H 0 A) :
    let v := firstVisit H A 0 ε
    0<v ∧ ∃ (m : (Fin I→Bool)→ℤ) (n : ℤ), m≠0 ∧ (∑ i, m i)=0 ∧
      (∑ i, (m i:ℝ)*H.property.isHermitian.eigenvalues i)=(2*π)*((n:ℝ)+SharpOccupation.physicalArc ε)/v := by
  let E := H.property.isHermitian.eigenvalues
  obtain ⟨hv,i,j,n,hij,hn⟩ := first_entry_gap H hA hε hs hfar
  obtain ⟨m,hm,hbal,hgap⟩ := gap_packet E hij
  exact ⟨hv,m,n,hm,hbal,hgap.trans hn⟩

/-- After any positive observation date outside the empty-circuit tube,
the first empty visit avoids every prescribed countable set of dates for
all but countably many terminal field increments. The observation date
can depend on the increment. -/
theorem gaussian_boundary_first_empty_dates :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ ε : ℝ, 0<ε → ε<sqrt 2 → ∀ S : Set ℝ, S.Countable →
      ∃ B : Set ℝ, B.Countable ∧ ∀ z ∉ B,
        let H : selfAdjoint (Reg k) := ⟨boundaryHamiltonian ω k z,(boundaryHermitian ω k z).isSelfAdjoint⟩
        ∀ A : ℝ, 0<A → ε<orbitCircuitDistance H 0 A → firstVisit H A 0 ε∉S := by
  filter_upwards [gaussian_boundary_frequency_avoidance] with ω hω
  intro k ε hε hsmall S hS
  let r := SharpOccupation.physicalArc ε
  haveI : Countable S := hS.to_subtype
  let Γ := range (fun p : S×ℤ => (2*π)*((p.2:ℝ)+r)/p.1.val)
  obtain ⟨B,hB,ha⟩ := hω k Γ (countable_range _)
  refine ⟨B,hB,?_⟩
  intro z hz H A hA hfar hS'
  let v := firstVisit H A 0 ε
  obtain ⟨_,m,n,hm,hbal,he⟩ := first_entry_action H hA hε hsmall hfar
  exact ha z hz m hm hbal ⟨(⟨v,hS'⟩,n),he.symm⟩

#print axioms gaussian_boundary_first_empty_dates
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
