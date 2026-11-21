import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.RealRelations
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.FaceGeometry

/-! # No tied endpoints on a prescribed separation clock -/
open Matrix MeasureTheory Set Real
namespace GaloisForLFunctions.HTGeometry.FirstGate
noncomputable section
open EmptyVisitFlux

/-- Three distinct energies cannot have one integer winding while the
other relative phase is exactly r turns beyond an integer. -/
def AvoidsTie {I : Type*} (E : I → ℝ) (r : ℝ) : Prop :=
  ∀ a b c : I, a ≠ b → c ≠ a → c ≠ b → ∀ m l : ℤ, m≠0 →
    (m:ℝ)*(E c-E a) ≠ ((l:ℝ)+r)*(E b-E a)

/-- Fixed real spectral hyperplanes exclude all integer windings and
all triples, simultaneously for every labeling of the same roots. -/
theorem ae_avoids_tie {m D : ℕ} (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hs : SpectrumEscapesRealRelations (range (spectralEnsembleMatrix P))) (r : ℝ) :
    ∀ᵐ θ ∂(volume : Measure (Fin m → ℝ)), ∀ e : Fin D → ℝ, Function.Injective e →
      (∀ i, matrixCharpolyRelation (spectralEnsembleMatrix P θ,(e i:ℂ))=0) → AvoidsTie e r := by
  classical
  have h (a b c : Fin D) (z l : ℤ) : ∀ᵐ θ ∂(volume : Measure (Fin m → ℝ)),
      c≠a → c≠b → z≠0 → ∀ e : Fin D → ℝ, Function.Injective e →
      (∀ i, matrixCharpolyRelation (spectralEnsembleMatrix P θ,(e i:ℂ))=0) →
      (z:ℝ)*(e c-e a) ≠ ((l:ℝ)+r)*(e b-e a) := by
    by_cases ha : c=a
    · exact Filter.Eventually.of_forall fun _ h => (h ha).elim
    by_cases hb : c=b
    · exact Filter.Eventually.of_forall fun _ _ h => (h hb).elim
    by_cases hz : z=0
    · exact Filter.Eventually.of_forall fun _ _ _ h => (h hz).elim
    let w (i : Fin D) := (if i=c then (z:ℝ) else 0)-
      (if i=b then (l:ℝ)+r else 0)+(if i=a then (l:ℝ)+r-z else 0)
    have hw : ∑ i, w i=0 := by simp [w,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    have hne : w≠0 := by
      intro he
      have he' := congrFun he c
      simp only [w,if_pos rfl,if_neg ha,if_neg hb,sub_zero,add_zero,Pi.zero_apply,Int.cast_eq_zero] at he'
      exact hz he'
    filter_upwards [ae_no_fixed_real_relation P hs w hw hne] with θ hθ _ _ _ e hi hr he
    apply hθ e hi hr
    have hsum : ∑ i, w i*e i = (z:ℝ)*(e c-e a)-((l:ℝ)+r)*(e b-e a) := by
      simp only [w,add_mul,sub_mul,ite_mul,zero_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib,
        Finset.sum_ite_eq',Finset.mem_univ,if_true]
      ring
    rw [hsum,he,sub_self]
  have all := ae_all_iff.mpr fun a => ae_all_iff.mpr fun b => ae_all_iff.mpr fun c =>
    ae_all_iff.mpr fun z => ae_all_iff.mpr fun l => h a b c z l
  filter_upwards [all] with θ hθ e hi hr a b c _ hca hcb z l hz
  exact hθ a b c z l hca hcb hz e hi hr

/-- Lifting one relative phase determines its integer winding. -/
theorem lift_gap {I : Type*} (E : I → ℝ) (t : ℝ) (i j : I) {r : ℝ}
    (h : flow (fun k => E k/(2*π)) t j-flow (fun k => E k/(2*π)) t i=(r:UnitAddCircle)) :
    ∃ z : ℤ, t*(E j-E i)/(2*π) = (z:ℝ)+r := by
  have hh : (((t*(E j-E i)/(2*π)-r:ℝ):UnitAddCircle))=0 := by
    rw [AddCircle.coe_sub,sub_eq_zero]
    convert h using 1
    simp only [flow,←AddCircle.coe_sub]
    congr 1
    ring
  obtain ⟨z,hz⟩ := (AddCircle.coe_eq_zero_iff 1).mp hh
  rw [zsmul_eq_mul,mul_one] at hz
  exact ⟨z,by linarith only [hz]⟩

/-- The exclusion of balanced real relations applies on the entire
positive time axis, including the first entry selected from that axis. -/
theorem simple_contact {I : Type*} (E : I → ℝ) (hi : Function.Injective E)
    {r t : ℝ} (hn : AvoidsTie E r) (ht : 0 < t) (a b c : I) (hab : a≠b) (hca : c≠a) (hcb : c≠b)
    (h : flow (fun k => E k/(2*π)) t c-flow (fun k => E k/(2*π)) t a=(r:UnitAddCircle)) :
    flow (fun k => E k/(2*π)) t b ≠ flow (fun k => E k/(2*π)) t a := by
  intro hba
  obtain ⟨m,hm⟩ := lift_gap E t a b (r := 0) (by rw [hba,sub_self,AddCircle.coe_zero])
  obtain ⟨l,hl⟩ := lift_gap E t a c h
  rw [add_zero] at hm
  have hπ : 2*π≠0 := by positivity
  have hm' := (div_eq_iff hπ).mp hm
  have hz : m≠0 := by
    intro he
    rw [he,Int.cast_zero,zero_mul] at hm'
    exact (sub_ne_zero.mpr (hi.ne hab.symm)) ((mul_eq_zero.mp hm').resolve_left ht.ne')
  apply hn a b c hab hca hcb m l hz
  rw [←hm,←hl]
  ring

#print axioms ae_avoids_tie
#print axioms simple_contact
end
end GaloisForLFunctions.HTGeometry.FirstGate
