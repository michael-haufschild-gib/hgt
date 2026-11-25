import GaloisForLFunctions.HTGeometry.HypertranscendentalKaehlerClockSymbol

/-! # Independence of horizontal forms over the differential field -/

namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.DifferentialPhases
noncomputable section
variable {C L V : Type*} [Field C] [Field L] [Algebra C L]
  [AddCommGroup V] [Module C V] [Module L V] [IsScalarTower C L V]

/-- In a relation among horizontal vectors normalize one coefficient
to one and differentiate. The shorter relation forces every normalized
coefficient into the constant field. -/
theorem horizontal_independent (δ : Derivation C L L) (hC : ∀ a, δ a=0 → ∃ b : C, algebraMap C L b=a)
    (T : V →+ V) (hT : ∀ a w, T (a • w)=δ a • w+a • T w)
    {n : ℕ} (v : Fin n → V) (hv : ∀ i, T (v i)=0) (hi : LinearIndependent C v) :
    LinearIndependent L v := by
  classical
  induction n with
  | zero => exact linearIndependent_empty_type
  | succ n ih =>
    have htail := ih (v ∘ Fin.succ) (fun i => hv i.succ) (hi.comp _ (Fin.succ_injective n))
    have drop (c : Fin (n+1) → L) (hc : ∑ i, c i • v i=0) (h0 : c 0=0) : ∀ i, c i=0 := by
      rw [Fin.sum_univ_succ,h0,zero_smul,zero_add] at hc
      exact Fin.cases h0 ((Fintype.linearIndependent_iff.mp htail) (fun i => c i.succ) hc)
    apply Fintype.linearIndependent_iff.mpr
    intro c hc
    by_cases h0 : c 0=0
    · exact drop c hc h0
    · let u (i : Fin (n+1)) := (c 0)⁻¹*c i
      have hu : ∑ i, u i • v i=0 := by
        simpa only [u,mul_smul,←Finset.smul_sum,hc,smul_zero]
      have hu0 : u 0=1 := inv_mul_cancel₀ h0
      have hd : ∑ i, δ (u i) • v i=0 := by
        have he := congrArg T hu
        simpa only [map_sum,hT,hv,smul_zero,add_zero,map_zero] using he
      have hz := drop (fun i => δ (u i)) hd (by rw [hu0,Derivation.map_one_eq_zero])
      choose b hb using fun i => hC (u i) (hz i)
      have hrel : ∑ i, b i • v i=0 := by
        simpa only [←hb,algebraMap_smul] using hu
      have hh := (Fintype.linearIndependent_iff.mp hi) b hrel 0
      have hbad := hb 0
      rw [hh,map_zero,hu0] at hbad
      exact (zero_ne_one hbad).elim

#print axioms horizontal_independent
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.DifferentialPhases
