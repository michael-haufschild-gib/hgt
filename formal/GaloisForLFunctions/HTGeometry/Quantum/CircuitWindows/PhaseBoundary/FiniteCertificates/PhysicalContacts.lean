import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.OrbitContacts
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FirstCrossing

/-! # Rational equations at the canonical first crossing and subsequent first dips -/

open Set Filter MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
open SharpOccupation PrecisionReturns
noncomputable section

/-- On the actual frozen path, the relative evolution satisfies an
orbit-nonzero rational equation at the first near-Hilbert crossing and
at the subsequent first visit for every budget through that crossing. -/
theorem gaussian_first_contact_equations :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let H : selfAdjoint (Square (Bits N)) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ>0, orbitCircuitDistance H P σ=9/80 ∧ (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        ∀ e : Bits N ≃ Fin ((2^N-1)+1),
          let ev (t : ℝ) := entryEval (Rat.castHom ℝ) (relativeOrbit e H t)
          let contact (t : ℝ) := ∃ p : EntryPolynomial N ℚ, ev t p=0 ∧ ∃ u, ev u p≠0
          contact σ ∧ ∀ s≤P, contact (firstVisit H σ s (1/10)) := by
  obtain ⟨_,h⟩ := gaussian_hilbert_first_crossing
  filter_upwards [h] with ω hw
  filter_upwards [hw] with k hk
  intro N H P
  have hP : P≤2^N/(16*(N+1)) := by
    apply Nat.div_le_div_left <;> dsimp [P,nearHilbertContinuousCircuitBudget,N] <;> omega
  obtain ⟨σ,hσ,hc,hprior,_⟩ := hk P hP
  refine ⟨σ,hσ,hc,hprior,?_⟩
  intro e ev contact
  have witness (s : ℕ) (r : ℚ) (hr : 0<(r:ℝ)) (a v : ℝ) (hav : a<v)
      (hv : orbitCircuitDistance H s v=(r:ℝ)) (hp : ∀ t∈Ioo a v, orbitCircuitDistance H s t≠(r:ℝ)) :
      contact v := by
    obtain ⟨F,hF,hz⟩ := orbit_contact_equations (Rat.castHom ℝ) e H s r hr
    obtain ⟨p,hp,hzero⟩ := hz a v hav hv hp
    exact ⟨p,hzero,hF p hp⟩
  constructor
  · apply witness P (9/80) (by norm_num) 0 σ hσ
    · simpa using hc
    · intro t ht
      simpa using (hprior t ⟨ht.1.le,ht.2⟩).ne
  · intro s hs
    have hout : 1/10<orbitCircuitDistance H s σ := by
      by_contra! hn
      obtain ⟨z,hz,C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ s _).mpr hn
      have hh : orbitCircuitDistance H P σ≤1/10 := (hasProjectiveCircuitApproximation_iff_infDist _ P _).mp
        ⟨z,hz,C,hC.trans hs,he⟩
      rw [hc] at hh
      norm_num at hh
    obtain ⟨hav,hv,hp⟩ := firstVisit_left_contact H s σ (by norm_num : (0:ℝ)<1/10) hout
    apply witness s (1/10) (by norm_num) σ _ hav
    · simpa using hv
    · intro t ht
      simpa using (hp t ht).ne'

#print axioms gaussian_first_contact_equations
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
