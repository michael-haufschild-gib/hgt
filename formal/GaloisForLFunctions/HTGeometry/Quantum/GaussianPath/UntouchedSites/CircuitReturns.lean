import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.GaussianCommutant
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.PhaseDistance
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitDeletionBound

/-! # An untouched qubit forces an all-time return near a scalar -/
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.UntouchedSites
noncomputable section

/-- On each Gaussian prefix one constant controls all times, targets and
unvisited sites: proximity to a circuit that skips even one qubit implies
proximity to the empty circuit. -/
theorem gaussian_untouched_circuit_return :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n,
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∃ A : ℝ, 0 < A ∧ ∀ (t : ℝ) (C : TwoQubitCircuit (n+2)), C.touchedSites ≠ Finset.univ →
        ∀ z : ℂ, HasProjectiveCircuitApproximation (n+2) (A*‖unitaryEvolution H t-z • (C.eval : SpinMatrix (Fin (n+2)))‖)
          0 (unitaryEvolution H t) := by
  classical
  filter_upwards [gaussian_one_site_scalar] with ω hω n
  intro H
  let M : selfAdjoint (SpinMatrix (Fin (n+2))) := ⟨H,isSelfAdjoint_pathHamiltonian _⟩
  let r : Fin (n+2) → Bool := fun _ => false
  have h (v : Fin (n+2)) := phase_distance_control r M (spin v) (hω n v)
  choose K hK hbound using h
  let A := 1+∑ v, K v
  have hsum : 0 ≤ ∑ v, K v := Finset.sum_nonneg fun v _ => (hK v).le
  refine ⟨A,by dsimp only [A]; linarith only [hsum],?_⟩
  intro t C hmiss z
  obtain ⟨v,hv⟩ : ∃ v, v ∉ C.touchedSites := by
    by_contra! ha
    exact hmiss (Finset.eq_univ_iff_forall.mpr ha)
  have hP (a : Fin 3) : IsSiteSupported {v} (spin v a) :=
    finitePauliMatrix_isSiteSupported_of_eq_none _ _ fun w hw => by
      simpa only [Finset.mem_singleton] using (show siteLabel v a w=none from
        if_neg (by simpa only [Finset.mem_singleton] using hw))
  have hd : Disjoint ({v} : Finset _) C.touchedSites := Finset.disjoint_singleton_left.mpr hv
  obtain ⟨c,hc,he⟩ := hbound v t (z • (C.eval : SpinMatrix (Fin (n+2)))) (fun a =>
    (commute_of_isSiteSupported_disjoint hd (hP a) (C.isSiteSupported_touchedSites.complex_smul z)).eq)
  have hk : K v ≤ A := by
    have hv' := Finset.single_le_sum (s := Finset.univ) (fun i _ => (hK i).le) (Finset.mem_univ v)
    dsimp only [A]
    linarith only [hv']
  exact ⟨c,hc,TwoQubitCircuit.one _,le_rfl,he.trans (mul_le_mul_of_nonneg_right hk (norm_nonneg _))⟩

/-- At fewer than half as many gates as qubits, the empty-circuit return
radius and the affordable return radius differ by at most a fixed factor
on the entire orbit of each fixed Gaussian prefix. -/
theorem gaussian_few_gate_scalar_return :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n,
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∃ A : ℝ, 0 < A ∧ ∀ (t ε : ℝ) (s : ℕ), 2*s<n+2 →
        HasProjectiveCircuitApproximation (n+2) ε s (unitaryEvolution H t) →
        HasProjectiveCircuitApproximation (n+2) (A*ε) 0 (unitaryEvolution H t) := by
  filter_upwards [gaussian_untouched_circuit_return] with ω hw n
  intro H
  obtain ⟨A,hA,h⟩ := hw n
  refine ⟨A,hA,?_⟩
  rintro t ε s hs ⟨z,_,C,hcount,herr⟩
  have hsmall := C.card_touchedSites_le.trans_lt (show 2*C.gateCount<n+2 by omega)
  have hmiss : C.touchedSites ≠ Finset.univ := fun hh => by
    rw [hh,Finset.card_univ,Fintype.card_fin] at hsmall
    exact hsmall.false
  obtain ⟨c,hc,E,hlen,he⟩ := h t C hmiss z
  exact ⟨c,hc,E,hlen,he.trans (mul_le_mul_of_nonneg_left herr hA.le)⟩

#print axioms gaussian_untouched_circuit_return
#print axioms gaussian_few_gate_scalar_return
end
end GaloisForLFunctions.HTGeometry.UntouchedSites
