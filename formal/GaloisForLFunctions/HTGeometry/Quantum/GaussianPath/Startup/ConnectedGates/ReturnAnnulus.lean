import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.ConnectedGates.Threshold
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # Exact gate count on both sides of every deep scalar return -/
open Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ConnectedGates
noncomputable section

/-- At every sufficiently short nonzero signed lag, all tolerances in
the interval [At²,c|t|] give exactly N−1 gates around every scalar
visit at half that tolerance. The same constants work at all visits. -/
theorem gaussian_exact_count_around_returns :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n,
      let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
      ∃ A c : ℝ, 0<A ∧ 0<c ∧ ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ ε : ℝ, A*t^2 ≤ ε → ε ≤ c * |t| →
        ∀ v : ℝ, HasProjectiveCircuitApproximation (n+2) (ε/2) 0 (unitaryEvolution H.val v) →
          ∀ s : ℕ, HasProjectiveCircuitApproximation (n+2) ε s (unitaryEvolution H.val (v+t)) ↔ n+1 ≤ s := by
  filter_upwards [gaussian_minimum_bond_count] with ω hω n
  intro H
  obtain ⟨A,c,hA,hc,hupper,hlower⟩ := hω n
  refine ⟨2*A,c/2,mul_pos two_pos hA,half_pos hc,?_⟩
  filter_upwards [hlower] with t ht
  intro ε hlow hhigh v hv s
  constructor
  · intro hh
    by_contra! hs
    have hback := affordable_add_time H hh (hv.neg_time H)
    simp only [Nat.add_zero,show v+t+-v=t by ring] at hback
    obtain ⟨z,hz,C,hC,he⟩ := hback
    obtain ⟨x,hx⟩ := ht C (hC.trans_lt hs) z hz
    have hx' := (norm_entry_le_l2_opNorm _ x (fun _ => false)).trans he
    have hnn : 0≤c*|t| := mul_nonneg hc.le (abs_nonneg _)
    linarith only [hx,hx',hhigh,hnn]
  · intro hs
    obtain ⟨z,hz,C,hC,he⟩ := affordable_add_time H hv (hupper t)
    refine ⟨z,hz,C,(by omega),he.trans ?_⟩
    linarith only [hlow]

/-- The exact gate-count annulus in particular surrounds the attained
first empty entry from each positive origin, also one chosen after the draw. -/
theorem gaussian_exact_count_around_first_entry :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n,
      let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
      ∃ A c : ℝ, 0<A ∧ 0<c ∧ ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ ε > 0, A*t^2 ≤ ε → ε ≤ c * |t| →
        ∀ a : ℝ, let v := PrecisionReturns.firstVisit H a 0 (ε/2)
        ∀ s : ℕ, HasProjectiveCircuitApproximation (n+2) ε s (unitaryEvolution H.val (v+t)) ↔ n+1 ≤ s := by
  filter_upwards [gaussian_exact_count_around_returns] with ω hω n
  intro H
  obtain ⟨A,c,hA,hc,h⟩ := hω n
  refine ⟨A,c,hA,hc,?_⟩
  filter_upwards [h] with t ht
  intro ε hε hlow hhigh a v
  exact ht ε hlow hhigh v (PrecisionReturns.firstVisit_isLeast H a 0 (half_pos hε)).1.2

#print axioms gaussian_exact_count_around_first_entry
end
end GaloisForLFunctions.HTGeometry.ConnectedGates
