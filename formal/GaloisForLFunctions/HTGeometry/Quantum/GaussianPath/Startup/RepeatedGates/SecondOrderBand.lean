import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.ReturnDuration
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.SymmetricBonds.Step

/-! # The next gate-count band at a deep scalar return -/
open MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates
noncomputable section

/-- Between cubic and quadratic accuracy one gate per bond fails.
Repeating only the smaller of the two alternating bond layers suffices.
Both bounds transfer to either side of any half-tolerance scalar visit. -/
theorem gaussian_second_order_band :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n : ℕ,
      let N := n+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (n+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∃ A a : ℝ, 0 < A ∧ 0 < a ∧ ∀ᶠ t : ℝ in 𝓝[≠] 0,
        ∀ ε ∈ Icc (A*|t|^3) (a*t^2), ∀ v : ℝ,
          HasProjectiveCircuitApproximation N (ε/2) 0 (unitaryEvolution H.val v) →
          let U := unitaryEvolution H.val (v+t)
          ¬HasProjectiveCircuitApproximation N ε (n+2) U ∧
            HasProjectiveCircuitApproximation N ε ((n+2)+(n+2)/2) U := by
  filter_upwards [gaussian_quadratic_bond_floor] with ω hω n
  intro N H
  obtain ⟨a,_,ha,_,_,hl⟩ := hω n
  obtain ⟨K,hK,hu⟩ := BondProducts.Symmetric.cubic_bond_step (pathPauliDisorderShell ω (n+1))
  refine ⟨2*K,a/2,mul_pos two_pos hK,half_pos ha,?_⟩
  filter_upwards [hl.filter_mono nhdsWithin_le_nhds,hu.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t hlow hupper ht
  intro ε hε v hv U
  constructor
  · intro h
    have hh := affordable_add_time H h (hv.neg_time H)
    simp only [Nat.add_zero,show v+t+-v=t by ring] at hh
    obtain ⟨z,hz,C,hC,he⟩ := hh
    have hf := (hlow C hC z hz).trans he
    have hp := mul_pos ha (sq_pos_of_ne_zero (show t ≠ 0 from ht))
    linarith only [hf,hε.2,hp]
  · obtain ⟨z,hz,C,hC,he⟩ := affordable_add_time H hv hupper
    exact ⟨z,hz,C,by simpa only [Nat.zero_add] using hC,he.trans (by linarith only [hε.1])⟩

/-- On three qubits the second precision band has minimum exactly three. -/
theorem gaussian_three_qubit_second_band :
    ∀ᵐ ω ∂pathPauliDisorderLaw,
      let H := pathHamiltonian (pathPauliDisorderShell ω 1)
      ∃ A a : ℝ, 0 < A ∧ 0 < a ∧ ∀ᶠ t : ℝ in 𝓝[≠] 0,
        ∀ ε ∈ Icc (A*|t|^3) (a*t^2), ∀ v : ℝ,
          HasProjectiveCircuitApproximation 3 (ε/2) 0 (unitaryEvolution H v) →
          ∀ s : ℕ, HasProjectiveCircuitApproximation 3 ε s (unitaryEvolution H (v+t)) ↔ 3 ≤ s := by
  filter_upwards [gaussian_second_order_band] with ω hω
  obtain ⟨A,a,hA,ha,h⟩ := hω 0
  refine ⟨A,a,hA,ha,?_⟩
  filter_upwards [h] with t ht
  intro ε hε v hv s
  obtain ⟨hn,hp⟩ := ht ε hε v hv
  constructor
  · rintro ⟨z,hz,C,hC,he⟩
    by_contra! hs
    exact hn ⟨z,hz,C,by omega,he⟩
  · intro hs
    obtain ⟨z,hz,C,hC,he⟩ := hp
    exact ⟨z,hz,C,hC.trans hs,he⟩

#print axioms gaussian_second_order_band
#print axioms gaussian_three_qubit_second_band
end
end GaloisForLFunctions.HTGeometry.RepeatedGates
