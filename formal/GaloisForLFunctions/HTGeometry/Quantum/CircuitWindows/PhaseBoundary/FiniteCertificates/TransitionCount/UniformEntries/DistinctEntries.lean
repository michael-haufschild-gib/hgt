import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.TransitionCount.UniformEntries.SpectralWords

/-! # Counting genuine first circuit entries uniformly over static Hamiltonians -/

open Set Filter Topology Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.TransitionCount.UniformEntries
open PrecisionReturns
noncomputable section

/-- At fixed register size and budget, the number of distinct first-entry
dates in any interval is bounded by a constant times one plus bandwidth
times duration. All positive errors and all possible outside origins share
the constant. The spectrum may have degeneracies or resonances. -/
theorem uniform_first_entry_count (N s : ℕ) : ∃ C ≥ (0:ℝ),
    ∀ (H : selfAdjoint (Square (Bits N))) (ε : ℝ), 0<ε → ∀ a b : ℝ, a<b →
    ∀ Z : Finset ℝ, (∀ v∈Z, v∈Icc a b ∧ ∃ t, ε<orbitCircuitDistance H s t ∧
      firstVisit H t s ε=v) → (Z.card:ℝ)≤C*(1+(b-a)*circuitHamiltonianSpectralWidth H) := by
  classical
  let d := 2^N-1
  let e : Bits N ≃ Fin (d+1) := (Fintype.equivFin _).trans (finCongr (by
    have hn := Nat.two_pow_pos N
    simp only [Bits,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
    dsimp only [d]; omega))
  obtain ⟨F,hF⟩ := common_first_entry_tests N s
  choose C hC hbnd using fun p : F => physical_test_zero_bound e p.val
  refine ⟨∑ p, C p,Finset.sum_nonneg (fun p _ => hC p),?_⟩
  intro H ε hε a b hab Z hZ
  let ev (t : ℝ) := testEval (relativeOrbit e H t,ε)
  let zeros (p : F) := Z.filter fun t => ev t p.val=0 ∧ ∃ u, ev u p.val≠0
  have hcov : Z⊆Finset.univ.biUnion zeros := by
    intro v hv
    obtain ⟨t,ht,he⟩ := (hZ v hv).2
    obtain ⟨p,hp,hzero,hne⟩ := hF e H ε hε t ht
    rw [he] at hzero
    exact Finset.mem_biUnion.mpr ⟨⟨p,hp⟩,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hv,hzero,hne.exists⟩⟩
  have hc := (Finset.card_le_card hcov).trans (Finset.card_biUnion_le ..)
  have hbound (p : F) : ((zeros p).card:ℝ)≤C p*(1+(b-a)*circuitHamiltonianSpectralWidth H) := by
    rcases (zeros p).eq_empty_or_nonempty with he | ⟨v,hv⟩
    · rw [he,Finset.card_empty,Nat.cast_zero]
      exact mul_nonneg (hC p) (by linarith only [mul_nonneg (sub_nonneg.mpr hab.le) (circuitHamiltonianSpectralWidth_nonneg H)])
    · exact hbnd p (H,ε) (Finset.mem_filter.mp hv).2.2 a b hab _
        (fun t ht => (hZ t (Finset.mem_filter.mp ht).1).1) (fun t ht => (Finset.mem_filter.mp ht).2.1)
  calc
    (Z.card:ℝ) ≤ ∑ p, ((zeros p).card:ℝ) := by exact_mod_cast hc
    _ ≤ _ := Finset.sum_le_sum (fun p _ => hbound p)
    _ = _ := (Finset.sum_mul ..).symm

#print axioms uniform_first_entry_count
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.TransitionCount.UniformEntries
