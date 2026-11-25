import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.TransitionCount.SpectralEntries
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.FirstVisitSchedule

/-! # Uniform counts of genuine circuit-distance transitions in translated windows -/

open Matrix Finset Set Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.TransitionCount
open PrecisionReturns
noncomputable section

/-- The number of threshold transitions grows at most linearly with
window length. A single constant works across all origins for this
Hamiltonian, budget and tolerance. -/
theorem linear_frontier_count {N : ℕ} (H : selfAdjoint (Square (Bits N))) (s : ℕ)
    {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0≤C ∧ ∀ a b : ℝ, a<b → ∀ Z : Finset ℝ,
      (∀ t∈Z, t∈Icc a b ∩ frontier {u | orbitCircuitDistance H s u=ε}) →
      (Z.card:ℝ)≤C*(1+(b-a)) := by
  classical
  let d := 2^N-1
  let e : Bits N ≃ Fin (d+1) := (Fintype.equivFin _).trans (finCongr (by
    have hn := Nat.two_pow_pos N
    simp only [Bits,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
    dsimp only [d]; omega))
  let ev (t : ℝ) := entryEval (RingHom.id ℝ) (relativeOrbit e H t)
  obtain ⟨F,hF,hcover⟩ := orbit_level_tests (RingHom.id ℝ) e H s ε hε
  choose w hw using fun p : F => polynomial_word e H p.val
  have bound (p : F) := word_zero_bound (w p)
    (fun t => by rw [hw,Complex.ofReal_im]) (by
      obtain ⟨t,ht⟩ := hF p p.property
      exact ⟨t,by rw [hw]; exact_mod_cast ht⟩)
  choose C hC hbound using bound
  refine ⟨∑ p, C p,Finset.sum_nonneg (fun p _ => hC p),?_⟩
  intro a b hab Z hZ
  let zeros (p : F) := Z.filter fun t => ev t p.val=0
  have hu : Z⊆Finset.univ.biUnion zeros := by
    intro t ht
    obtain ⟨p,hp,hzero⟩ := hcover t (hZ t ht).2
    exact Finset.mem_biUnion.mpr ⟨⟨p,hp⟩,Finset.mem_univ _,Finset.mem_filter.mpr ⟨ht,hzero⟩⟩
  have hn := (Finset.card_le_card hu).trans (Finset.card_biUnion_le ..)
  calc
    (Z.card:ℝ) ≤ ∑ p, ((zeros p).card:ℝ) := by exact_mod_cast hn
    _ ≤ ∑ p, C p*(1+(b-a)) := Finset.sum_le_sum fun p _ =>
      hbound p a b hab _ (fun t ht => (hZ t (Finset.mem_filter.mp ht).1).1)
        (fun t ht => by rw [hw]; exact_mod_cast (Finset.mem_filter.mp ht).2)
    _ = _ := (Finset.sum_mul ..).symm

/-- All origins selecting a first visit strictly after the right
endpoint select the very same first visit from that endpoint. -/
theorem firstVisit_eq_of_past_endpoint {N : ℕ} (H : selfAdjoint (Square (Bits N))) (s : ℕ)
    {t b ε : ℝ} (hε : 0<ε) (ht : t≤b) (hv : b≤firstVisit H t s ε) :
    firstVisit H t s ε=firstVisit H b s ε := by
  have A := firstVisit_isLeast H t s hε
  have B := firstVisit_isLeast H b s hε
  exact le_antisymm (A.2 ⟨ht.trans B.1.1,B.1.2⟩) (B.2 ⟨hv,A.1.2⟩)

/-- Across every outside origin in a compact window, the number of
distinct first-return dates has at most one additional terminal date
beyond the transition count within the window. -/
theorem linear_firstVisit_count {N : ℕ} (H : selfAdjoint (Square (Bits N))) (s : ℕ)
    {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0≤C ∧ ∀ a b : ℝ, a<b → ∀ Z : Finset ℝ,
      (∀ v∈Z, ∃ t∈Icc a b, ε<orbitCircuitDistance H s t ∧ firstVisit H t s ε=v) →
      (Z.card:ℝ)≤1+C*(1+(b-a)) := by
  classical
  obtain ⟨C,hC,hB⟩ := linear_frontier_count H s hε
  refine ⟨C,hC,?_⟩
  intro a b hab Z hZ
  let W := Z.filter (· ≤ b)
  have hl := hB a b hab W (by
    intro v hv
    obtain ⟨hvZ,hvb⟩ := Finset.mem_filter.mp hv
    obtain ⟨t,ht,hout,rfl⟩ := hZ v hvZ
    exact ⟨⟨ht.1.trans (firstVisit_isLeast H t s hε).1.1,hvb⟩,firstVisit_mem_level_frontier H s t hε hout⟩)
  have hu : Z⊆insert (firstVisit H b s ε) W := by
    intro v hv
    by_cases hvb : v≤b
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hv,hvb⟩)
    · obtain ⟨t,ht,_,rfl⟩ := hZ v hv
      exact Finset.mem_insert.mpr (Or.inl (firstVisit_eq_of_past_endpoint H s hε ht.2 (le_of_not_ge hvb)))
  have hn := (Finset.card_le_card hu).trans (Finset.card_insert_le ..)
  have hn' : (Z.card:ℝ) ≤ (W.card:ℝ)+1 := by exact_mod_cast hn
  linarith

#print axioms linear_frontier_count
#print axioms linear_firstVisit_count
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.TransitionCount

