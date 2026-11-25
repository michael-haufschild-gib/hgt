import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.FinitePrefixes.BoxDifferences
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.ResonantReturns.PairDeadline
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation
import Mathlib.Data.Nat.Nth

/-! # Deadlines for every affordable tick after one circuit visit -/

open Finset Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.FinitePrefixes
noncomputable section

/-- A single affordable index p gives a linear upper bound on all
subsequent visit indices after increasing the operator tolerance by
2π/Q. The period, Hamiltonian and original circuit are arbitrary. -/
theorem visit_index_deadline {N d : ℕ} (e : (Fin N → Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Matrix (Fin N → Bool) (Fin N → Bool) ℂ)) (a τ : ℝ) (p s : ℕ)
    {ε : ℝ} (hfit : HasProjectiveCircuitApproximation N ε s (unitaryEvolution H.val (a+(p:ℝ)*τ)))
    {Q : ℕ} (hQ : 0<Q) {η : ℝ} (hη : ε+2*π/Q≤η) :
    let hit (n : ℕ) := HasProjectiveCircuitApproximation N η s (unitaryEvolution H.val (a+(n:ℝ)*τ))
    (setOf hit).Infinite ∧ ∀ i, Nat.nth hit i≤p+Q^d*i := by
  classical
  intro hit
  let E := H.2.isHermitian.eigenvalues
  let u := e.symm 0
  let β (k : Fin d) := τ*(E (e.symm k.succ)-E u)/(2*π)
  have hc (i : ℕ) : i<Nat.count hit (p+Q^d*i+1) := by
    obtain ⟨S,hS,hall⟩ := many_dirichlet_returns β hQ i
    rw [Nat.count_eq_card_filter_range]
    let F := S.image (fun n => p+n)
    have hcard : F.card=S.card := card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)
    apply hS.trans_le
    rw [←hcard]
    apply Finset.card_le_card
    intro n hn
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hn
    obtain ⟨hle,hclose⟩ := hall j hj
    refine mem_filter.mpr ⟨mem_range.mpr (by omega),?_⟩
    have hrel (v : Fin N → Bool) : latticeClose (((j:ℝ)*τ)*(E v-E u)/(2*π)) (1/Q) := by
      obtain ⟨l,rfl⟩ := e.symm.surjective v
      refine Fin.cases ?_ (fun k => ?_) l
      · refine ⟨0,?_⟩
        simp only [u,sub_self,mul_zero,zero_div,Int.cast_zero,abs_zero]
        positivity
      · rw [show ((j:ℝ)*τ)*(E (e.symm k.succ)-E u)/(2*π)=(j:ℝ)*β k by dsimp [β]; ring]
        exact hclose k
    have hempty := ResonantReturns.empty_of_anchored_gaps H u ((j:ℝ)*τ)
      (show (0:ℝ)≤1/Q by positivity) hrel
    have hf : HasProjectiveCircuitApproximation N (ε+2*π/Q) s (unitaryEvolution H.val (a+((p+j:ℕ):ℝ)*τ)) := by
      simpa only [Nat.add_zero,Nat.cast_add,add_mul,←add_assoc,mul_one_div] using affordable_add_time H hfit hempty
    obtain ⟨z,hz,C,hC,he⟩ := hf
    exact ⟨z,hz,C,hC,he.trans hη⟩
  constructor
  · intro hf
    exact (hc hf.toFinset.card).not_ge (Nat.count_le_card hf _)
  · intro i
    exact Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count (hc i))

#print axioms visit_index_deadline
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.FinitePrefixes
