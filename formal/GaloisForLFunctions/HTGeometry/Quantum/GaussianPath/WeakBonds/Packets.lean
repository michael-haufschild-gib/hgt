import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Subregister.Evolution
import GaloisForLFunctions.HTGeometry.PathShellDelayFloor
import GaloisForLFunctions.HTGeometry.NearestNeighborPathSpectrumRealRelationEscape

/-! # Exact cost of the path interactions retained in a packet of sites -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds
open Subregister DiagonalSynthesis
noncomputable section

/-- The three magnetic field terms at one site. -/
def onsiteAt {n : ℕ} (u : PathShell n) (i : Fin (n+2)) : Register (n+2) :=
  ∑ q : Fin 3, ((u (Sum.inl (i,q)) : ℝ) : ℂ) • finitePauliMatrix (onsiteWord i q)

/-- Retain every field in S and precisely the interactions with both ends in S. -/
def packet {n : ℕ} (u : PathShell n) (S : Finset (Fin (n+2))) : Register (n+2) :=
  (∑ i : Fin (n+2), if i ∈ S then onsiteAt u i else 0) +
    ∑ e : Fin (n+1), if e.castSucc ∈ S ∧ e.succ ∈ S then edgePart u e else 0

private theorem supported_sum {n : ℕ} (S : Finset (Fin n)) {ι : Type*}
    (s : Finset ι) (F : ι → Register n)
    (h : ∀ i ∈ s, IsSiteSupported (A := fun _ : Fin n => Bool) S (F i)) :
    IsSiteSupported (A := fun _ : Fin n => Bool) S (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using IsSiteSupported.zero (A := fun _ : Fin n => Bool) S
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self ..)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private theorem supported_pauli {n : ℕ} {S : Finset (Fin n)} (P : Fin n → Option (Fin 3))
    (hP : ∀ v, v ∉ S → P v = none) (r : ℝ) :
    IsSiteSupported (A := fun _ : Fin n => Bool) S ((r:ℂ) • finitePauliMatrix P) := by
  have he : (r:ℂ) • finitePauliMatrix P = r • finitePauliMatrix P := by
    ext x y
    simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
  rw [he]
  exact (finitePauliMatrix_isSiteSupported_of_eq_none S P hP).smul r

theorem packet_supported {n : ℕ} (u : PathShell n) (S : Finset (Fin (n+2))) :
    IsSiteSupported (A := fun _ : Fin (n+2) => Bool) S (packet u S) := by
  apply IsSiteSupported.add
  · apply supported_sum
    intro i _
    split
    next hi =>
      apply supported_sum
      intro q _
      apply supported_pauli
      intro v hv
      simp [onsiteWord,show v ≠ i from fun h => hv (h ▸ hi)]
    next => exact IsSiteSupported.zero S
  · apply supported_sum
    intro e _
    by_cases he : e.castSucc ∈ S ∧ e.succ ∈ S
    · rw [if_pos he]
      apply supported_sum
      intro ab _
      apply supported_pauli
      intro v hv
      have h₁ : v ≠ e.castSucc := fun h => hv (h ▸ he.1)
      have h₂ : v ≠ e.succ := fun h => hv (h ▸ he.2)
      simp [couplingWord,h₁,h₂]
    · rw [if_neg he]
      exact IsSiteSupported.zero S

theorem packet_selfAdjoint {n : ℕ} (u : PathShell n) (S : Finset (Fin (n+2))) :
    IsSelfAdjoint (packet u S) := by
  apply IsSelfAdjoint.add
  · rw [IsSelfAdjoint,star_sum]
    apply Finset.sum_congr rfl
    intro i _
    split
    · exact isSelfAdjoint_pauliCombination (onsiteWord i) (fun q => u (Sum.inl (i,q)))
    · exact star_zero _
  · rw [IsSelfAdjoint,star_sum]
    apply Finset.sum_congr rfl
    intro e _
    split
    · exact isSelfAdjoint_edgePart u e
    · exact star_zero _

/-- An all-time exact cap for the full operator on a possibly disconnected packet. -/
theorem packet_exact_evolution {n : ℕ} (u : PathShell n) (S : Finset (Fin (n+2)))
    (hS : 2 ≤ S.card) (t : ℝ) :
    Realizes (packetCost S.card) (unitaryEvolution (packet u S) t) :=
  exact_supported_evolution S hS ⟨_,packet_selfAdjoint u S⟩ (packet_supported u S) t

#print axioms packet_exact_evolution
end
end GaloisForLFunctions.HTGeometry.WeakBonds
