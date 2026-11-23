import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.Exchange
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliLineObstruction
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliNoncontextualCircuit

/-! # Six directed Pauli signals on three consecutive physical sites -/
open Matrix Real Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
noncomputable section
variable {n : ℕ}
private abbrev Reg := Matrix (Fin (n+2) → Bool) (Fin (n+2) → Bool) ℂ

def tripleSites (e f : Fin (n+1)) : Finset (Fin (n+2)) := {e.castSucc,e.succ,f.succ}

def tripleGenerator (e f : Fin (n+1)) : Reg (n:=n) :=
  mix (finitePauliMatrix (couplingWord e (2,0))) (finitePauliMatrix (couplingWord f (2,2)))

/-- X on either outside spin and Z on the middle spin each anticommute
with one bond and commute with the other. -/
def tripleAxis (e : Fin (n+1)) (i : Fin (n+2)) : Fin 3 := if i=e.succ then 2 else 0

private theorem probe_odd {e f : Fin (n+1)} (hm : e.succ=f.castSucc) {i : Fin (n+2)}
    (hi : i ∈ tripleSites e f) :
    oddProbe (finitePauliMatrix (couplingWord e (2,0))) (finitePauliMatrix (couplingWord f (2,2)))
      (finitePauliMatrix (onsiteWord i (tripleAxis e i))) := by
  have hl : e.castSucc<e.succ := Nat.lt_succ_self e.val
  have hr : e.succ<f.succ := hm ▸ (show f.castSucc<f.succ from Nat.lt_succ_self f.val)
  have hne := hl.trans hr
  simp only [tripleSites,mem_insert,mem_singleton] at hi
  rcases hi with rfl|rfl|rfl
  · left
    constructor
    · apply finitePauliMatrix_anticommute_of_not_commute
      intro h
      have hh := ((commute_onsite_coupling_iff ..).mp h.symm).1 rfl
      simp [tripleAxis,hl.ne] at hh
    · apply Commute.symm
      exact (commute_onsite_coupling_iff ..).mpr
        ⟨fun h => (hl.ne (h.trans hm.symm)).elim,fun h => (hne.ne h).elim⟩
  · left
    constructor
    · apply finitePauliMatrix_anticommute_of_not_commute
      intro h
      have hh := ((commute_onsite_coupling_iff ..).mp h.symm).2 rfl
      simp [tripleAxis] at hh
    · apply Commute.symm
      exact (commute_onsite_coupling_iff ..).mpr
        ⟨fun _ => by simp [tripleAxis],fun h => (hr.ne h).elim⟩
  · right
    constructor
    · apply Commute.symm
      exact (commute_onsite_coupling_iff ..).mpr
        ⟨fun h => (hne.ne' h).elim,fun h => (hr.ne' h).elim⟩
    · apply finitePauliMatrix_anticommute_of_not_commute
      intro h
      have hh := ((commute_onsite_coupling_iff ..).mp h.symm).2 rfl
      simp [tripleAxis,hr.ne'] at hh

/-- The calibrated propagator gives a maximal signal for every
ordered pair of distinct sites, uniformly over the size of the register. -/
theorem triple_pair_signal {e f : Fin (n+1)} (hm : e.succ=f.castSucc) {i j : Fin (n+2)}
    (hi : i∈tripleSites e f) (hj : j∈tripleSites e f) (hij : i≠j) :
    let U := unitaryEvolution (tripleGenerator e f) (π/2)
    let P := finitePauliMatrix (onsiteWord i (tripleAxis e i))
    let Q := finitePauliMatrix (onsiteWord j (tripleAxis e j))
    ‖(star U*P*U)*Q-Q*(star U*P*U)‖=2 := by
  have hab : ¬Commute (finitePauliMatrix (couplingWord e (2,0)))
      (finitePauliMatrix (couplingWord f (2,2))) :=
    fun h => (by decide : (0:Fin 3)≠2) ((commute_consecutive_coupling_iff e f hm _ _).mp h)
  exact quarter_exchange_norm _ _ _ _ (finitePauliMatrix_isHermitian _).isSelfAdjoint
    (finitePauliMatrix_isHermitian _).isSelfAdjoint (finitePauliMatrix_mul_self _)
    (finitePauliMatrix_mul_self _) (finitePauliMatrix_anticommute_of_not_commute _ _ hab)
    (probe_odd hm hi) (probe_odd hm hj) ((commute_onsitePauli_iff ..).mpr (Or.inl hij))
    (finitePauliMatrix_mem_unitary _) (finitePauliMatrix_mem_unitary _)

#print axioms triple_pair_signal
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
