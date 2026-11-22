import GaloisForLFunctions.HTGeometry.ImageSeparatingPolynomial
import GaloisForLFunctions.HTGeometry.PolynomialCircuitReplicaHilbertLaw
import GaloisForLFunctions.HTGeometry.TwoLocalContinuousCircuitFixedErrorHardEpochLaw

/-! # A polynomial annihilating all projective physical circuits through a gate budget -/
open MvPolynomial
namespace GaloisForLFunctions.HTGeometry.ExactContacts
noncomputable section
private abbrev State (n : ℕ) := Fin n → Bool
private abbrev Pair (n : ℕ) := State n × State n

/-- Linear probes of a normalized Choi vector, with an independent scalar
variable for the overall amplitude. -/
private def probePoly {n r j : ℕ} (w : Fin r → Pair n → ℂ) (pos : Fin j → Fin n × Fin n)
    (i : Fin r) : MvPolynomial (Fin (j*16+1)) ℂ :=
  X 0 * ∑ p, C (w i p) * rename Fin.succ (TwoQubitCircuit.complexTwoQubitCircuitChoiCoords j pos p)

private theorem eval_probe {n r : ℕ} (w : Fin r → Pair n → ℂ)
    (U : TwoQubitCircuit n) (z : ℂ) :
    ∃ θ : Fin (U.gateCount*16+1) → ℂ, ∀ i,
      aeval θ (probePoly w U.reversePosition i) =
        z * ∑ p : Pair n, w i p * (U.eval.val p.1 p.2) := by
  classical
  let q : ℂ := Real.sqrt (Fintype.card (State n))
  have hq : q ≠ 0 := by
    dsimp only [q]
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos (α:=State n))).ne'
  obtain ⟨u,hu⟩ := TwoQubitCircuit.exists_param_aeval_complexTwoQubitCircuitChoiCoords
    U.reversePosition U.reverseGate U.reverseGate_isTwoQubitGate
  refine ⟨Fin.cons (z*q) u,fun i => ?_⟩
  have hrename (f : MvPolynomial (Fin (U.gateCount*16)) ℂ) :
      aeval (Fin.cons (z*q) u) (rename Fin.succ f)=aeval u f := by
    rw [aeval_rename]
    rfl
  simp only [probePoly,map_mul,map_sum,aeval_X,aeval_C,hrename,Fin.cons_zero,hu,U.reverseGate_prod_eq_eval]
  change z*q*(∑ p : Pair n, w i p*(U.eval.val p.1 p.2/q))=_
  rw [Finset.mul_sum,Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by field_simp [hq]

/-- For any r>16s+1 linear probes of matrix entries one nonzero complex
polynomial vanishes on every projective s-gate endpoint, simultaneously
over all layouts, continuous gates and scalar choices. -/
theorem projective_gate_annihilator {n r : ℕ} (s : ℕ) (hr : s*16+1<r) (w : Fin r → Pair n → ℂ) :
    ∃ F : MvPolynomial (Fin r) ℂ, F ≠ 0 ∧ ∀ U : TwoQubitCircuit n, U.gateCount ≤ s → ∀ z : ℂ,
      aeval (fun i => z * ∑ p : Pair n, w i p * U.eval.val p.1 p.2) F=0 := by
  classical
  let Layout := (j : Fin (s+1)) × (Fin j.val → Fin n × Fin n)
  have h (p : Layout) : ∃ F : MvPolynomial (Fin r) ℂ, F≠0 ∧ aeval (probePoly w p.2) F=0 := by
    apply exists_ne_zero_aeval_eq_zero
    have hj := p.1.isLt
    omega
  choose f hn hz using h
  refine ⟨∏ p : Layout, f p,Finset.prod_ne_zero_iff.mpr (fun p _ => hn p),?_⟩
  intro U hU z
  let p : Layout := ⟨⟨U.gateCount,by omega⟩,U.reversePosition⟩
  obtain ⟨θ,hθ⟩ := eval_probe w U z
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ p)
  have he := aeval_eq_zero_of_aeval_eq_zero (hz p) θ
  exact (congrArg (fun g : Fin r→ℂ => aeval g (f p)) (funext hθ)).symm.trans he

#print axioms projective_gate_annihilator
end
end GaloisForLFunctions.HTGeometry.ExactContacts
