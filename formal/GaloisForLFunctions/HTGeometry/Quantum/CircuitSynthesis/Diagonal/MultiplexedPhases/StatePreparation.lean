import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.MultiplexedPhases.Synthesis
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.StatePreparation

/-! # Geometric gate costs for clearing a register state -/
open Matrix Finset
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis.MultiplexedPhases
open private normalizer normalizer_norm normalizer_mul firstPhase middle middle_pair
  diagonal_preserves mix_preserves from GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.StatePreparation
noncomputable section
variable {n : ℕ}

/-- On the face where all cleared bits are zero, a diagonal circuit
needs only the remaining bits as controls. -/
private theorem phase_on_face (hn : 2 ≤ n) (S : Finset (Fin n)) (v p : Config n→ℂ)
    (hv : ∀ j∉S, Cleared v j) (hp : ∀ x, ‖p x‖=1) :
    ∃ A : Register n, Realizes (2^S.card*3) A ∧ A *ᵥ v=diagonal p *ᵥ v := by
  let mask (x : Config n) (j : Fin n) := if j∈S then x j else false
  have hs : DependsOn (fun x => p (mask x)) (S:Set (Fin n)) := by
    intro x y h
    apply congrArg p
    funext j
    by_cases hj : j∈S
    · simp only [mask,if_pos hj,h j hj]
    · simp only [mask,if_neg hj]
  refine ⟨_,supported_phases hn S _ (fun x => hp (mask x)) hs,?_⟩
  funext x
  rw [mulVec_diagonal,mulVec_diagonal]
  by_cases hx : mask x=x
  · rw [hx]
  · obtain ⟨j,hj⟩ := Function.ne_iff.mp hx
    have hjs : j∉S := fun hi => hj (if_pos hi)
    have hbit : x j=true := by
      cases he : x j
      · exact False.elim (hj (by simp [mask,hjs,he]))
      · rfl
    rw [hv j hjs x hbit,mul_zero,mul_zero]

private theorem clear_active (hn : 2 ≤ n) (S : Finset (Fin n)) (v : Config n→ℂ)
    (hc : ∀ j∉S, Cleared v j) (i : Fin n) (hi : i∈S) :
    ∃ W : Register n, Realizes (2*(2^S.card*3+1)) W ∧ Cleared (W *ᵥ v) i ∧
      ∀ j∉S, Cleared (W *ᵥ v) j := by
  let p := firstPhase i v
  let w := middle i v
  let q := fun x => normalizer (w x)
  have hp (x : Config n) : ‖p x‖=1 := by
    dsimp only [p,firstPhase]; split <;> simp [normalizer_norm]
  have hw (j : Fin n) (hj : j∉S) : Cleared w j :=
    mix_preserves _ (fun e => hj (e.symm ▸ hi)) (diagonal_preserves v p j (hc j hj))
  obtain ⟨A,hA,ha⟩ := phase_on_face hn S v p hc hp
  obtain ⟨B,hB,hb⟩ := phase_on_face hn S w q hw (fun _ => normalizer_norm _)
  let H := bitMix i
  have hH := bitMix_circuit hn i
  let W := H*(B*(H*A))
  have hW : Realizes (2*(2^S.card*3+1)) W := by
    convert hH.mul (hB.mul (hH.mul hA)) using 1
    omega
  have hmid : H *ᵥ (A *ᵥ v)=w := by rw [ha]; rfl
  have he : W *ᵥ v=H *ᵥ (diagonal q *ᵥ w) := by
    simp only [W,←mulVec_mulVec,hmid,hb]
  refine ⟨W,hW,?_,?_⟩
  · intro x hx
    simp only [he,H,bitMix_mulVec,mulVec_diagonal,q,normalizer_mul,hx]
    have eq := middle_pair i v x
    change ‖w (Function.update x i false)‖=‖w (Function.update x i true)‖ at eq
    simp [boolHadamardMatrix,eq]
  · intro j hj
    rw [he]
    exact mix_preserves _ (fun e => hj (e.symm ▸ hi)) (diagonal_preserves w q j (hw j hj))

/-- As bits are cleared, the cost of the two required diagonal phase
circuits halves at each step. -/
theorem prepare_to_origin (hn : 2 ≤ n) (v : Config n→ℂ) :
    ∃ C : TwoQubitCircuit n, C.gateCount ≤ 16*2^n ∧
      ∀ x : Config n, x≠(fun _ => false) → ((C.eval : Register n) *ᵥ v) x=0 := by
  classical
  have step (S : Finset (Fin n)) (v : Config n→ℂ) (hv : ∀ j∉S, Cleared v j) :
      ∃ P : ℕ, P+16 ≤ 16*2^S.card ∧ ∃ W : Register n, Realizes P W ∧ ∀ j, Cleared (W *ᵥ v) j := by
    induction S using Finset.induction_on generalizing v with
    | empty => exact ⟨0,by simp,1,Realizes.one n,by simpa only [one_mulVec] using
        (fun j => hv j (notMem_empty j))⟩
    | @insert i S hi ih =>
      obtain ⟨A,hA,hAi,hrest⟩ := clear_active hn (insert i S) v hv i (mem_insert_self ..)
      have hc (j : Fin n) (hj : j∉S) : Cleared (A *ᵥ v) j := by
        by_cases e : j=i
        · simpa only [e] using hAi
        · exact hrest j (fun h => (mem_insert.mp h).elim e hj)
      obtain ⟨P,hP,B,hB,hclear⟩ := ih _ hc
      refine ⟨_,?_,B*A,hB.mul hA,?_⟩
      · rw [card_insert_of_notMem hi,pow_succ]
        have hpos := Nat.one_le_two_pow (n:=S.card)
        omega
      · simpa only [←mulVec_mulVec] using hclear
  obtain ⟨P,hP,W,⟨z,hz,C,hC,rfl⟩,hc⟩ := step univ v (by simp)
  rw [card_univ,Fintype.card_fin] at hP
  refine ⟨C,by omega,?_⟩
  intro x hx
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hx
  have h := hc i x (by simpa using hi)
  rw [smul_mulVec] at h
  change z*((C.eval : Register n) *ᵥ v) x=0 at h
  exact (mul_eq_zero.mp h).resolve_left (fun e => by simp [e] at hz)

#print axioms prepare_to_origin
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis.MultiplexedPhases
