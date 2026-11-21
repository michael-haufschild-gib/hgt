import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.BitMix

/-! # Preparing a register state by clearing one bit at a time -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis
noncomputable section
private abbrev Config (n : ℕ) := Fin n → Bool

private def normalizer (z : ℂ) : ℂ := if z=0 then 1 else (‖z‖:ℂ)/z

private theorem normalizer_norm (z : ℂ) : ‖normalizer z‖=1 := by
  by_cases h : z=0
  · simp [normalizer,h]
  · simp [normalizer,h,norm_ne_zero_iff.mpr h]

private theorem normalizer_mul (z : ℂ) : normalizer z*z=(‖z‖:ℂ) := by
  by_cases h : z=0 <;> simp [normalizer,h]

/-- Amplitudes on the true side of the chosen register bit vanish. -/
def Cleared {n : ℕ} (v : Config n → ℂ) (i : Fin n) := ∀ x, x i=true → v x=0

private theorem diagonal_preserves {n : ℕ} (v p : Config n → ℂ) (i : Fin n) (h : Cleared v i) :
    Cleared (diagonal p *ᵥ v) i := fun x hx => by rw [mulVec_diagonal,h _ hx,mul_zero]

private theorem mix_preserves {n : ℕ} (v : Config n → ℂ) {i j : Fin n} (hne : j≠i) (h : Cleared v j) :
    Cleared (bitMix i *ᵥ v) j := by
  intro x hx
  have hf (b : Bool) : v (Function.update x i b) = 0 := h _ (by rwa [Function.update_of_ne hne])
  simp only [bitMix_mulVec,hf,mul_zero,add_zero]

private def firstPhase {n : ℕ} (i : Fin n) (v : Config n → ℂ) (x : Config n) :=
  (if x i then Complex.I else 1)*normalizer (v x)

private def middle {n : ℕ} (i : Fin n) (v : Config n → ℂ) :=
  bitMix i *ᵥ (diagonal (firstPhase i v) *ᵥ v)

/-- Choosing a relative quarter-turn before the first Hadamard makes the two
output amplitudes conjugate. A diagonal can then make them equal. -/
private theorem middle_pair {n : ℕ} (i : Fin n) (v : Config n → ℂ) (x : Config n) :
    ‖middle i v (Function.update x i false)‖ = ‖middle i v (Function.update x i true)‖ := by
  have h (b : Bool) : middle i v (Function.update x i b) =
      boolHadamardMatrix b false*(‖v (Function.update x i false)‖:ℂ) +
      boolHadamardMatrix b true*(Complex.I*(‖v (Function.update x i true)‖:ℂ)) := by
    simp [middle,bitMix_mulVec,mulVec_diagonal,firstPhase,Function.update_idem,mul_assoc,normalizer_mul]
  have hc : star (middle i v (Function.update x i false)) =
      middle i v (Function.update x i true) := by
    simp only [h,boolHadamardMatrix]
    simp
  rw [← hc,norm_star]

private def sweepCost (n : ℕ) := 2*(2^n*(2*n+1)+1)

private theorem clear_one {n : ℕ} (hn : 2 ≤ n) (v : Config n → ℂ) (i : Fin n) :
    ∃ W : Register n, Realizes (sweepCost n) W ∧ Cleared (W *ᵥ v) i ∧
      ∀ j, j≠i → Cleared v j → Cleared (W *ᵥ v) j := by
  let p := firstPhase i v
  let w := middle i v
  let q (x : Config n) := normalizer (w x)
  have hp (x : Config n) : ‖p x‖=1 := by
    dsimp [p,firstPhase]; split <;> simp [normalizer_norm]
  have hA := diagonal_phases hn p hp
  have hB := diagonal_phases hn q (fun _ => normalizer_norm _)
  have hH := bitMix_circuit hn i
  let W := bitMix i*(diagonal q*(bitMix i*diagonal p))
  have hreal : Realizes (sweepCost n) W := by
    convert hH.mul (hB.mul (hH.mul hA)) using 1
    dsimp [sweepCost]
    omega
  have hev : W *ᵥ v = bitMix i *ᵥ (diagonal q *ᵥ w) := by
    simp only [W,w,middle,p,← mulVec_mulVec]
  refine ⟨W,hreal,?_,?_⟩
  · intro x hx
    simp only [hev,bitMix_mulVec,mulVec_diagonal,q,normalizer_mul,hx]
    have eq := middle_pair i v x
    change ‖w (Function.update x i false)‖ = ‖w (Function.update x i true)‖ at eq
    simp [boolHadamardMatrix,eq]
  · intro j hj h
    rw [hev]
    apply mix_preserves _ hj
    apply diagonal_preserves
    exact mix_preserves _ hj (diagonal_preserves v p j h)

/-- At most 2n((2n+1)2^n+1) physical gates concentrate any register vector
on the all-zero configuration. -/
theorem prepare_to_zero {n : ℕ} (hn : 2 ≤ n) (v : Config n → ℂ) :
    ∃ C : TwoQubitCircuit n, C.gateCount ≤ n*(2*(2^n*(2*n+1)+1)) ∧
      ∀ x : Config n, x ≠ (fun _ => false) → ((C.eval : Register n) *ᵥ v) x = 0 := by
  classical
  have h (s : Finset (Fin n)) : ∃ W : Register n, Realizes (s.card*sweepCost n) W ∧
      ∀ i ∈ s, Cleared (W *ᵥ v) i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by simpa using Realizes.one n,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨W,hW,hc⟩ := ih
      obtain ⟨V,hV,hVi,hVj⟩ := clear_one hn (W *ᵥ v) i
      refine ⟨V*W,?_,?_⟩
      · rw [Finset.card_insert_of_notMem hi,Nat.add_mul,Nat.one_mul,Nat.add_comm]
        exact hV.mul hW
      · intro j hj
        rw [← mulVec_mulVec]
        rcases Finset.mem_insert.mp hj with rfl|hj
        · exact hVi
        · exact hVj j (fun he => hi (he ▸ hj)) (hc j hj)
  obtain ⟨W,⟨z,hz,C,hC,rfl⟩,hc⟩ := h Finset.univ
  refine ⟨C,by simpa [sweepCost] using hC,?_⟩
  intro x hx
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hx
  have hh := hc i (Finset.mem_univ i) x (by simpa using hi)
  rw [smul_mulVec] at hh
  change z*((C.eval : Register n) *ᵥ v) x = 0 at hh
  exact (mul_eq_zero.mp hh).resolve_left (fun h => by simp [h] at hz)

#print axioms prepare_to_zero
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis
