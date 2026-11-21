import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.OneGate
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion
import GaloisForLFunctions.HTGeometry.HaferkampCliffordSign
import GaloisForLFunctions.HTGeometry.HaferkampLiftedPauliTransport
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension

/-! # Physical circuits for arbitrary Pauli rotations -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem rotate_short_word {n : ℕ} (hn : 2 ≤ n) (P : Fin n → Option (Fin 3))
    (hw : pauliWeight P ≤ 2) (t : ℝ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit n, C.gateCount ≤ 1 ∧
      unitaryEvolution (finitePauliMatrix P) t = c • (C.eval : Reg n) := by
  classical
  by_cases hi : P = pauliIdentityLabel n
  · subst P
    have hI : finitePauliMatrix (pauliIdentityLabel n) = (1 : Reg n) := by
      ext x y
      exact finitePauliMatrix_pauliIdentityLabel x y
    let z := (t : ℂ) * (-Complex.I)
    refine ⟨Complex.exp z,by simp [z,Complex.norm_exp],TwoQubitCircuit.one n,by decide,?_⟩
    rw [hI,TwoQubitCircuit.one_eval,unitaryEvolution]
    change NormedSpace.exp (t • ((-Complex.I) • (1 : Reg n))) = Complex.exp z • 1
    rw [← exp_complex_smul_one_matrix]
    congr 1
    ext x y
    simp [z,Matrix.smul_apply,mul_assoc]
  · let Q : PauliTracelessLabel n 2 := ⟨P,hw,hi⟩
    let H := finitePauliSelfAdjointBasis (Fin n) P
    have hc : realPauliCoefficient H Q.val = 1 := by
      change (finitePauliSelfAdjointBasis (Fin n)).repr ((finitePauliSelfAdjointBasis (Fin n)) P) P = 1
      simp
    obtain ⟨z,hz,G,hG⟩ := exists_projective_twoQubitGate_eq_exp_twoLocalSkewGenerator hn H Q t
    refine ⟨z,hz,TwoQubitCircuit.singleOn _ _ (Q.coveringPair_distinct hn) G,le_rfl,?_⟩
    rw [TwoQubitCircuit.singleOn_eval]
    simpa only [twoLocalSkewGenerator,hc,Complex.ofReal_one,one_smul,unitaryEvolution] using hG

/-- A two-site Clifford merges two occupied sites into one. Conjugating
the shorter rotation by this gate and its inverse adds exactly two gates. -/
theorem exists_projective_pauli_rotation_circuit {n : ℕ} (hn : 2 ≤ n)
    (P : Fin n → Option (Fin 3)) (t : ℝ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∃ C : TwoQubitCircuit n, C.gateCount ≤ 2 * pauliWeight P + 1 ∧
      unitaryEvolution (finitePauliMatrix P) t = z • (C.eval : Reg n) := by
  classical
  induction hw : pauliWeight P using Nat.strong_induction_on generalizing P t with
  | h w ih =>
    by_cases hs : w ≤ 2
    · obtain ⟨z,hz,C,hC,h⟩ := rotate_short_word hn P (hw.trans_le hs) t
      exact ⟨z,hz,C,by omega,h⟩
    let S := Finset.univ.filter fun i => P i ≠ none
    have hcard : S.card = w := hw
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
    let R := updateTwoQubitPauliLabel P a b none (some 2)
    have hR : (Finset.univ.filter fun i => R i ≠ none) = S.erase a := by
      ext i
      by_cases hia : i = a
      · subst i
        simp [R,updateTwoQubitPauliLabel,Function.update_of_ne,hab]
      by_cases hib : i = b
      · subst i
        simp [R,updateTwoQubitPauliLabel,hia,hb]
      simp [R,S,updateTwoQubitPauliLabel,hia,hib]
    have hr : pauliWeight R = w - 1 := by
      rw [pauliWeight,hR,Finset.card_erase_of_mem ha,hcard]
    obtain ⟨G,c,_,hc⟩ := finitePauliMatrix_exists_twoQubitLift_transport P a b hab
      (Or.inl (Finset.mem_filter.mp ha).2)
    let L := TwoQubitCircuit.singleOn a b hab G
    have hg : L.eval = twoQubitLift a b hab G := TwoQubitCircuit.singleOn_eval _ _ _ _
    let V : Reg n := L.eval
    have hV : V ∈ unitary (Reg n) := L.eval.2
    have htr : V * finitePauliMatrix P * star V = c • finitePauliMatrix R := by
      simpa only [V,hg,Matrix.star_eq_conjTranspose] using hc
    have he (s : ℝ) := unitaryEvolution_conj V (finitePauliMatrix P) (Unitary.isUnit_coe (U := L.eval)) s
    have he' : ∃ s : ℝ, V * unitaryEvolution (finitePauliMatrix P) t * star V =
        unitaryEvolution (finitePauliMatrix R) s := by
      have h := he t
      rw [inv_eq_star_of_mem_unitary hV,htr] at h
      rcases pauli_conjugation_scalar_eq_one_or_neg_one L.eval P R c htr with h₁ | h₁
      · exact ⟨t,by simpa [h₁] using h.symm⟩
      · exact ⟨-t,by simpa [h₁,unitaryEvolution] using h.symm⟩
    obtain ⟨s,heq⟩ := he'
    obtain ⟨z,hz,C,hC,hrot⟩ := ih (w-1) (by omega) R s hr
    refine ⟨z,hz,L.adjoint.mul (C.mul L),?_,?_⟩
    · simp only [TwoQubitCircuit.mul_gateCount]
      change 1 + C.gateCount + 1 ≤ _
      omega
    rw [TwoQubitCircuit.mul_eval,TwoQubitCircuit.mul_eval,TwoQubitCircuit.adjoint_eval]
    change _ = z • (star V * ((C.eval : Reg n) * V))
    have hback := congrArg (fun A : Reg n => star V * A * V) (heq.trans hrot)
    have hcanc (A : Reg n) : star V * (V * A * star V) * V = A := by
      calc
        _ = (star V * V) * A * (star V * V) := by simp only [mul_assoc]
        _ = _ := by simp only [(Unitary.mem_iff.mp hV).1,one_mul,mul_one]
    change star V * (V * _ * star V) * V = star V * (z • (C.eval : Reg n)) * V at hback
    simpa only [hcanc,Matrix.mul_smul,Matrix.smul_mul,mul_assoc] using hback

#print axioms exists_projective_pauli_rotation_circuit
end
end GaloisForLFunctions.HTGeometry
