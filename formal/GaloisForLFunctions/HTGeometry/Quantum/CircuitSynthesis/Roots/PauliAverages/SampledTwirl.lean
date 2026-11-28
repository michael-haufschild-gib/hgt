import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.PauliAverages.Twirl
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.PauliAverages.Sampling.Empirical

/-! # Short lists of physical Pauli commutators -/

open Matrix Finset Complex
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages
noncomputable section
variable {K : ℕ}
private abbrev Reg (K : ℕ) := Matrix (Fin K → Bool) (Fin K → Bool) ℂ

theorem pauli_bracket_skew (U : Reg K) (j : Fin K → Option (Fin 3)) :
    star (pauliBracket U j) = -pauliBracket U j := by
  have hP : star (finitePauliMatrix j)=finitePauliMatrix j := finitePauliMatrix_isHermitian _
  simp only [pauliBracket,star_sub,star_mul,star_star,hP,Matrix.mul_assoc,neg_sub]

theorem pauli_bracket_norm (U : unitary (Reg K)) (j : Fin K → Option (Fin 3)) :
    ‖pauliBracket U.val j‖≤2 := by
  let P := finitePauliMatrix j
  have hP : P∈unitary (Reg K) := by
    have he : star P=P := finitePauliMatrix_isHermitian _
    rw [Unitary.mem_iff,he]
    exact ⟨finitePauliMatrix_mul_self _,finitePauliMatrix_mul_self _⟩
  have hQ : U.val*P*star U.val∈unitary (Reg K) := mul_mem (mul_mem U.2 hP) (U⁻¹).2
  apply (norm_sub_le ..).trans
  rw [CStarRing.norm_of_mem_unitary (mul_mem hQ hP),CStarRing.norm_of_mem_unitary (mul_mem hP hQ)]
  norm_num

/-- A list of $(K+1)n^2$ Pauli commutators recovers the skew part in the
normalized trace frame with operator error at most $16/n$. -/
theorem sampled_pauli_bracket (U : unitary (Reg K)) (n : ℕ) (hn : 0<n) :
    let τ := U.val.trace/(2:ℂ)^K
    ∃ a : Fin ((K+1)*n^2) → Fin K → Option (Fin 3),
      ‖(((K:ℝ)+1)*n^2)⁻¹ • (∑ j, pauliBracket U.val (a j))-(conj τ • U.val-τ • star U.val)‖
        ≤16/n := by
  intro τ
  let A (j : Fin K → Option (Fin 3)) := Complex.I • pauliBracket U.val j
  have hh (j) : (A j).IsHermitian := by
    change star (Complex.I • pauliBracket U.val j)=_
    rw [star_smul,pauli_bracket_skew,Complex.star_def,Complex.conj_I,neg_smul,smul_neg,neg_neg]
  have hb (j) : ‖A j‖≤2 := by
    simpa only [A,norm_smul,Complex.norm_I,one_mul] using pauli_bracket_norm U j
  have hd : Fintype.card (Fin K → Bool)≤2^(2*(K+1)) := by
    simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨a,ha⟩ := Sampling.empirical_mean A hh (by norm_num) hb n (K+1) hn (by omega) hd
  have hc : Fintype.card (Fin K → Option (Fin 3))=4^K := by simp
  have he {Z : Type} [Fintype Z] (f : Z → Fin K → Option (Fin 3)) :
      Sampling.matrixMean (A ∘ f)= Complex.I • ((Fintype.card Z:ℝ)⁻¹ • ∑ j, pauliBracket U.val (f j)) := by
    simp only [Sampling.matrixMean,Function.comp_apply,A,←Finset.smul_sum,smul_comm (Fintype.card Z:ℝ)⁻¹ Complex.I]
  have hf := mean_pauli_bracket U.val
  change ((4:ℂ)^K)⁻¹ • _=conj τ • U.val-τ • star U.val at hf
  have hm : Sampling.matrixMean A=Complex.I • (conj τ • U.val-τ • star U.val) := by
    rw [←hf]
    have h := he (Z:=Fin K → Option (Fin 3)) id
    simpa only [Function.comp_id,id_eq,hc,Nat.cast_pow,Nat.cast_ofNat,
      ←Complex.coe_smul,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_ofNat] using h
  rw [he a,hm,←smul_sub,norm_smul,Complex.norm_I,one_mul,Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow] at ha
  refine ⟨a,ha.trans_eq ?_⟩
  ring

#print axioms sampled_pauli_bracket
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages
