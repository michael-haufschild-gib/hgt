import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.PauliAverages.Pulses.Circuit
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.PauliAverages.Pulses.Cycles
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.PauliAverages.SampledTwirl
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.UniformGateCap
import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw

/-! # Physical synthesis of the trace-weighted skew part of a circuit -/

open Matrix Finset NormedSpace Complex
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Pulses
open private product_circuit from GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.UniformGateCap
noncomputable section
private abbrev Reg (K : ℕ) := Matrix (Fin K → Bool) (Fin K → Bool) ℂ
local instance (K : ℕ) : CStarAlgebra (Reg K) where

/-- Scalar phase cancels between the normalized trace and its unitary. -/
def traceSkew {K : ℕ} (U : Reg K) : Reg K :=
  let τ := U.trace/(2:ℂ)^K
  conj τ • U-τ • star U

theorem traceSkew_mem {K : ℕ} (U : Reg K) : traceSkew U∈skewAdjoint (Reg K) := by
  rw [skewAdjoint.mem_iff]
  simp only [traceSkew,star_sub,star_smul,star_star,Complex.star_def,Complex.conj_conj,neg_sub]

/-- Up to time one the exponential of the Pauli mean has a circuit of
cost $4(K+1)m^3(s+2K+1)$ and projective operator error at most $30/m$. -/
theorem physical_twirl {K : ℕ} (hK : 2 ≤ K) (C : TwoQubitCircuit K)
    (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    HasProjectiveCircuitApproximation K (30/(m:ℝ)) (4*(K+1)*m^3*(C.gateCount+2*K+1))
      (exp (t • traceSkew C.eval.val)) := by
  let N := (K+1)*m^2
  have hN : m^2 ≤ N := by
    change m^2 ≤ (K+1)*m^2
    rw [Nat.add_mul,one_mul]; omega
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hNp : (0:ℝ) < N := by dsimp [N]; positivity
  let b := Real.sqrt (t/(m*N))
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hb₁ : b ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    apply (div_le_one (by positivity)).mpr
    exact ht'.trans (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hm)
      (by exact_mod_cast (show 0 < N by dsimp [N]; positivity)))
  obtain ⟨a,ha⟩ := sampled_pauli_bracket C.eval m hm
  let X (j : Fin N) := pauliBracket C.eval.val (a j)
  have hx (j) : X j∈skewAdjoint (Reg K) := (skewAdjoint.mem_iff).mpr (pauli_bracket_skew _ _)
  have hn (j) : ‖X j‖ ≤ 2 := pauli_bracket_norm _ _
  choose G hcost herr using (fun j : Fin N => bracket_circuit hK C (a j) hb hb₁)
  let Y (j : Fin N) := (G j).eval.val
  have hy (j) : Y j∈unitary (Reg K) := (G j).eval.2
  have hstep := sweep_error N m hm hN X Y hx hn hy ht ht' herr
  let mean := (N:ℝ)⁻¹ • ∑ j, X j
  have hmX : mean∈skewAdjoint (Reg K) :=
    skewAdjoint.smul_mem _ ((skewAdjoint (Reg K)).sum_mem (fun j _ => hx j))
  have herr' : ‖mean-traceSkew C.eval.val‖ ≤ 16/m := by
    simpa only [mean,traceSkew,X,N,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow] using ha
  have hdist := exp_skewAdjoint_sub_exp_skewAdjoint_norm_le mean (traceSkew C.eval.val)
    hmX (traceSkew_mem _) t
  have hfit : ‖(List.ofFn Y).prod^m-exp (t • traceSkew C.eval.val)‖ ≤ 30/m := by
    apply (norm_sub_le_norm_sub_add_norm_sub _ (exp (t • mean)) _).trans
    apply (add_le_add hstep hdist).trans
    rw [abs_of_nonneg ht]
    have hb' := mul_le_mul ht' herr' (norm_nonneg _) zero_le_one
    calc
      _ ≤ 14/(m:ℝ)+1*(16/(m:ℝ)) := add_le_add_right hb' (14/(m:ℝ))
      _ = 30/(m:ℝ) := by ring
  have hgate (y) (hy' : y∈List.ofFn Y) :
      ∃ z : ℂ, ‖z‖=1 ∧ ∃ D : TwoQubitCircuit K,
        D.gateCount ≤ 4*(C.gateCount+2*K+1) ∧ y=z • D.eval.val := by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hy'
    exact ⟨1,norm_one,G j,hcost j,(one_smul _ _).symm⟩
  obtain ⟨z,hz,D,hD,he⟩ := product_circuit (List.ofFn Y) hgate
  refine ⟨z^m,by rw [norm_pow,hz,one_pow],D.pow m,?_,?_⟩
  · rw [TwoQubitCircuit.pow_gateCount]
    rw [List.length_ofFn] at hD
    exact (Nat.mul_le_mul_left m hD).trans_eq (by dsimp only [N]; ring)
  · rw [TwoQubitCircuit.pow_eval_coe,norm_sub_rev,←smul_pow,←he]
    exact hfit

#print axioms physical_twirl
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Pulses
