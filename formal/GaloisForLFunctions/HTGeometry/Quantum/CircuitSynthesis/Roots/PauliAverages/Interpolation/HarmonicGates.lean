import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.PauliAverages.Pulses.Synthesis
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.PauliAverages.Interpolation.TraceCoordinates

/-! # Physical gate bounds for signed spectral harmonics -/

open Matrix Complex NormedSpace
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Interpolation
noncomputable section
private abbrev Reg (K : ℕ) := Matrix (Fin K → Bool) (Fin K → Bool) ℂ
local instance (K : ℕ) : CStarAlgebra (Reg K) where

private theorem fit_star {K n : ℕ} {e : ℝ} {X : Reg K}
    (h : HasProjectiveCircuitApproximation K e n X) :
    HasProjectiveCircuitApproximation K e n (star X) := by
  obtain ⟨z,hz,C,hC,hfit⟩ := h
  refine ⟨conj z,by simpa only [Complex.norm_conj] using hz,C.adjoint,hC,?_⟩
  rw [TwoQubitCircuit.adjoint_eval]
  change ‖star X-conj z • star C.eval.val‖ ≤ e
  rwa [←Complex.star_def,←star_smul,←star_sub,norm_star]

/-- Each positive or negative harmonic takes at most four calls
to the input circuit per sampled power and pulse. -/
theorem harmonic_gate {K : ℕ} (hK : 2 ≤ K) (C : TwoQubitCircuit K)
    (V : unitary (Reg K)) (θ : (Fin K → Bool) → ℝ) (hC : C.eval.val=packet V θ)
    (l m : ℕ) (hm : 0 < m) (t : ℝ) (ht : |t| ≤ 1) :
    HasProjectiveCircuitApproximation K (30/(m:ℝ)) (4*(K+1)*m^3*(l*C.gateCount+2*K+1))
      (packet V (fun i => 2*t*sineReading θ l i)) := by
  have pos_case (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
      HasProjectiveCircuitApproximation K (30/(m:ℝ)) (4*(K+1)*m^3*(l*C.gateCount+2*K+1))
        (packet V (fun i => 2*u*sineReading θ l i)) := by
    have h := Pulses.physical_twirl hK (C.pow l) m hm hu hu'
    rw [TwoQubitCircuit.pow_gateCount,Pulses.traceSkew,TwoQubitCircuit.pow_eval_coe,hC] at h
    have he := trace_exponential V θ l u
    simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] at he
    rwa [←he]
  rcases le_total 0 t with h|h
  · exact pos_case t h ((le_abs_self _).trans ht)
  · have hh := fit_star (pos_case (-t) (neg_nonneg.mpr h) ((neg_le_abs _).trans ht))
    simpa only [packet_star,mul_neg,neg_mul,neg_neg] using hh

#print axioms harmonic_gate
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Interpolation
