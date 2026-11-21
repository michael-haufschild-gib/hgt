import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.PhaseComparison
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage

/-! # First continuous visit to a closed circuit tube at arbitrary precision -/
open Matrix Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns
noncomputable section
variable {n : ℕ}

/-- Affordable times from the prescribed observation origin. -/
def visitSet (H : selfAdjoint (Register n)) (a : ℝ) (s : ℕ) (ε : ℝ) : Set ℝ :=
  {t | a ≤ t ∧ HasProjectiveCircuitApproximation n ε s (unitaryEvolution H.val t)}

/-- First affordable time, including the origin if it already qualifies. -/
def firstVisit (H : selfAdjoint (Register n)) (a : ℝ) (s : ℕ) (ε : ℝ) : ℝ :=
  sInf (visitSet H a s ε)

theorem firstVisit_physical_error (H : selfAdjoint (Register n)) (a : ℝ) (s : ℕ) :
    firstVisit H a s (1/10) = firstCircuitVisit H s a := rfl

/-- At each positive accuracy, compactness of bounded circuit images and
simultaneous phase approximation make the infimum an attained minimum. -/
theorem firstVisit_isLeast (H : selfAdjoint (Register n)) (a : ℝ) (s : ℕ) {ε : ℝ} (hε : 0 < ε) :
    IsLeast (visitSet H a s ε) (firstVisit H a s ε) := by
  have hd : 0 < (2:ℕ)^n := Nat.two_pow_pos _
  let e : (Fin n → Bool) ≃ Fin ((2^n-1)+1) := (Fintype.equivFin _).trans
    (finCongr (by simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]; omega))
  obtain ⟨Q,hQ⟩ := exists_nat_gt (2*π/ε)
  obtain ⟨u,hu,z,hz,C,hC,hh⟩ := projective_operator_zero_gate_return_after e H a Q
  have htol : 2*π/(Q+1:ℝ) ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hQ
    linarith only [hQ,hε]
  have hne : (visitSet H a s ε).Nonempty := ⟨u,by linarith only [hu.1,le_abs_self a],
    z,hz,C,by omega,hh.trans htol⟩
  have hb : BddBelow (visitSet H a s ε) := ⟨a,fun _ h => h.1⟩
  have hset : visitSet H a s ε = Ici a ∩ {t | orbitCircuitDistance H s t ≤ ε} := by
    ext t
    exact and_congr_right fun _ => hasProjectiveCircuitApproximation_iff_infDist _ s ε
  have hc : IsClosed (visitSet H a s ε) := by
    rw [hset]
    exact isClosed_Ici.inter (isClosed_le (orbitCircuitDistance_lipschitz H s).continuous continuous_const)
  exact ⟨hc.csInf_mem hne hb,fun _ ht => csInf_le hb ht⟩

#print axioms firstVisit_isLeast
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns
