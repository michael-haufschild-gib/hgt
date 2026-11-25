import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns.Multiples

/-! # A necessary interaction strength for a long actual first return -/

open Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns
open PrescribedTimes WeakBonds
noncomputable section

/-- Testing the cut clock at multiples of the actual onset gives a
pathwise alternative at every bond. A wait beyond all those multiples
forces a lower bound on the bond action accumulated since the identity. -/
theorem first_wait_or_bond_strength {n : ℕ} (u : PathShell n) (a : Fin (n+1)) (P s Q : ℕ) :
    let x := fun i => u (pathCoeffEquiv n i)
    let σ := crossingOrigin n P (9/80) x
    let M : ℕ := (Q+1)^(2^(leftBlock a).card+2^(rightBlock a).card)
    crossingWait n P s x ≤ ((M:ℝ)-1)*σ ∨
       1/10 < 4*π/(Q+1:ℝ)+σ*(M:ℝ)*‖edgePart u a‖ := by
  intro x σ M
  by_cases h : 1/10 < 4*π/(Q+1:ℝ)+σ*(M:ℝ)*‖edgePart u a‖
  · exact Or.inr h
  have hσ : 0≤σ := Real.sInf_nonneg fun _ h => h.1
  obtain ⟨q,hq,hqM,hfit⟩ := perturbed_cut_return u a σ Q
  have hq' : 1≤(q:ℝ) := by exact_mod_cast hq
  have hqM' : (q:ℝ)≤(M:ℝ) := by exact_mod_cast hqM
  have htime : σ*(q:ℝ)≤σ*(M:ℝ) := mul_le_mul_of_nonneg_left hqM' hσ
  rw [abs_of_nonneg (mul_nonneg hσ (Nat.cast_nonneg q))] at hfit
  have hnorm : ‖unitaryEvolution (pathHamiltonian u) (σ*q)-1‖≤1/10 :=
    hfit.trans ((add_le_add le_rfl
      (mul_le_mul_of_nonneg_right htime (norm_nonneg _))).trans (le_of_not_gt h))
  left
  apply (crossingWait_le_iff ..).mpr
  have hdate : σ*(M:ℝ)=σ+((M:ℝ)-1)*σ := by ring
  refine ⟨σ*q,⟨le_mul_of_one_le_right hσ hq',htime.trans_eq hdate⟩,?_⟩
  change pathGateDistance n s (fun i => u (pathCoeffEquiv n i)) (σ*q)≤1/10
  rw [pathGateDistance,numberedGenerator_shell]
  apply (hasProjectiveCircuitApproximation_iff_infDist ..).mp
  refine ⟨1,norm_one,TwoQubitCircuit.one _,Nat.zero_le _,?_⟩
  rw [TwoQubitCircuit.one_eval,one_smul]
  exact hnorm

#print axioms first_wait_or_bond_strength
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns
