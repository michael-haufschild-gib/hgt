import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FirstReturnDates
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.JointFrequencies

/-! # The first empty return from the perturbed chain's own robust crossing -/
open MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section
open PrecisionReturns
private abbrev Reg (n : ℕ) := Matrix (Fin n→Bool) (Fin n→Bool) ℂ

/-- At the prescribed physical error, the actual return date after the first
robust crossing avoids any countable schedule, even one chosen from the
unperturbed Gaussian background. Only countably many increments are excepted. -/
theorem gaussian_boundary_crossing_return_dates :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ∀ S : Set ℝ, S.Countable →
      ∃ B : Set ℝ, B.Countable ∧ ∀ z ∉ B,
        let N := k+3
        let H : selfAdjoint (Reg N) := ⟨boundaryHamiltonian ω k z,(boundaryHermitian ω k z).isSelfAdjoint⟩
        let P := nearHilbertContinuousCircuitBudget N
        ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
          (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧ firstVisit H σ 0 (1/10)∉S := by
  have hlim : Tendsto (fun k : ℕ => k+3) atTop atTop := by
    rw [tendsto_atTop]
    intro n
    exact eventually_atTop.2 ⟨n,fun k h => by omega⟩
  have hs : (1/10:ℝ)<Real.sqrt 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
  filter_upwards [gaussian_boundary_joint_nonresonance,gaussian_boundary_first_empty_dates] with ω hf hd
  filter_upwards [hlim.eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier] with k hent
  intro S hS
  obtain ⟨B,hB,hn⟩ := hf k
  obtain ⟨C,hC,hv⟩ := hd k (1/10) (by norm_num) hs S hS
  refine ⟨B∪C,hB.union hC,?_⟩
  intro z hz N H P
  have hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues := by
    intro q hb hq
    exact (hn z (fun h => hz (Or.inl h)) 0 q (by simp) hb (by simpa only [Pi.zero_apply,Int.cast_zero,zero_mul,Finset.sum_const_zero,zero_add] using hq)).2
  let d := 2^N-1
  let e : (Fin N→Bool) ≃ Fin (d+1) := (Fintype.equivFin _).trans (finCongr (by
    simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
    have hpos : 0<(2:ℕ)^N := by positivity
    dsimp [d]; omega))
  have hinc (t : ℝ) (ht : |t|≤0) : HasProjectiveCircuitApproximation N (1/100:ℝ) 0 (unitaryEvolution H.val t) := by
    obtain rfl := abs_nonpos_iff.mp ht
    refine ⟨1,norm_one,TwoQubitCircuit.one N,by rfl,?_⟩
    simp [TwoQubitCircuit.one_eval,unitaryEvolution]
  obtain ⟨σ,hσ,he,hprior,_,_⟩ := first_circuit_threshold_of_increment e H (hmax.comp_equiv e.symm)
    hent 0 le_rfl (show 2*0≤P from Nat.zero_le _) hinc
  refine ⟨σ,hσ,he,hprior,hv z (fun h => hz (Or.inr h)) σ hσ ?_⟩
  by_contra! h
  obtain ⟨c,hc,Q,hQ,herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ 0 (1/10:ℝ)).mpr h
  have hp : orbitCircuitDistance H P σ≤1/10 := (hasProjectiveCircuitApproximation_iff_infDist _ P _).mp
    ⟨c,hc,Q,hQ.trans (Nat.zero_le _),herr⟩
  rw [he] at hp
  norm_num at hp

#print axioms gaussian_boundary_crossing_return_dates
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
