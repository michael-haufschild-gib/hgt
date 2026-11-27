import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.SingleCut.Passage

/-! # Cheap increments at the original near-Hilbert crossing -/
open Filter MeasureTheory ProbabilityTheory Set Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open PrescribedTimes DiagonalSynthesis
noncomputable section

/-- A cheap increment around the original crossing delays every
actual half-budget first visit by the same amount. -/
theorem delay_of_cheap :
    ∀ᶠ k : ℕ in atTop, ∀ᵐ ω ∂pathPauliDisorderLaw,
      let n := k+1
      let P := nearHilbertContinuousCircuitBudget (n+2)
      let u := pathPauliDisorderShell ω n
      let x := fun i => u (pathCoeffEquiv n i)
      ∀ T > (0:ℝ), ∀ B : ℕ, 2*B ≤ P →
        (∀ t : ℝ, |t| ≤ T → HasProjectiveCircuitApproximation (n+2) (1/100) B
          (unitaryEvolution (pathHamiltonian u) t)) →
        T < crossingOrigin n P (9/80) x ∧ ∀ s ≤ P/2, T < crossingWait n P s x := by
  have hen := (tendsto_add_atTop_nat 3).eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier
  filter_upwards [hen] with k hen
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro n P u x T hT B hB hinc
  let H : selfAdjoint (Register (n+2)) := ⟨_,isSelfAdjoint_pathHamiltonian u⟩
  let d := 2^(n+2)-1
  let e : (Fin (n+2)→Bool) ≃ Fin (d+1) := (Fintype.equivFin _).trans
    (finCongr (by simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
                  have hd : 0 < (2:ℕ)^(n+2) := by positivity
                  dsimp [d]; omega))
  obtain ⟨σ,hσ,hd,hpre,hnone,_⟩ := first_circuit_threshold_of_increment e H
    ((hω k).comp_equiv e.symm) hen T hT.le hB hinc
  have hdist (j : ℕ) (t : ℝ) : pathGateDistance n j x t=orbitCircuitDistance H j t := by
    change pathGateDistance n j (fun i => u (pathCoeffEquiv n i)) t=_
    rw [pathGateDistance,numberedGenerator_shell]; rfl
  have ho := crossingOrigin_eq_of_first (hT.trans hσ).le ((hdist P σ).trans hd)
    (fun t ht => (hdist P t).trans_lt (hpre t ht))
  refine ⟨ho.symm ▸ hσ,fun s hs => ?_⟩
  by_contra! he
  obtain ⟨t,ht,hvisit⟩ := (crossingWait_le_iff n P s x T).mp he
  rw [ho] at ht
  obtain ⟨z,hz,C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr ((hdist s t).symm.trans_le hvisit)
  exact (hnone t ⟨(sub_le_self σ hT.le).trans ht.1,ht.2⟩ z hz C (hC.trans hs)).not_ge he

#print axioms delay_of_cheap
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
