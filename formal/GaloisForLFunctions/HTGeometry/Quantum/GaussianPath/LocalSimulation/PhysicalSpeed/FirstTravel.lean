import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.PhysicalSpeed.BoxIncrement
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.PrefixProbability

/-! # Coupling-normalized travel to and from the first near-Hilbert crossing -/
open Filter Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches.PhysicalSpeed
open PrescribedTimes ShortWindows
noncomputable section

/-- For almost every frozen chain at each sufficiently large size, onset
and the first subsequent half-budget wait both exceed the local travel
product divided by any upper bound on the absolute couplings. -/
theorem gaussian_capped_first_passage :
    ∀ᶠ k : ℕ in atTop, ∀ᵐ ω ∂pathPauliDisorderLaw,
      let N := k+3
      let P := nearHilbertContinuousCircuitBudget N
      let x := prefixPoint k ω
      ∀ R : ℝ, 0 < R → (∀ i, |x i| ≤ R) →
        travelProduct N/R < min (crossingOrigin (k+1) P (9/80) x) (crossingWait (k+1) P (P/2) x) := by
  have hN := (tendsto_add_atTop_nat 3).eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier
  filter_upwards [hN,eventually_ge_atTop (128*128)] with k hent hk
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hspec
  intro N P x R hR hcap
  let u := pathPauliDisorderShell ω (k+1)
  let H : selfAdjoint (Register N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  let T := travelProduct N/R
  have hT : 0 ≤ T := by dsimp only [T,travelProduct,localCrossingWidth]; positivity
  have hgen : numberedGenerator (k+1) x = H.val := numberedGenerator_shell u
  have hd (j) (t) : pathGateDistance (k+1) j x t = orbitCircuitDistance H j t := by
    unfold pathGateDistance orbitCircuitDistance
    rw [hgen]
  have hinc (t : ℝ) (ht : |t| ≤ T) : HasProjectiveCircuitApproximation N (1/100:ℝ)
      (P/2) (unitaryEvolution H.val t) := by
    apply (hasProjectiveCircuitApproximation_iff_infDist ..).mpr
    apply (hd _ _).symm.trans_le
    apply capped_increment x t (Nat.le_sqrt.mpr (by omega)) hR hcap
    exact (mul_comm R _).trans_le ((le_div_iff₀ hR).mp ht)
  let d := 2^N-1
  let e : (Fin N → Bool) ≃ Fin (d+1) := (Fintype.equivFin _).trans
    (finCongr (by simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
                  have hpos : 0 < (2:ℕ)^N := by positivity
                  dsimp [d]; omega))
  obtain ⟨σ,hσ,he,hprior,hwin,_⟩ := first_circuit_threshold_of_increment e H
    ((hspec k).comp_equiv e.symm) hent T hT (by omega : 2*(P/2) ≤ P) hinc
  have hor := crossingOrigin_eq_of_first (hT.trans hσ.le) ((hd _ σ).trans he)
    (fun v hv => (hd _ v).trans_lt (hprior v hv))
  apply lt_min (hor.symm ▸ hσ)
  by_contra! hx
  obtain ⟨v,hv,he⟩ := (crossingWait_le_iff (k+1) P (P/2) x T).mp hx
  rw [hor] at hv
  have hsep := hwin v ⟨(sub_le_self σ hT).trans hv.1,hv.2⟩
  obtain ⟨z,hz,C,hC,herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist
    (unitaryEvolution H.val v) (P/2) (1/10:ℝ)).mpr ((hd _ v).symm.trans_le he)
  exact herr.not_lt (hsep z hz C hC)

#print axioms gaussian_capped_first_passage
end
end GaloisForLFunctions.HTGeometry.LocalPatches.PhysicalSpeed
