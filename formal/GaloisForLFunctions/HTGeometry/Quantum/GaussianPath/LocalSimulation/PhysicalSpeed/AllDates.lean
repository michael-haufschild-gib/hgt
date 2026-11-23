import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.PhysicalSpeed.BoxIncrement

/-! # Coupling-normalized transfer time between robust and affordable dates -/
open Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches.PhysicalSpeed
open PrescribedTimes
noncomputable section

/-- One coupling cap protects every robust date from every affordable
date on the entire two-sided trajectory, including dates selected after
observing the evolution. -/
theorem all_dates_travel {n : ℕ} (x : PrefixIndex n → ℝ)
    (hn : 128 ≤ (n+2).sqrt) {R : ℝ} (hR : 0 < R) (hcap : ∀ i, |x i| ≤ R) :
    let N := n+2
    let P := nearHilbertContinuousCircuitBudget N
    ∀ {ε σ t : ℝ}, ε+1/100 < 9/80 → 9/80 ≤ pathGateDistance n P x σ →
      ∀ {s : ℕ}, s ≤ P/2 → pathGateDistance n s x t ≤ ε →
        travelProduct N < R*|σ-t| := by
  intro N P ε σ t hε hσ s hs ht
  let H := prefixGenerator n x
  have hfar : ProjectiveCircuitSeparated N (ε+1/100) P (unitaryEvolution H.val σ) := by
    intro z hz C hC
    by_contra! h
    have hd := (hasProjectiveCircuitApproximation_iff_infDist
      (unitaryEvolution H.val σ) P (ε+1/100)).mp ⟨z,hz,C,hC,h⟩
    exact hε.not_ge (hσ.trans hd)
  by_contra! hnear
  have hi := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val (σ-t)) (P/2) (1/100:ℝ)).mpr
    (capped_increment x (σ-t) hn hR hcap hnear)
  have hd := projectiveCircuitSeparated_unitaryEvolution_backward_cone H
    (by omega : P/2 ≤ P) hfar hi (show ε+1/100 ≤ ε+1/100 from le_rfl)
  rw [show σ-(σ-t)=t by ring] at hd
  obtain ⟨z,hz,C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val t) s ε).mpr ht
  exact (not_lt_of_ge he) (hd z hz C (by omega))

#print axioms all_dates_travel
end
end GaloisForLFunctions.HTGeometry.LocalPatches.PhysicalSpeed
