import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.LocalTangents.Conormal
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.CrossingDeadline
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ElapsedWindow.ContactMargin

/-! # Simultaneous local stationarity at the original first return -/

open Filter MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents
open PhaseBoundary.FiniteCertificates.BudgetComparisons PrecisionReturns SpectralFilling.ReplicaOrders
noncomputable section

/-- At the original first affordable date, one extra bond sweep advances the
return or every implementing circuit has a real norming functional which
annihilates all onsite, nearest-neighbour and scalar rotations simultaneously. -/
theorem gaussian_first_return_conormal :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let H := generator (pathPauliDisorderShell ω (k+1))
      let P := nearHilbertContinuousCircuitBudget K
      let σ := Iterated.crossing H P 0
      ∀ s ≤ P, let v := firstVisit H σ s (1/10)
        let U := unitaryEvolution H.val v
        (∃ (C : TwoQubitCircuit K) (z : ℂ), C.gateCount ≤ s ∧ ‖z‖=1 ∧ ‖U-z • C.eval.val‖≤1/10) ∧
          (firstVisit H σ (s+(k+2)) (1/10)<v ∨
            ∀ (C : TwoQubitCircuit K) (z : ℂ), C.gateCount ≤ s → ‖z‖=1 →
              let Q := z • C.eval.val
              ‖U-Q‖≤1/10 → ‖U-Q‖=1/10 ∧ ∃ φ : StrongDual ℝ (Register K),
                ‖φ‖=1 ∧ ‖φ (U-Q)‖=1/10 ∧ ∀ y c, φ (direction Q y c)=0) := by
  obtain ⟨_,_,hcross⟩ := gaussian_replica_crossing_deadline
  filter_upwards [hcross] with ω hw
  filter_upwards [hw] with k hk
  intro K H P σ s hs v U
  have he : (0:ℝ)<1/10 := by norm_num
  have hc := (hk 0).1.1
  change 0≤σ ∧ 9/80≤orbitCircuitDistance H P σ at hc
  have hfar : 1/10<orbitCircuitDistance H s σ := by
    by_contra! ha
    obtain ⟨z,hz,C,hC,hfit⟩ := (hasProjectiveCircuitApproximation_iff_infDist ..).mpr ha
    have hh : orbitCircuitDistance H P σ≤1/10 :=
      (hasProjectiveCircuitApproximation_iff_infDist ..).mp ⟨z,hz,C,hC.trans hs,hfit⟩
    linarith only [hc.2,hh]
  constructor
  · obtain ⟨_,z,hz,C,hC,hfit⟩ := (firstVisit_isLeast H σ s he).1
    exact ⟨C,z,hC,hz,hfit⟩
  · by_cases hstrict : firstVisit H σ (s+(k+2)) (1/10)<v
    · exact Or.inl hstrict
    right
    have hboundary : 1/10≤orbitCircuitDistance H (s+(k+2)) v :=
      le_of_not_gt fun h => hstrict (ElapsedWindow.strict_of_first_margin H σ s _ he hfar h)
    intro C z hC hz Q hfit
    have hlower (D : TwoQubitCircuit K) (hD : D.gateCount ≤ s+(k+2)) (w : ℂ) (hw : ‖w‖=1) :
        1/10≤‖U-w • D.eval.val‖ := hboundary.trans
      ((hasProjectiveCircuitApproximation_iff_infDist ..).mp ⟨w,hw,D,hD,le_rfl⟩)
    have hQ := hfit.antisymm (hlower C (hC.trans (Nat.le_add_right ..)) z hz)
    obtain ⟨φ,hφ,hX,hzero⟩ := contact_conormal U C hz fun D hD w hw =>
      hQ.le.trans (hlower D (hD.trans (Nat.add_le_add_right hC _)) w hw)
    have hop := φ.le_opNorm (U-Q)
    rw [hX,hQ] at hop
    exact ⟨hQ,φ,hφ.antisymm (by linarith only [hop]),hX.trans hQ,hzero⟩

#print axioms gaussian_first_return_conormal
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents
