import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.LocalTangents.Multiplicity.Correction
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.BudgetComparisons.BondTies
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.CrossingDeadline
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ElapsedWindow.ContactMargin

/-! # Active multiplicity at the first physical return -/

open Filter MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents.Multiplicity
open PhaseBoundary.FiniteCertificates.BudgetComparisons PrecisionReturns SpectralFilling.ReplicaOrders
noncomputable section

/-- Every implementing circuit at the original first return can advance the
date using at most `(2K+1)r²` additional gates, where `r` is the dimension
of its norming input space. The estimate holds at the prescribed error. -/
theorem gaussian_first_return_active_rank :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let H := generator (pathPauliDisorderShell ω (k+1))
      let P := nearHilbertContinuousCircuitBudget K
      let σ := Iterated.crossing H P 0
      ∀ s ≤ P, let v := firstVisit H σ s (1/10)
        let U := unitaryEvolution H.val v
        (∃ (C : TwoQubitCircuit K) (z : ℂ), C.gateCount ≤ s ∧ ‖z‖=1 ∧ ‖U-z • C.eval.val‖≤1/10) ∧
          ∀ (C : TwoQubitCircuit K) (z : ℂ), C.gateCount ≤ s → ‖z‖=1 →
            let X := U-z • C.eval.val
            ‖X‖≤1/10 → ‖X‖=1/10 ∧
              firstVisit H σ (C.gateCount+(activeRank X)^2*(2*K+1)) (1/10)<v := by
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
  intro C z hC hz X hfit
  have hX : ‖X‖=1/10 := hfit.antisymm (le_of_not_gt fun h => by
    have hd : orbitCircuitDistance H s v≤‖X‖ :=
      (hasProjectiveCircuitApproximation_iff_infDist ..).mp ⟨z,hz,C,hC,le_rfl⟩
    exact (lt_irrefl v) (ElapsedWindow.strict_of_first_margin H σ s s he hfar (hd.trans_lt h)))
  let A := (⟨U,unitaryEvolution_mem_unitary H.2 v⟩ : unitary (Matrix (Fin K → Bool) (Fin K → Bool) ℂ))
  have hpos : 0<‖X‖ := he.trans_eq hX.symm
  have hsmall : ‖X‖<2 := hX.trans_lt (by norm_num)
  obtain ⟨D,hD,w,hw,hgain⟩ := rank_correction (N:=K) (by dsimp [K]; omega) A C hz hpos hsmall
  refine ⟨hX,ElapsedWindow.strict_of_first_margin H σ s _ he hfar ?_⟩
  exact lt_of_le_of_lt ((hasProjectiveCircuitApproximation_iff_infDist ..).mp
    ⟨w,hw,D,hD,le_rfl⟩) (hgain.trans_eq hX)

#print axioms gaussian_first_return_active_rank
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents.Multiplicity
