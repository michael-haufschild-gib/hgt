import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.TimedReflection
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.CutoffClock

/-! # First-passage bounds from a sliding phase cover -/
open Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.PlateauConfidence
open PassageMoments
noncomputable section

/-- A hard sign dates the first crossing. A scalar visit within the
next window dates the first return, simultaneously for every budget. -/
theorem clock_bounds_first_passage (k : ℕ) (ω : PathPauliDisorder) (G : ℝ) :
    let n := k+1
    let N := k+3
    let D : ℕ := 2^N
    let P := nearHilbertContinuousCircuitBudget N
    let u := pathPauliDisorderShell ω n
    let H : selfAdjoint (Matrix (Fin N → Bool) (Fin N → Bool) ℂ) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    let x := fun i => u (pathCoeffEquiv n i)
    atMostQuarterCircuitEntropyBound N P < ((2^(D-1):ℕ):ℝ) →
    (∃ e : (Fin N → Bool) ≃ Fin ((D-1)+1), ∀ a : ℝ, ∀ z : Fin (D-1) → ℝ,
      ∃ v ∈ Icc a (a+G), ∀ j, turnDist
        (v*RHTower.zeroProjectiveFrequency (H.2.isHermitian.eigenvalues ∘ e.symm) j-z j)<1/80) →
    passageMax k 0 x≤G := by
  intro n N D P u H x hent ⟨e,he⟩
  let σ := crossingOrigin n P (9/80) x
  obtain ⟨t,ht,hh,_⟩ := phase_horizon_reaches_robust_threshold (n:=N) e H G (P:=P) hent
    (fun z => by simpa only [zero_add,Function.comp_def] using he 0 z)
  have hg : numberedGenerator n x=H.val := numberedGenerator_shell u
  have hd (s : ℕ) (v : ℝ) : pathGateDistance n s x v=orbitCircuitDistance H s v := by
    rw [pathGateDistance,orbitCircuitDistance,hg]
  have hσ : σ≤t := csInf_le (show BddBelow {v : ℝ | 0≤v ∧ (9/80:ℝ)≤pathGateDistance n P x v}
    from ⟨0,fun _ hv => hv.1⟩) ⟨ht.1,hh.trans_eq (hd P t).symm⟩
  obtain ⟨w,hw,hzero⟩ := phase_interval_contains_zero_gate (n:=N) e H σ (σ+G)
    (fun z => by simpa only [Function.comp_def] using he σ z)
  have hw' : crossingWait n P 0 x≤G := (crossingWait_le_iff n P 0 x G).mpr
    ⟨w,hw,(hd 0 w).trans_le ((hasProjectiveCircuitApproximation_iff_infDist _ 0 _).mp hzero)⟩
  exact max_le (hσ.trans ht.2) hw'

#print axioms clock_bounds_first_passage
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.PlateauConfidence
