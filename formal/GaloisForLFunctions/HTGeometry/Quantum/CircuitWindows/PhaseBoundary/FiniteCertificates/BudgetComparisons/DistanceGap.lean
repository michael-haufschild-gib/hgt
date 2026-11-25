import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.BudgetComparisons.AnalyticCoefficients
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.FiniteTransitions

/-! # Ties between physical circuit budgets have locally finite transition dates -/

open Set Metric Matrix Polynomial
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.BudgetComparisons
noncomputable section

/-- A circuit distance satisfies a polynomial relation over analytic functions
of time, even at times where different optimizing circuit layouts exchange roles. -/
theorem algebraic_distance {N : ℕ} (H : selfAdjoint (Square (Bits N))) (s : ℕ) :
    IsAlgebraic coefficients (orbitCircuitDistance H s) := by
  classical
  let d := 2^N-1
  let e : Bits N ≃ Fin (d+1) := (Fintype.equivFin _).trans (finCongr (by
    have hn := Nat.two_pow_pos N
    simp only [Bits,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
    dsimp only [d]; omega))
  let U := relativeOrbit e H
  have rep : MatrixRep atTime U := by
    intro i j
    have h := spectral_entries_analytic e (hermitianEigenbasisUnitary H.2.isHermitian)
      (H.2.isHermitian.eigenvalues ∘ e.symm) 0 i j
    simp only [add_zero] at h
    exact ⟨⟨⟨fun t => (U t i j).re,h.1⟩,fun _ => rfl⟩,⟨⟨fun t => (U t i j).im,h.2⟩,fun _ => rfl⟩⟩
  obtain ⟨T,hn,hroot⟩ := distance_graph_family atTime continuous_coefficient U rep s
  refine ⟨∏ p ∈ T, p,Finset.prod_ne_zero_iff.mpr (fun p hp h => hn (h ▸ hp)),?_⟩
  funext t
  rw [aeval_atTime]
  obtain ⟨p,hp,hval⟩ := hroot t
  change p.eval₂ (atTime t) (Metric.infDist (relativeOrbit e H t) (phaseCircuitMatrixImageAtMost N s))=0 at hval
  rw [infDist_relativeOrbit] at hval
  change (eval₂RingHom (atTime t) (orbitCircuitDistance H s t)) (∏ p∈T, p)=0
  rw [map_prod]
  exact Finset.prod_eq_zero hp hval

/-- On any bounded window, equality of two circuit distances can begin or
end only finitely many times. The two registers, Hamiltonians and budgets
may differ, and the equality can persist on whole intervals. -/
theorem finite_distance_tie_frontier {M N : ℕ} (H : selfAdjoint (Square (Bits M)))
    (K : selfAdjoint (Square (Bits N))) (s j : ℕ) (a b : ℝ) :
    (Icc a b ∩ frontier {t | orbitCircuitDistance H s t=orbitCircuitDistance K j t}).Finite := by
  have hc := (orbitCircuitDistance_lipschitz H s).continuous.sub (orbitCircuitDistance_lipschitz K j).continuous
  have h := finite_zero_frontier hc ((algebraic_distance H s).sub (algebraic_distance K j)) a b
  simpa only [Pi.sub_apply,sub_eq_zero] using h

#print axioms algebraic_distance
#print axioms finite_distance_tie_frontier
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.BudgetComparisons
