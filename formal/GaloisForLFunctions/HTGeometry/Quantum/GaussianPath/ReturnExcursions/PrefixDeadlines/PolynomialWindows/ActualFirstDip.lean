import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.VisitWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrefixDeadlines.HaarWindows.ScalarFloor

/-! # A physical first-dip deadline from polynomial gaps between scalar visits -/

open Real Filter MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines.PolynomialWindows
open SharpOccupation
noncomputable section

/-- Before an arbitrary origin the accumulated scalar time is bounded
by the number of polynomial windows, each with inverse-size scalar
residence. It bounds the absolute date of the next visit at every budget. -/
theorem gaussian_first_date_deadline :
    ∃ A>0, ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let H := FirstAscent.ThermodynamicEdges.shellOperator (pathPauliDisorderShell ω n)
      let T := δ*K/(log K)^2
      let p := zeroGateArcDensity (2^(n+2)) (physicalArc (1/10)/2)
      ∀ a≥(0:ℝ), ∀ s : ℕ, p*PrecisionReturns.firstVisit H a s (1/10)≤(1+a/T)*(A/K) := by
  obtain ⟨κ,hκ,A,hA,δ,hδ,h⟩ := BlockDilations.gaussian_polynomial_occupation
  refine ⟨A,hA,δ,hδ,?_⟩
  filter_upwards [h] with ω hω
  filter_upwards [hω] with n hn
  intro K H T p a ha s
  have hmass := hn 0 (by simp only [Nat.cast_zero]; exact mul_nonneg hκ.le (Nat.cast_nonneg _)) 0 a ha
  rw [zero_add] at hmass
  exact (HaarWindows.static_scalar_deadline H (by norm_num : (1/10:ℝ)∈Ioo (0:ℝ) 2) s a ha).trans hmass

/-- Apply the deadline to the first 9/80 crossing from identity itself,
simultaneously for all subsequent 1/10 gate budgets on the same draw. -/
theorem gaussian_first_dip_deadline :
    ∃ A>0, ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let x := fun i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
      let σ := PrescribedTimes.crossingOrigin n (nearHilbertContinuousCircuitBudget (n+2)) (9/80) x
      let T := δ*K/(log K)^2
      let p := zeroGateArcDensity (2^(n+2)) (physicalArc (1/10)/2)
      ∀ s, p*RepeatedGates.PhysicalBlocks.firstLowAfterCrossing ω n s≤(1+σ/T)*(A/K) := by
  obtain ⟨A,hA,δ,hδ,h⟩ := gaussian_first_date_deadline
  refine ⟨A,hA,δ,hδ,?_⟩
  filter_upwards [h] with ω hω
  filter_upwards [hω] with n hn
  intro K x σ T p s
  have hσ : 0≤σ := Real.sInf_nonneg fun _ h => h.1
  exact hn σ hσ s

#print axioms gaussian_first_date_deadline
#print axioms gaussian_first_dip_deadline
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines.PolynomialWindows
