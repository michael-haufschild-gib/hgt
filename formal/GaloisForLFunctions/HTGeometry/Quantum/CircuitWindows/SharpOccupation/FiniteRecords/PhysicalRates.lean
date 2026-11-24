import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.FullRange.PhysicalRates
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FiniteRecords.Occupation

/-! # Simultaneous occupation and first-record spacing on finite physical windows -/
open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
noncomputable section

/-- At the prescribed operator error, one deterministic observation horizon
gives the sharp occupation exponent and the reciprocal spacing exponent for
records begun at any origin, including the actual first crossing. -/
theorem gaussian_finite_physical_return_rates :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℕ → ℕ, subcriticalBudget s →
      ∀ ε ∈ Ioo (0:ℝ) (Real.sqrt 2), ∀ l b : ℝ, 0 < l → l < physicalArc ε → physicalArc ε < b →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D : ℕ := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
          isSelfAdjoint_pathHamiltonian _⟩
        let G := 2*(2:ℝ)^(D^c)
        ∀ j ≤ s N, ∀ a : ℝ,
          (∀ T ≥ G, l^D < visitFraction H j ε a (a+T) ∧ visitFraction H j ε a (a+T) < b^D) ∧
          ∃ t, records H j ε a t ∧ ∀ i : ℕ, 0 < i → G ≤ t i-a →
            1/b^D < (t i-a)/i ∧ (t i-a)/i < 1/l^D := by
  obtain ⟨c,hc⟩ := gaussian_finite_physical_rates_full
  refine ⟨c,?_⟩
  filter_upwards [hc] with ω hw
  exact fun s hs ε hε => hw s hs ε ⟨hε.1,hε.2.trans (by nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2])⟩

#print axioms gaussian_finite_physical_return_rates
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
