import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.FullRange.FiniteWindows

/-! # Finite observations below the semicircle threshold -/
open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
noncomputable section

/-- Every interval longer than twice the fine recurrence deadline has
the sharp long-time occupation exponent. The same prefix and deadline
work for every origin and every gate budget below the given schedule. -/
theorem gaussian_finite_occupation_exponent :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℕ → ℕ, subcriticalBudget s →
      ∀ x ∈ Ioo (0:ℝ) (1/2), ∀ l b : ℝ, 0 < l → l < x → x < b →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D : ℕ := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
          isSelfAdjoint_pathHamiltonian _⟩
        ∀ j ≤ s N, ∀ a T : ℝ, 2*(2:ℝ)^(D^c) ≤ T →
          l^D < visitFraction H j (zeroGateArcTolerance x) a (a+T) ∧
          visitFraction H j (zeroGateArcTolerance x) a (a+T) < b^D := by
  obtain ⟨c,hc⟩ := gaussian_finite_occupation_full
  refine ⟨c,?_⟩
  filter_upwards [hc] with ω hw
  exact fun s hs x hx => hw s hs x ⟨hx.1,hx.2.trans (by norm_num)⟩

#print axioms gaussian_finite_occupation_exponent
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
