import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FiniteRecords.WindowCover
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.FullRange.ForwardWait
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FiniteRecords.Occupation

/-! # First-hit probabilities for origins sampled from a finite physical record -/
open Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
noncomputable section

/-- In every sufficiently long finite record, an affordable date in the
next W time units costs at most W+1 times the single-date exponential
upper bound. The lower bound counts origins already affordable. -/
theorem gaussian_finite_forward_wait :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℕ → ℕ, subcriticalBudget s →
      ∀ ε ∈ Ioo (0:ℝ) (Real.sqrt 2), ∀ l b : ℝ, 0<l → l<physicalArc ε → physicalArc ε<b →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D : ℕ := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
          isSelfAdjoint_pathHamiltonian _⟩
        ∀ j ≤ s N, ∀ a T W : ℝ, 2*(2:ℝ)^(D^c) ≤ T → 0≤W →
          let p := volume.real (windowHits H j ε W ∩ Icc a (a+T))/T
          l^D < p ∧ p ≤ (W+1)*b^D := by
  obtain ⟨c,hc⟩ := gaussian_finite_forward_wait_full
  refine ⟨c,?_⟩
  filter_upwards [hc] with ω hw
  exact fun s hs ε hε => hw s hs ε ⟨hε.1,hε.2.trans (by nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2])⟩

#print axioms gaussian_finite_forward_wait

/-- In each record, only an exponentially small fraction of origins can
return within b⁻ᴰ, for any b above the physical arc width. -/
theorem gaussian_finite_wait_quantile :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℕ → ℕ, subcriticalBudget s →
      ∀ ε ∈ Ioo (0:ℝ) (Real.sqrt 2), ∀ z b : ℝ, physicalArc ε<z → z<b → b<1 →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
          isSelfAdjoint_pathHamiltonian _⟩
        ∀ j ≤ s N, ∀ a T : ℝ, 2*(2:ℝ)^(D^c) ≤ T →
          volume.real (windowHits H j ε (1/b^D) ∩ Icc a (a+T))/T ≤ 2*(z/b)^D := by
  obtain ⟨c,hc⟩ := gaussian_finite_wait_quantile_full
  refine ⟨c,?_⟩
  filter_upwards [hc] with ω hw
  exact fun s hs ε hε => hw s hs ε ⟨hε.1,hε.2.trans (by nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2])⟩

#print axioms gaussian_finite_wait_quantile
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
