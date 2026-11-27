import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.IncrementMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.BoxTransfer

/-! # Uniform Gaussian cost of the first excursion with strong bonds -/
open Filter MeasureTheory ProbabilityTheory Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open PrescribedTimes WeakBonds.SingleCut
noncomputable section

/-- Every sufficiently large prefix has joint survival mass at least
exp(−CK²)/T⁷, with an absolute constant and every ZZ coupling above
one half. The dates are the original first crossing and first waits. -/
theorem uniform_strong_bond_survival :
    ∃ C > (0:ℝ), ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      let μ := Measure.pi (fun _ : PrefixIndex n => gaussianReal 0 1)
      ∀ T ≥ (1:ℝ), exp (-C*(K:ℝ)^2) ≤ T^7*μ.real {x |
        (∀ e : Fin (n+1), 1/2 < x ((pathCoeffEquiv n).symm (.inr (e,(2,2))))) ∧
        T < crossingOrigin n P (9/80) x ∧ ∀ s ≤ P/2, T < crossingWait n P s x} := by
  obtain ⟨C,hC,hbox⟩ := gaussian_central_increment_box
  refine ⟨C,hC,?_⟩
  filter_upwards [hbox,transfer_increment_sector] with k hb hpass
  intro n K P μ T hT
  obtain ⟨B,E,hB,hE,hfloor,hw⟩ := hb T hT
  let Q := {x : PrefixIndex n→ℝ | ∀ e : Fin (n+1), 1/2 < x ((pathCoeffEquiv n).symm (.inr (e,(2,2))))}
  have hQ : MeasurableSet Q := by
    simp only [Q,setOf_forall]
    exact MeasurableSet.iInter fun _ => measurableSet_lt measurable_const (measurable_pi_apply _)
  apply hfloor.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hT) _)
  apply hpass E Q hE hQ T (zero_lt_one.trans_le hT) B hB
  intro x hx
  obtain ⟨hdiag,_,hinc⟩ := hw x hx
  refine ⟨fun e => ?_,hinc⟩
  change 1/2 < x ((pathCoeffEquiv n) ((pathCoeffEquiv n).symm (.inr (e,(2,2)))))
  rw [Equiv.apply_symm_apply]
  exact hdiag _ rfl

#print axioms uniform_strong_bond_survival
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
