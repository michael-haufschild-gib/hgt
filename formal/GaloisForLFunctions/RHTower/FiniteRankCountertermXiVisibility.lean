import GaloisForLFunctions.HTGeometry.FiniteRankCountertermKernelVisibility
import GaloisForLFunctions.RHTower.XiWeilPositivityCriterion

/-!
# Finite-rank counterterm Xi visibility

If a finite real quadratic correction vanishes on every off-real Xi sign test, repaired
Xi-Weil diagonal positivity still implies RH.  This is the exact closed bridge available
without assuming the unresolved reciprocal-carrier or density construction.
-/

namespace RHTower

open Complex

noncomputable section

/-- If a finite quadratic correction vanishes on every off-real Xi sign test, then positivity of
the repaired Xi-Weil diagonal form still forces RH. -/
theorem riemannHypothesis_of_repairedXiWeil_nonneg_of_signTests_in_ker
    {r : ℕ} (L : (ℂ → ℂ) →ₗ[ℝ] (Fin r → ℝ)) (B : QuadraticForm ℝ (Fin r → ℝ))
    (hpos : ∀ F : ℂ → ℂ, XiWeilSquareSummable F →
      0 ≤ (xiWeilPolarization F F).re + B (L F))
    (hker : ∀ q : XiZeroCopy, L (xiOffRealSignTest (xiSpectralPoint q)) = 0) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  by_cases hreal : (starRingEnd ℂ) (xiSpectralPoint q) = xiSpectralPoint q
  · exact ⟨(xiSpectralPoint q).re,
      (Complex.conj_eq_iff_re.mp hreal).symm⟩
  · have hqpos := hpos (xiOffRealSignTest (xiSpectralPoint q))
      (xiOffRealSignTest_squareSummable (xiSpectralPoint q))
    rw [hker q, QuadraticMap.map_zero, add_zero] at hqpos
    exact False.elim ((not_lt_of_ge hqpos)
      (xiWeilPolarization_offRealSignTest_re_neg q hreal))

end

end RHTower

