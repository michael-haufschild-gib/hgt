import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.MeasurableTest

/-! # Gaussian dilation tests for prescribed observation dates -/
open Set Filter MeasureTheory
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes
noncomputable section

/-- Every prescribed sequence of finite grid tests has summable failure
probability on the actual prefixes, even though those prefixes overlap. -/
theorem gaussian_path_eventually_outside_dilation_test
    (t b : ℕ → ℝ) (s q : ℕ → ℕ) (hq : ∀ k, 0 < q k) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      x ∉ testedDilationEvent (rayGrid (q k)) ((2:ℝ)^(2^(k+3)/1024))
        (prescribedWindowEvent (k+1) (s k) (t k) (b k)) :=
  gaussian_path_eventually_outside_measurable_test
    (fun k => prescribedWindowEvent (k+1) (s k) (t k) (b k))
    (fun _ => measurable_prescribedWindowEvent _ _ _ _) q hq

#print axioms gaussian_path_eventually_outside_dilation_test
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes
