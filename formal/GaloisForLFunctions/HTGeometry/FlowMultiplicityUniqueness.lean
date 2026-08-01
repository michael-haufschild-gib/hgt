import GaloisForLFunctions.HTGeometry.FlowCharFunUniqueness

/-!
# The multiplicity measure is determined by its trace pairings

On each bounded window the multiplicity measure is finite, so it is determined there by the
integrals of the weight transforms — Fourier inversion for finite measures.  A measure on the
line is determined by its restrictions to the windows, so the trace pairings determine the
multiplicity measure outright.

* `multiplicityMeasure_eq_of_forall_window_cWeightTransform_eq` : the uniqueness statement.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

section Uniqueness

variable {iota kappa : Type*}

/-- **Uniqueness of the multiplicity measure from its trace pairings.**  If every bounded window
carries finitely many spectral points and the weight-transform integrals over every window agree,
the multiplicity measures are equal. -/
theorem multiplicityMeasure_eq_of_forall_window_cWeightTransform_eq
    (lam : iota → ℝ) (mu : kappa → ℝ)
    (hfl : ∀ k : ℕ, {i | lam i ∈ Set.Icc (-(k : ℝ)) k}.Finite)
    (hfm : ∀ k : ℕ, {i | mu i ∈ Set.Icc (-(k : ℝ)) k}.Finite)
    (h : ∀ (k : ℕ) (phi : ℝ → ℂ), Continuous phi → HasCompactSupport phi →
      ∫ l, cWeightTransform phi l
          ∂((multiplicityMeasure lam).restrict (Set.Icc (-(k : ℝ)) k))
        = ∫ l, cWeightTransform phi l
          ∂((multiplicityMeasure mu).restrict (Set.Icc (-(k : ℝ)) k))) :
    multiplicityMeasure lam = multiplicityMeasure mu := by
  refine measure_eq_of_restrict_Icc_eq fun k => ?_
  haveI := multiplicityMeasure_restrict_isFiniteMeasure lam measurableSet_Icc (hfl k)
  haveI := multiplicityMeasure_restrict_isFiniteMeasure mu measurableSet_Icc (hfm k)
  exact measure_eq_of_forall_integral_cWeightTransform_eq _ _ fun phi hcont hsupp =>
    h k phi hcont hsupp

end Uniqueness

end GaloisForLFunctions.HTGeometry
