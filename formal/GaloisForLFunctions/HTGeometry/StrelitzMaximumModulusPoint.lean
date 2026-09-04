import GaloisForLFunctions.HTGeometry.StrelitzHeatLeadingDecay
import GaloisForLFunctions.HTGeometry.CircleMaximumExistence

/-!
# Maximum-modulus points in Strelitz logarithmic coordinates

Every positive circle has a maximum-modulus point.  A nonzero Taylor coefficient makes the value
there nonzero, and angular criticality says its Euler logarithmic derivative is real.  This packages
the exact maximum-modulus locus used by the global Strelitz branch argument.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℕ → ℂ}

/-- **Maximum-modulus Strelitz point.** The selected value dominates the maximum term, is nonzero,
and has real Euler logarithmic derivative. -/
theorem exists_maximumPoint_real_eulerLogDeriv
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {r : ℝ} (hr : 0 < r) :
    ∃ z : ℂ, ‖z‖ = r ∧
      maxTerm a r ≤ ‖coeffFun a z‖ ∧
      coeffFun a z ≠ 0 ∧
      (eulerLogDeriv (coeffFun a) z).im = 0 := by
  obtain ⟨z, hz, hmax⟩ := exists_max_on_circle ha hr
  have hfloor := maxTerm_le_norm_of_max_on_circle ha hr hz hmax
  have hfz : coeffFun a z ≠ 0 := by
    have hmu : 0 < maxTerm a r := maxTerm_pos ha hr hn₀
    exact norm_pos_iff.mp (lt_of_lt_of_le hmu hfloor)
  exact ⟨z, hz, hfloor, hfz, by
    simpa [eulerLogDeriv] using
      im_mul_deriv_div_eq_zero_of_max_on_circle ha hr hz hfz hmax⟩

end

end GaloisForLFunctions.HTGeometry
