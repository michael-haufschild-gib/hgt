import GaloisForLFunctions.HTGeometry.StrelitzMaximumSlopeGrowth
import GaloisForLFunctions.HTGeometry.EntireHeatHolonomicFiniteSpectrum
import GaloisForLFunctions.HTGeometry.SuperGaussianCentralIndex

/-!
# Exact maximum-slope growth for entire heat evolutions

An everywhere-entire one-sided periodic heat evolution gives super-Gaussian coefficient decay,
hence a sublogarithmic central index.  For an anchor with infinite coefficient support, the exact
right slope of the logarithmic maximum modulus therefore diverges but remains sublinear.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter

noncomputable section

/-- Entire heat evolution and infinite coefficient support force the exact logarithmic maximum
slope to be sublinear. -/
theorem tendsto_strelitzMaximumSlope_div_id_zero_of_entireHeat
    {a : ℕ → ℂ} (ha : EntireCoeffs a)
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ (2 : ℕ)) * (n : ℂ) ^ (2 : ℕ) * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0) :
    Tendsto (fun x : ℝ => strelitzMaximumSlope a x / x) atTop (nhds 0) := by
  obtain ⟨n₀, _, hn₀⟩ := htrans 0
  exact tendsto_strelitzMaximumSlope_div_id_zero_of_centralIndex ha htrans hn₀
    (tendsto_centralIndex_div_log_zero ha
      (fun A hA => EntireHeatHolonomic.exists_superGaussian_bound hheat A hA) hn₀)

/-- Entire heat evolution and infinite coefficient support force the exact logarithmic maximum
slope to diverge while remaining sublinear. -/
theorem strelitzMaximumSlope_growth_of_entireHeat
    {a : ℕ → ℂ} (ha : EntireCoeffs a)
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ (2 : ℕ)) * (n : ℂ) ^ (2 : ℕ) * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0) :
    Tendsto (strelitzMaximumSlope a) atTop atTop ∧
      Tendsto (fun x : ℝ => strelitzMaximumSlope a x / x) atTop (nhds 0) := by
  exact ⟨tendsto_strelitzMaximumSlope_atTop ha htrans,
    tendsto_strelitzMaximumSlope_div_id_zero_of_entireHeat ha hheat htrans⟩

end

end GaloisForLFunctions.HTGeometry
