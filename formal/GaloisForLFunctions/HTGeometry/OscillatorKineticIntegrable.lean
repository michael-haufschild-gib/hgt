import GaloisForLFunctions.HTGeometry.OscillatorVirialWindow
import GaloisForLFunctions.HTGeometry.OscillatorBoundaryVanishing
import GaloisForLFunctions.HTGeometry.IntegrableOfBoundedWindows

/-!
# Kinetic energy and second moment of a square-integrable oscillator mode

For a nontrivial square-integrable solution of `v″ = (ξ²−μ)v`, both `v′` and `ξv` are square
integrable.  The windowed virial identity says

`∫_{−n}^{n} v′² + ∫_{−n}^{n} ξ²v² = ∫_{−n}^{n} (Av)² + ∫_{−n}^{n} v² − n(v(n)² + v(−n)²)` ,

and the boundary term is *subtracted with a favourable sign*: it is nonnegative, so it can simply be
dropped.  The first two terms are bounded by the total masses of `(Av)²` and of `v²`, both finite.
So the window masses of `v′² + ξ²v²` are bounded by one constant and the criterion of the previous
file applies.

This is what makes the cross-Wronskian of two modes integrable, hence — being constant — zero.
-/

open Set MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Kinetic energy and second moment are integrable.** -/
theorem integrable_kinetic_add_moment {mu : ℝ} {v v' : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hmu : mu < a ^ 2)
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x)
    (hnt : ∀ y, v y ≠ 0 ∨ v' y ≠ 0)
    (hint : Integrable (fun x => v x ^ 2)) :
    Integrable (fun x => v' x ^ 2 + x ^ 2 * v x ^ 2) := by
  have hcv : Continuous v := continuous_of_hasDerivAt hv
  have hcv' : Continuous v' := continuous_of_hasDerivAt hv'
  have hB := tendsto_oscBoundary_atTop_zero ha hmu hv hv' hnt hint
  have hBneg := tendsto_oscBoundary_atBot_zero ha hmu hv hv' hnt hint
  have hAint : Integrable (fun x => oscLower v v' x ^ 2) :=
    integrable_oscLower_sq hv hv' hB hBneg hint
  have hcA : Continuous fun x => oscLower v v' x ^ 2 := by
    have hc : Continuous fun x => oscLower v v' x := by
      rw [show (fun x => oscLower v v' x) = fun x => v' x + x * v x from rfl]
      exact hcv'.add (continuous_id.mul hcv)
    exact hc.pow 2
  have hck : Continuous fun x : ℝ => v' x ^ 2 + x ^ 2 * v x ^ 2 :=
    (hcv'.pow 2).add ((continuous_pow 2).mul (hcv.pow 2))
  refine integrable_of_bounded_windows hck (fun x => by positivity)
    (C := (∫ x, oscLower v v' x ^ 2) + ∫ x, v x ^ 2) ?_
  intro n
  have hle : -(n : ℝ) ≤ (n : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  -- pass from `Icc` to the interval integral
  have hIcc : (∫ x in Icc (-(n : ℝ)) (n : ℝ), (v' x ^ 2 + x ^ 2 * v x ^ 2))
      = ∫ x in (-(n : ℝ))..(n : ℝ), (v' x ^ 2 + x ^ 2 * v x ^ 2) := by
    rw [intervalIntegral.integral_of_le hle]
    exact MeasureTheory.integral_Icc_eq_integral_Ioc
  -- the virial identity on the window
  have hvir := integral_oscLower_sq_virial hv hcv' (-(n : ℝ)) (n : ℝ)
  have hsplit : (∫ x in (-(n : ℝ))..(n : ℝ), (v' x ^ 2 + x ^ 2 * v x ^ 2))
      = (∫ x in (-(n : ℝ))..(n : ℝ), v' x ^ 2)
        + ∫ x in (-(n : ℝ))..(n : ℝ), x ^ 2 * v x ^ 2 :=
    intervalIntegral.integral_add ((hcv'.pow 2).intervalIntegrable _ _)
      (((continuous_pow 2).mul (hcv.pow 2)).intervalIntegrable _ _)
  -- the boundary term has a favourable sign
  have hbdry : (0 : ℝ) ≤ (n : ℝ) * v (n : ℝ) ^ 2 - (-(n : ℝ)) * v (-(n : ℝ)) ^ 2 := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) * v (n : ℝ) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ (n : ℝ) * v (-(n : ℝ)) ^ 2 := by positivity
    nlinarith [h1, h2]
  -- the two remaining window masses are bounded by the total masses
  have hA : (∫ x in (-(n : ℝ))..(n : ℝ), oscLower v v' x ^ 2) ≤ ∫ x, oscLower v v' x ^ 2 := by
    rw [intervalIntegral.integral_of_le hle]
    exact setIntegral_le_integral hAint (Filter.Eventually.of_forall fun x => sq_nonneg _)
  have hV : (∫ x in (-(n : ℝ))..(n : ℝ), v x ^ 2) ≤ ∫ x, v x ^ 2 := by
    rw [intervalIntegral.integral_of_le hle]
    exact setIntegral_le_integral hint (Filter.Eventually.of_forall fun x => sq_nonneg _)
  rw [hIcc, hsplit]
  linarith [hvir, hbdry, hA, hV]

end GaloisForLFunctions.HTGeometry
