import GaloisForLFunctions.RHTower.Sieve.TrigNormSqDeriv

/-!
# Gallagher's bound at a point of a trigonometric polynomial

Applying the Sobolev bound to `f = |S|²` on the window of length `δ` centred at `a`, and bounding
`(|S|²)'` by `2|S||S'|`, gives

`|S(a)|² ≤ δ^{-1} ∫_{a-δ/2}^{a+δ/2} |S|² + ∫_{a-δ/2}^{a+δ/2} 2|S||S'|`.

Every ingredient is continuous, so the integrals exist without further hypotheses.  The windows
around `δ`-separated points are disjoint, which is what turns this local bound into the sharp large
sieve; that assembly is the remaining step.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- **Gallagher's bound at a point.** -/
theorem gallagher_at_point (N : ℕ) (c : Fin N → ℂ) (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ‖expSum N c a‖ ^ 2
      ≤ (1 / δ) * (∫ t in (a - δ / 2)..(a + δ / 2), ‖expSum N c t‖ ^ 2)
        + (∫ t in (a - δ / 2)..(a + δ / 2),
            2 * ‖expSum N c t‖ * ‖expSum N (derivCoeff N c) t‖) := by
  have hh : (0 : ℝ) < δ / 2 := by linarith
  have hab : a - δ / 2 ≤ a + δ / 2 := by linarith
  -- the derivative of the squared modulus, as a continuous function
  have hcontg : Continuous (fun s : ℝ =>
      (inner ℝ (expSum N c s) (expSum N (derivCoeff N c) s) : ℝ)
        + (inner ℝ (expSum N (derivCoeff N c) s) (expSum N c s) : ℝ)) :=
    (Continuous.inner (𝕜 := ℝ) (continuous_expSum N c)
        (continuous_expSum N (derivCoeff N c))).add
      (Continuous.inner (𝕜 := ℝ) (continuous_expSum N (derivCoeff N c)) (continuous_expSum N c))
  have hbase := gallagher_sobolev (f := fun s => ‖expSum N c s‖ ^ 2)
    (f' := fun s => (inner ℝ (expSum N c s) (expSum N (derivCoeff N c) s) : ℝ)
      + (inner ℝ (expSum N (derivCoeff N c) s) (expSum N c s) : ℝ))
    (a := a) (h := δ / 2) hh (fun x _ => hasDerivAt_normSq_expSum N c x) hcontg.continuousOn
  -- the squared modulus is its own absolute value
  have habs1 : (∫ t in (a - δ / 2)..(a + δ / 2), |‖expSum N c t‖ ^ 2|)
      = ∫ t in (a - δ / 2)..(a + δ / 2), ‖expSum N c t‖ ^ 2 :=
    intervalIntegral.integral_congr (fun t _ => abs_of_nonneg (sq_nonneg _))
  have habs0 : |‖expSum N c a‖ ^ 2| = ‖expSum N c a‖ ^ 2 := abs_of_nonneg (sq_nonneg _)
  -- Cauchy–Schwarz on the derivative term
  have hderivbound : (∫ t in (a - δ / 2)..(a + δ / 2),
        |(inner ℝ (expSum N c t) (expSum N (derivCoeff N c) t) : ℝ)
          + (inner ℝ (expSum N (derivCoeff N c) t) (expSum N c t) : ℝ)|)
      ≤ ∫ t in (a - δ / 2)..(a + δ / 2),
          2 * ‖expSum N c t‖ * ‖expSum N (derivCoeff N c) t‖ := by
    refine intervalIntegral.integral_mono_on hab
      (hcontg.abs.intervalIntegrable _ _) ?_ (fun t _ => abs_deriv_normSq_le N c t)
    exact (((continuous_const.mul (continuous_expSum N c).norm).mul
      (continuous_expSum N (derivCoeff N c)).norm)).intervalIntegrable _ _
  -- the window length
  have hlen : (1 : ℝ) / (2 * (δ / 2)) = 1 / δ := by
    congr 1
    ring
  rw [habs0, habs1, hlen] at hbase
  linarith

end RHTower.Sieve
