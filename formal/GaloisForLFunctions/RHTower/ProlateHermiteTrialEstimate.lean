import GaloisForLFunctions.RHTower.ProlateHermiteTrialFamily

/-!
# The bandwidth-uniform split of the Hermite trial pairing

At the Hermite scale the pairwise prolate Rayleigh numerator of two rescaled Hermite trial
functions splits into

`√c · N_{mn}(c) = −c(2m+1)·∫_{−√c}^{√c} φ_mφ_n  +  ∫_{−√c}^{√c} (correction)` ,

and the correction integral is bounded by a constant that does not move with the bandwidth,
because its integrand is a polynomial times `e^{−ξ²}`.  So the rung term dominates: the whole
bandwidth dependence of the pairing is the single explicit factor `c`.
-/

open Filter Topology Set MeasureTheory

noncomputable section

namespace RHTower

/-- The bounded correction in the Hermite-scale pairing. -/
def hermiteCorrectionIntegrand (m n : ℕ) (xi : ℝ) : ℝ :=
  ((2 * (m : ℝ) + 1) * xi ^ (2 : ℕ) - xi ^ (4 : ℕ)) * (hermiteFun m xi * hermiteFun n xi)
    - 2 * xi * (deriv (hermiteFun m) xi * hermiteFun n xi)

theorem hermiteCorrectionIntegrand_eq (m n : ℕ) :
    hermiteCorrectionIntegrand m n = fun xi =>
      ((2 * (m : ℝ) + 1) * xi ^ (2 : ℕ) - xi ^ (4 : ℕ)) * (hermiteFun m xi * hermiteFun n xi)
        - 2 * xi * (deriv (hermiteFun m) xi * hermiteFun n xi) := rfl

theorem continuous_hermiteCorrectionIntegrand (m n : ℕ) :
    Continuous (hermiteCorrectionIntegrand m n) := by
  rw [hermiteCorrectionIntegrand_eq]
  have h1 := continuous_hermiteFun m
  have h2 := continuous_hermiteFun n
  have h3 := continuous_deriv_hermiteFun m
  fun_prop

/-- **The correction is uniformly bounded.**  Its integrand is a polynomial times `e^{−ξ²}`, so all
its truncated integrals are bounded by a single constant. -/
theorem exists_bound_hermiteCorrection (m n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : ℝ, |∫ xi in u..v, hermiteCorrectionIntegrand m n xi| ≤ C := by
  obtain ⟨p, hp⟩ := exists_poly_hermiteFun m
  obtain ⟨q, hq⟩ := exists_poly_hermiteFun n
  obtain ⟨pd, hpd⟩ := exists_poly_deriv_hermiteFun m
  refine exists_uniform_bound_of_gaussEnvelope
    ((Polynomial.C (2 * (m : ℝ) + 1) * Polynomial.X ^ (2 : ℕ) - Polynomial.X ^ (4 : ℕ)) * p * q
      - Polynomial.C (2 : ℝ) * Polynomial.X * pd * q) (by norm_num : (0 : ℝ) < 1) ?_
  intro x
  rw [hermiteCorrectionIntegrand, hp x, hq x, hpd x]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  rw [show Real.exp (-(1 * x ^ (2 : ℕ)))
      = Real.exp (-(1 / 2 * x ^ (2 : ℕ))) * Real.exp (-(1 / 2 * x ^ (2 : ℕ))) by
    rw [← Real.exp_add]; congr 1; ring]
  ring

/-- **The bandwidth split of the pairwise numerator.**  The rung term carries the factor `c`; the
rest is the uniformly bounded correction. -/
theorem sqrt_mul_integral_trialPair_numerator {c : ℝ} (hc : 0 < c) (m n : ℕ) :
    Real.sqrt c * (∫ x in (-1 : ℝ)..1,
        ((1 - x ^ (2 : ℕ)) * prolateHermiteTrialDeriv2 c m x
          - 2 * x * prolateHermiteTrialDeriv c m x
          - c ^ (2 : ℕ) * x ^ (2 : ℕ) * prolateHermiteTrial c m x) * prolateHermiteTrial c n x)
      = -(c * (2 * (m : ℝ) + 1))
          * (∫ xi in (-Real.sqrt c)..(Real.sqrt c), hermiteFun m xi * hermiteFun n xi)
        + ∫ xi in (-Real.sqrt c)..(Real.sqrt c), hermiteCorrectionIntegrand m n xi := by
  have hs : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  rw [integral_trialPair_numerator hc]
  have hsplit : (∫ xi in (-Real.sqrt c)..(Real.sqrt c),
        ((-(c * (2 * (m : ℝ) + 1)) + (2 * (m : ℝ) + 1) * xi ^ (2 : ℕ) - xi ^ (4 : ℕ))
            * (hermiteFun m xi * hermiteFun n xi)
          - 2 * xi * (deriv (hermiteFun m) xi * hermiteFun n xi)))
      = -(c * (2 * (m : ℝ) + 1))
          * (∫ xi in (-Real.sqrt c)..(Real.sqrt c), hermiteFun m xi * hermiteFun n xi)
        + ∫ xi in (-Real.sqrt c)..(Real.sqrt c), hermiteCorrectionIntegrand m n xi := by
    have hint1 : IntervalIntegrable
        (fun xi => -(c * (2 * (m : ℝ) + 1)) * (hermiteFun m xi * hermiteFun n xi))
        volume (-Real.sqrt c) (Real.sqrt c) := by
      apply Continuous.intervalIntegrable
      have h1 := continuous_hermiteFun m
      have h2 := continuous_hermiteFun n
      fun_prop
    have hint2 : IntervalIntegrable (hermiteCorrectionIntegrand m n)
        volume (-Real.sqrt c) (Real.sqrt c) :=
      (continuous_hermiteCorrectionIntegrand m n).intervalIntegrable _ _
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hint1 hint2]
    refine intervalIntegral.integral_congr fun xi _ => ?_
    rw [hermiteCorrectionIntegrand]
    ring
  rw [hsplit]
  field_simp

end RHTower
