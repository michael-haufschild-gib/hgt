import GaloisForLFunctions.RHTower.Sieve.RamarePhaseBilinear

/-!
# The damped cofactor as an average of undamped ones

`Sieve/OmegaBudgetLadderTail` consumes a *saving* on the cofactor polynomial of the plain Möbius
coefficient — a bound strictly better than the trivial `#C` — and `Sieve/CofactorLowFreqBound`
supplies it from the zero-free region.  The exact Ramaré identity produces the damped coefficient
`μ(m)/(ω_P(m)+1)` instead, for which no such saving exists in the corpus.

`1/(k+1) = ∫₀¹ t^k dt` writes the damped cofactor polynomial as an average over `t ∈ [0,1]` of
polynomials with the multiplicative weight `t^{ω_P(m)}`.  A saving uniform in `t` therefore transfers
to the damped polynomial, which reduces the missing analytic input to one perturbed Euler product:
the Dirichlet series of `μ(m)·t^{ω_P(m)}` is `(1/ζ(s))·∏_{p ∈ P}(1 − t·p^{-s})/(1 − p^{-s})`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- The Möbius coefficient damped by a power of `t` for each designated prime factor. -/
def dampedOmegaMoebius (P : Finset ℕ) (t : ℝ) (m : ℕ) : ℂ :=
  ((moebius m : ℤ) : ℂ) * ((t ^ (primeFactorsIn P m).card : ℝ) : ℂ)

theorem norm_dampedOmegaMoebius_le_one {P : Finset ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (m : ℕ) : ‖dampedOmegaMoebius P t m‖ ≤ 1 := by
  rw [dampedOmegaMoebius, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hpow : |t ^ (primeFactorsIn P m).card| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_one₀ ht0 ht1
  have hmu : ‖((moebius m : ℤ) : ℂ)‖ ≤ 1 := by
    have := abs_moebius_real_le_one m
    rw [show ((moebius m : ℤ) : ℂ) = (((moebius m : ℤ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    exact this
  have hnn : (0 : ℝ) ≤ ‖((moebius m : ℤ) : ℂ)‖ := norm_nonneg _
  nlinarith [hmu, hpow, hnn, abs_nonneg (t ^ (primeFactorsIn P m).card)]

/-- **The damped cofactor polynomial is an average of undamped ones.** -/
theorem logPoly_ramareCofactorCoeff_eq_integral (P C : Finset ℕ) (w : ℝ) :
    logPoly (ramareCofactorCoeff P) C w
      = ∫ t in (0 : ℝ)..1, logPoly (dampedOmegaMoebius P t) C w := by
  classical
  have hterm : ∀ m : ℕ, IntervalIntegrable
      (fun t : ℝ => dampedOmegaMoebius P t m
        * Complex.exp (((2 * Real.pi * (w * Real.log m) : ℝ) : ℂ) * Complex.I))
      MeasureTheory.volume 0 1 := by
    intro m
    refine Continuous.intervalIntegrable ?_ _ _
    refine Continuous.mul ?_ continuous_const
    have hfun : (fun t : ℝ => dampedOmegaMoebius P t m)
        = fun t : ℝ => ((moebius m : ℤ) : ℂ)
            * ((t ^ (primeFactorsIn P m).card : ℝ) : ℂ) := rfl
    rw [hfun]
    exact continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_pow ((primeFactorsIn P m).card)))
  have hswap : (∫ t in (0 : ℝ)..1, logPoly (dampedOmegaMoebius P t) C w)
      = ∑ m ∈ C, ∫ t in (0 : ℝ)..1, dampedOmegaMoebius P t m
          * Complex.exp (((2 * Real.pi * (w * Real.log m) : ℝ) : ℂ) * Complex.I) := by
    rw [show (fun t : ℝ => logPoly (dampedOmegaMoebius P t) C w)
        = (fun t : ℝ => ∑ m ∈ C, dampedOmegaMoebius P t m
            * Complex.exp (((2 * Real.pi * (w * Real.log m) : ℝ) : ℂ) * Complex.I)) from rfl]
    exact intervalIntegral.integral_finsetSum (fun m _ => hterm m)
  rw [hswap, logPoly]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hfun : (fun t : ℝ => dampedOmegaMoebius P t m
        * Complex.exp (((2 * Real.pi * (w * Real.log m) : ℝ) : ℂ) * Complex.I))
      = (fun t : ℝ => (((moebius m : ℤ) : ℂ)
          * Complex.exp (((2 * Real.pi * (w * Real.log m) : ℝ) : ℂ) * Complex.I))
          * (((t ^ (primeFactorsIn P m).card : ℝ)) : ℂ)) := by
    funext t
    simp only [dampedOmegaMoebius]
    ring
  have hpow : (∫ t in (0 : ℝ)..1, (t : ℝ) ^ (primeFactorsIn P m).card)
      = 1 / (((primeFactorsIn P m).card : ℝ) + 1) := by
    rw [integral_pow]
    norm_num
  rw [hfun, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, hpow,
    ramareCofactorCoeff]
  push_cast
  ring

end

end RHTower.Sieve
