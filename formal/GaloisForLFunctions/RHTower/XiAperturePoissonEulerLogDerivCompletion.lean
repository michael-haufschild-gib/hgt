import GaloisForLFunctions.RHTower.XiAperturePoissonValuationClockShuttle
import GaloisForLFunctions.RHTower.PolarPrimeMellinDefect
import GaloisForLFunctions.RHTower.XiRelativeResolventFlux
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Euler completion of the Xi aperture--Poisson current

Complete valuation fusion gives the per-prime Poisson current `a/(p^a-1)`.  Multiplying it by
the prime clock forced by the actual Xi source and summing over primes reconstructs, on `a>1`,
the von Mangoldt L-series and therefore the negative logarithmic derivative of zeta:

`sum_p log(p) * a/(p^a-1) = -a * zeta'(a)/zeta(a)`.

The proof uses the canonical equivalence `(p,e) ↦ p^(e+1)` between prime-valuation clocks and
positive prime powers.  Adding the already canonical archimedean current then identifies the
completed response with `-a * xi'/xi` on the same ray.  Scalar completion is therefore closed;
operator-level continuation and the orbit-selecting quadratic response estimate remain open.
-/

open scoped BigOperators
open ArithmeticFunction

namespace RHTower

noncomputable section

private abbrev vonMangoldtComplexCoeff (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ)

/-- The source-forced prime-clock weighting of the fused Poisson current. -/
def xiAperturePoissonClockedPrimeCurrent
    (a : ℝ) (p : Nat.Primes) : ℂ :=
  (Real.log (p : ℝ) * poissonPrimeValuationFusedHalfDensity a p : ℝ)

private theorem vonMangoldtLSeriesTerm_primePow_eq_clockedDensity
    (a : ℝ) (p : Nat.Primes) (e : ℕ) :
    LSeries.term vonMangoldtComplexCoeff (a : ℂ) ((p : ℕ) ^ (e + 1)) =
      ((Real.log (p : ℝ) *
        Real.exp (-a * xiPrimeValuationLaplaceRate e p) : ℝ) : ℂ) := by
  have hpow : (p : ℕ) ^ (e + 1) ≠ 0 :=
    pow_ne_zero _ p.prop.ne_zero
  rw [LSeries.term_of_ne_zero hpow]
  simp only [vonMangoldtComplexCoeff]
  rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero e),
    ArithmeticFunction.vonMangoldt_apply_prime p.prop]
  have hcast : (((p : ℕ) ^ (e + 1) : ℕ) : ℂ) =
      (((((p : ℕ) ^ (e + 1) : ℕ) : ℝ)) : ℂ) := by
    norm_num
  rw [hcast]
  rw [← Complex.ofReal_cpow
    (by positivity : 0 ≤ ((((p : ℕ) ^ (e + 1) : ℕ) : ℝ))) a]
  norm_cast
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [Real.rpow_def_of_pos (by positivity :
    0 < ((((p : ℕ) ^ (e + 1) : ℕ) : ℝ))),
    Nat.cast_pow, Real.log_pow]
  unfold xiPrimeValuationLaplaceRate
  rw [div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  push_cast
  ring

private theorem vonMangoldtLSeriesTerm_support_primePowers (a : ℝ) :
    Function.support (LSeries.term vonMangoldtComplexCoeff (a : ℂ)) ⊆
      {n : ℕ | IsPrimePow n} := by
  intro n hn
  by_contra hpow
  apply hn
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn0]
    simp only [vonMangoldtComplexCoeff]
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow]
    simp

/-- On the absolute-convergence ray, the clocked, fully valuation-fused Poisson current
reconstructs the actual von Mangoldt channel after prime assembly. -/
theorem tsum_xiAperturePoissonClockedPrimeCurrent_eq_zetaLogDeriv
    {a : ℝ} (ha : 1 < a) :
    (∑' p : Nat.Primes, xiAperturePoissonClockedPrimeCurrent a p) =
      (a : ℂ) * vonMangoldtPrimeLaplaceChannel (a - 1) := by
  have hsum : Summable (LSeries.term vonMangoldtComplexCoeff (a : ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using ha)
  rw [vonMangoldtPrimeLaplaceChannel]
  have harg : ((((a - 1) + 1 : ℝ) : ℂ)) = (a : ℂ) := by
    push_cast
    ring
  rw [harg, LSeries,
    tsum_eq_tsum_primes_of_support_subset_prime_powers hsum
      (vonMangoldtLSeriesTerm_support_primePowers a),
    ← tsum_mul_left]
  apply tsum_congr
  intro p
  rw [← tsum_mul_left]
  rw [xiAperturePoissonClockedPrimeCurrent]
  push_cast
  rw [poissonPrimeValuationFusedHalfDensity, Complex.ofReal_tsum]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro e
  rw [vonMangoldtLSeriesTerm_primePow_eq_clockedDensity]
  unfold poissonSpectralHalfDensity
  push_cast
  ring

/-- Prime completion of the fused current is exactly the Euler-region logarithmic derivative of
zeta, with the aperture Euler factor and no residual prime term. -/
theorem tsum_xiAperturePoissonClockedPrimeCurrent_eq_neg_zeta_deriv_div
    {a : ℝ} (ha : 1 < a) :
    (∑' p : Nat.Primes, xiAperturePoissonClockedPrimeCurrent a p) =
      -(a : ℂ) * deriv riemannZeta (a : ℂ) / riemannZeta (a : ℂ) := by
  rw [tsum_xiAperturePoissonClockedPrimeCurrent_eq_zetaLogDeriv ha,
    vonMangoldtPrimeLaplaceChannel_eq_logDeriv (by linarith : 0 < a - 1)]
  push_cast
  ring

/-- The scalar response current after the canonical archimedean completion.  The factor `a`
multiplies both the prime current and the Gamma/boundary current because it is the aperture clock
already forced by valuation fusion. -/
def xiAperturePoissonCompletedCurrent (a : ℝ) : ℂ :=
  (∑' p : Nat.Primes, xiAperturePoissonClockedPrimeCurrent a p) -
    (a : ℂ) * logDeriv archFactor (a : ℂ)

/-- On the Euler ray, completing the response-derived prime current by the fixed archimedean
current gives exactly `a` times the canonical completed Xi flux.  There is no residual term. -/
theorem xiAperturePoissonCompletedCurrent_eq_seamFluxCochain
    {a : ℝ} (ha : 1 < a) :
    xiAperturePoissonCompletedCurrent a =
      (a : ℂ) * seamFluxCochain (a : ℂ) := by
  have hs : 1 < ((a : ℂ).re) := by simpa using ha
  rw [xiAperturePoissonCompletedCurrent,
    tsum_xiAperturePoissonClockedPrimeCurrent_eq_neg_zeta_deriv_div ha,
    seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re hs,
    infinitePrimeFlux]
  simp only [logDeriv_apply]
  ring

/-- Equivalently, the completed response current is the actual Xi logarithmic derivative on the
absolute-convergence ray. -/
theorem xiAperturePoissonCompletedCurrent_eq_neg_xi_logDeriv
    {a : ℝ} (ha : 1 < a) :
    xiAperturePoissonCompletedCurrent a =
      -(a : ℂ) * logDeriv xi (a : ℂ) := by
  rw [xiAperturePoissonCompletedCurrent_eq_seamFluxCochain ha, seamFluxCochain]
  ring

end

end RHTower
