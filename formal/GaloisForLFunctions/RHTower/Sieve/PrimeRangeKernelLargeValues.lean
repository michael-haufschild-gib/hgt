import GaloisForLFunctions.RHTower.Sieve.SupportKernelLargeValues
import GaloisForLFunctions.RHTower.Sieve.PrimeBlockTwistBound

/-!
# Halász's inequality for prime-supported coefficients

The Gram kernel of a prime range is the twisted prime sum `∑_{lo < p ≤ hi} p^{2πiv}`, which the
Route-T envelope bounds by a quantity carrying the zero-free saving
`x^{−w(τ)/3}`, `w(τ) ≍ (log|τ|)^{−9/10}`.  Substituting it into the finite-frequency
Halász–Montgomery bound of `Sieve/SupportKernelLargeValues` gives the prime version of Halász's
inequality: the diagonal is the number of primes in the range, and the off-diagonal price is the
number of frequencies times the twisted prime sum bound.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The prime polynomial is minus the sum of the phases over the range. -/
theorem primeBlockPoly_eq_neg_sum_unitLogPhase {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) (w : ℝ) :
    primeBlockPoly B w = -∑ p ∈ B, unitLogPhase w p := by
  rw [primeBlockPoly, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [moebiusPhase, ArithmeticFunction.moebius_apply_prime (hB p hp)]
  push_cast
  ring

/-- The exponential sum over a prime range has the same modulus as the prime polynomial. -/
theorem norm_sum_unitLogPhase_eq {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) (w : ℝ) :
    ‖∑ p ∈ B, unitLogPhase w p‖ = ‖primeBlockPoly B w‖ := by
  rw [primeBlockPoly_eq_neg_sum_unitLogPhase hB, norm_neg]

/-- The Route-T bound for the Gram kernel of a prime range. -/
def routeTPrimeKernel (A delta C : ℝ) (lo hi : ℕ) (v : ℝ) : ℝ :=
  (routeTTwistEnvelope A delta C (-(2 * Real.pi * v)) (max (hi : ℝ) 1) + 7 * Real.exp 9)
      * (1 / Real.log 2 + 1 / Real.log ((hi + 1 : ℕ) : ℝ))
    + (routeTTwistEnvelope A delta C (-(2 * Real.pi * v)) (max (lo : ℝ) 1) + 7 * Real.exp 9)
      * (1 / Real.log 2 + 1 / Real.log ((lo + 1 : ℕ) : ℝ))

theorem routeTPrimeKernel_nonneg {A delta C : ℝ} (hC : 0 ≤ C) (lo hi : ℕ) (v : ℝ) :
    0 ≤ routeTPrimeKernel A delta C lo hi v := by
  have hE1 : 0 ≤ routeTTwistEnvelope A delta C (-(2 * Real.pi * v)) (max (hi : ℝ) 1) :=
    routeTTwistEnvelope_nonneg hC (le_max_right _ _)
  have hE2 : 0 ≤ routeTTwistEnvelope A delta C (-(2 * Real.pi * v)) (max (lo : ℝ) 1) :=
    routeTTwistEnvelope_nonneg hC (le_max_right _ _)
  have h9 : (0 : ℝ) ≤ 7 * Real.exp 9 := by positivity
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hf1 : (0 : ℝ) ≤ 1 / Real.log 2 + 1 / Real.log ((hi + 1 : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ Real.log ((hi + 1 : ℕ) : ℝ) := by
      refine Real.log_nonneg ?_
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.succ_ne_zero hi)
    positivity
  have hf2 : (0 : ℝ) ≤ 1 / Real.log 2 + 1 / Real.log ((lo + 1 : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ Real.log ((lo + 1 : ℕ) : ℝ) := by
      refine Real.log_nonneg ?_
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.succ_ne_zero lo)
    positivity
  rw [routeTPrimeKernel]
  have h1 : (0 : ℝ) ≤ (routeTTwistEnvelope A delta C (-(2 * Real.pi * v)) (max (hi : ℝ) 1)
      + 7 * Real.exp 9) * (1 / Real.log 2 + 1 / Real.log ((hi + 1 : ℕ) : ℝ)) :=
    mul_nonneg (by linarith) hf1
  have h2 : (0 : ℝ) ≤ (routeTTwistEnvelope A delta C (-(2 * Real.pi * v)) (max (lo : ℝ) 1)
      + 7 * Real.exp 9) * (1 / Real.log 2 + 1 / Real.log ((lo + 1 : ℕ) : ℝ)) :=
    mul_nonneg (by linarith) hf2
  linarith

/-- **The Gram kernel of a prime range obeys the Route-T envelope.** -/
theorem exists_norm_sum_unitLogPhase_primeRange_le :
    ∃ A delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (B : Finset ℕ) (lo hi : ℕ), lo ≤ hi →
        (∀ p, p ∈ B ↔ (p.Prime ∧ lo < p ∧ p ≤ hi)) →
        ∀ v : ℝ, ‖∑ p ∈ B, unitLogPhase v p‖ ≤ routeTPrimeKernel A delta C lo hi v := by
  obtain ⟨A, delta, C, hdelta, hC, hbound⟩ := exists_norm_primeBlockPoly_routeT_le
  refine ⟨A, delta, C, hdelta, hC, ?_⟩
  intro B lo hi hle hB v
  have hprime : ∀ p ∈ B, p.Prime := fun p hp => ((hB p).1 hp).1
  rw [norm_sum_unitLogPhase_eq hprime]
  exact hbound B lo hi hle hB v

/-- **Halász's inequality for prime-supported coefficients.**  For a Dirichlet polynomial supported
on the primes of `(lo, hi]` and any finite frequency set `T` whose nonzero differences all obey the
kernel bound `E`, the discrete mean square is at most `(#B + E·#T)` times the coefficient energy.
The diagonal `#B` is the number of primes in the range — smaller than the length of the polynomial
by a factor `log hi` — and `E` is supplied by the Route-T twisted prime sum. -/
theorem exists_sum_normSq_logPoly_primeRange_le :
    ∃ A delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (a : ℕ → ℂ) (B : Finset ℕ) (lo hi : ℕ) (T : Finset ℝ) (E : ℝ),
        lo ≤ hi → (∀ p, p ∈ B ↔ (p.Prime ∧ lo < p ∧ p ≤ hi)) → 0 ≤ E →
        (∀ u ∈ T, ∀ v ∈ T, u ≠ v → routeTPrimeKernel A delta C lo hi (u - v) ≤ E) →
        ∑ w ∈ T, ‖logPoly a B w‖ ^ (2 : ℕ)
          ≤ ((B.card : ℝ) + E * (T.card : ℝ)) * ∑ p ∈ B, ‖a p‖ ^ (2 : ℕ) := by
  obtain ⟨A, delta, C, hdelta, hC, hker⟩ := exists_norm_sum_unitLogPhase_primeRange_le
  refine ⟨A, delta, C, hdelta, hC, ?_⟩
  intro a B lo hi T E hle hB hE0 hE
  refine sum_normSq_logPoly_le_of_kernelBound a hE0 ?_
  intro u hu v hv huv
  exact le_trans (hker B lo hi hle hB (u - v)) (hE u hu v hv huv)

end

end RHTower.Sieve
