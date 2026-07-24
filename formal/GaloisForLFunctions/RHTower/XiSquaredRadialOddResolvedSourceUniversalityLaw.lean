import GaloisForLFunctions.RHTower.CompletedPrimeGammaResolvedMomentColligation
import GaloisForLFunctions.RHTower.SquaredXiRadialJetSourceAlignment

/-!
# Xi squared-radial odd resolved-source universality

The parity normalization in each completed odd logarithmic-derivative moment cancels the same
parity normalization in its exact prime--Gamma--polar resolution.  Consequently all odd
coefficients of the alternating squared-radial Xi jet carry one common negative source sign.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Every odd Xi logarithmic jet on the real Euler half-plane is the factorial multiple of its
exact prime + Gamma − polar resolved moment.  The two parity normalizations cancel. -/
theorem iteratedDeriv_xiLogDeriv_odd_ofReal_eq_factorial_mul_resolved
    {x : ℝ} (hx : 1 < x) (k : ℕ) :
    iteratedDeriv (2 * k + 1) xiLogDeriv (x : ℂ) =
      ((2 * k + 1).factorial : ℂ) *
        (completedPrimeGammaResolvedMoment x k : ℂ) := by
  have h := completedOddLogDerivMoment_ofReal_eq_resolved hx k
  rw [completedOddLogDerivMoment,
    show logDeriv xi = xiLogDeriv by
      funext s
      rw [logDeriv_apply, xiLogDeriv]] at h
  push_cast at h
  have hfac : (((2 * k + 1).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * k + 1)
  have hsign : (-1 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hfac] at h
  exact mul_left_cancel₀ hsign (by simpa [mul_assoc] using h)

/-- Odd-index sector of the alternating squared-radial Xi logarithmic-jet polynomial, with
indices restricted to the polynomial's triangular range. -/
def squaredXiOddRadialJetPolynomial (n : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ (Finset.range (n + 1)).filter (fun k => 2 * k + 1 < n + 1),
    (squaredRadialJetWeight n (2 * k + 1) : ℂ) *
      ((x - 1 / 2 : ℝ) : ℂ) ^ (2 * k + 1) *
      (-1 : ℂ) ^ (2 * k + 1) *
      iteratedDeriv (2 * k + 1) xiLogDeriv (x : ℂ)

/-- Positive-sign prime--Gamma--polar carrier corresponding to the odd squared-radial sector. -/
def squaredXiOddRadialResolvedSourcePolynomial (n : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ (Finset.range (n + 1)).filter (fun k => 2 * k + 1 < n + 1),
    (squaredRadialJetWeight n (2 * k + 1) : ℂ) *
      ((x - 1 / 2 : ℝ) : ℂ) ^ (2 * k + 1) *
      ((2 * k + 1).factorial : ℂ) *
      (completedPrimeGammaResolvedMoment x k : ℂ)

/-- **Xi squared-radial odd resolved-source universality.**  At every radial depth and every
real Euler-half-plane base point, the complete odd alternating radial sector is the negative of
its exact prime--Gamma--polar resolved source sector. -/
theorem squaredXiOddRadialJetPolynomial_eq_neg_resolvedSource
    {x : ℝ} (hx : 1 < x) (n : ℕ) :
    squaredXiOddRadialJetPolynomial n x =
      -squaredXiOddRadialResolvedSourcePolynomial n x := by
  rw [squaredXiOddRadialJetPolynomial,
    squaredXiOddRadialResolvedSourcePolynomial, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDeriv_xiLogDeriv_odd_ofReal_eq_factorial_mul_resolved hx k]
  have hodd : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hodd]
  ring

end

end RHTower
