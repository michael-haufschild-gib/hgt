import GaloisForLFunctions.RHTower.Sieve.RouteTEnvelopeRho
import GaloisForLFunctions.RHTower.Sieve.PrimeRangeTwistTail

/-!
# The Granville–Soundararajan tail, reduced to three real inequalities

Composing `Sieve/PrimeRangeTwistTail` with `Sieve/RouteTEnvelopeRho` leaves the tail cosine sum
bounded as soon as the three regimes of the Route-T envelope — contour, Perron truncation and the
Chebyshev remainder — are each below `ρ₀` at every block top of the range.  Nothing arithmetic is
left: the three hypotheses are inequalities between explicit real functions of the block top and the
frequency.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The tail cosine sum from a uniform envelope majorant.** -/
theorem exists_abs_sum_cos_div_primesRange_le_of_envelope :
    ∃ A delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (y z : ℕ) (t ρ₀ : ℝ), 1 ≤ y → y ≤ z → 0 ≤ ρ₀ →
        14 * Real.exp 9 ≤ ρ₀ * (y : ℝ) →
        (∀ i : ℕ, y ≤ i → i ≤ z →
          routeTTwistEnvelope A delta C (-t) (max (i : ℝ) 1) ≤ ρ₀ * (i : ℝ)) →
        |∑ p ∈ primesRange y z, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)|
          ≤ 9 * ρ₀ * (2 + Real.log (z : ℝ)) := by
  obtain ⟨A, delta, C, hdelta, hC, hbound⟩ := exists_abs_sum_cos_div_primesRange_le_routeT
  refine ⟨A, delta, C, hdelta, hC, ?_⟩
  intro y z t ρ₀ hy hyz hρ₀ he9 henv
  have hz : 0 < z := lt_of_lt_of_le hy hyz
  refine hbound y z t (9 * ρ₀) hy hz (by linarith) ?_
  intro i hyi hiz
  have hyR : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hiR : (y : ℝ) ≤ (i : ℝ) := by exact_mod_cast hyi
  have hEi := henv i hyi hiz
  have hEy := henv y le_rfl (le_trans hyi hiz)
  have hEyi : routeTTwistEnvelope A delta C (-t) (max (y : ℝ) 1) ≤ ρ₀ * (i : ℝ) := by
    refine hEy.trans ?_
    exact mul_le_mul_of_nonneg_left hiR hρ₀
  have h14 : 14 * Real.exp 9 ≤ ρ₀ * (i : ℝ) := by
    refine he9.trans ?_
    exact mul_le_mul_of_nonneg_left hiR hρ₀
  linarith [hEi, hEyi, h14]

/-- **The tail cosine sum, reduced to the three envelope regimes.** -/
theorem exists_abs_sum_cos_div_primesRange_le_regimes :
    ∃ A delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (y z : ℕ) (t ρ₀ : ℝ), 1 ≤ y → y ≤ z → 0 ≤ ρ₀ →
        16 * Real.pi / 3 ≤ |t| →
        14 * Real.exp 9 ≤ ρ₀ * (y : ℝ) →
        (∀ i : ℕ, y ≤ i → i ≤ z →
          9 * C * ((3 * (i : ℝ)) ^ (-(min delta (routeTWidthPolylogLower A (-t)) / 6))
            * (routeTTwistHeightFactor A (-t) + Real.log (2 * (i : ℝ)))) ≤ ρ₀) →
        (∀ i : ℕ, y ≤ i → i ≤ z →
          9 * C * ((3 * (i : ℝ)) ^ (2 * (1 / (routeTWidthUpperConst
                * (Real.log |t| / Real.log 2) ^ ((9 : ℝ) / 10))) / 3)
            * (1 + (Real.log (i : ℝ)) ^ 2 + routeTTwistHeightFactor A (-t)))
            / (1 + |t|) ≤ ρ₀) →
        (∀ i : ℕ, y ≤ i → i ≤ z → 6 * Real.log (i : ℝ) / Real.sqrt (i : ℝ) ≤ ρ₀) →
        |∑ p ∈ primesRange y z, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)|
          ≤ 9 * ρ₀ * (2 + Real.log (z : ℝ)) := by
  obtain ⟨A, delta, C, hdelta, hC, hbound⟩ := exists_abs_sum_cos_div_primesRange_le_of_envelope
  refine ⟨A, delta, C, hdelta, hC, ?_⟩
  intro y z t ρ₀ hy hyz hρ₀ hτ he9 h1 h2 h3
  have habs : |(-t : ℝ)| = |t| := abs_neg t
  refine hbound y z t ρ₀ hy hyz hρ₀ he9 ?_
  intro i hyi hiz
  have hi1 : 1 ≤ i := le_trans hy hyi
  have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
  have hmax : max ((i : ℕ) : ℝ) 1 = (i : ℝ) := max_eq_left hiR
  rw [hmax]
  refine routeTTwistEnvelope_le_mul hC.le hiR (by rw [habs]; exact hτ) ?_ ?_ ?_
  · exact h1 i hyi hiz
  · rw [habs]
    exact h2 i hyi hiz
  · exact h3 i hyi hiz

end

end RHTower.Sieve
