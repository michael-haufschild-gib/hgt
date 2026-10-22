import GaloisForLFunctions.RHTower.Sieve.GuthMaynardTheoremOneOne
import GaloisForLFunctions.RHTower.ZetaZeroDensityThirtyThirteenths
import GaloisForLFunctions.RHTower.PrimeShortIntervalsSeventeenThirtieths

/-!
# The zero-density exponent `30/13` and primes in `(x, x + x^{17/30+ε}]`, unconditionally

Guth–Maynard Theorem 1.2 and Corollary 1.3 in the corpus's form, with the large values datum
discharged by `guthMaynardLargeValuesBound_holds`:

* `N(σ, T) ≪ T^{(30/13 + ε)(1−σ)} (log T)^{O(1)}` uniformly for `σ ∈ [1/2, 1]`;
* `ψ(x + x^α) − ψ(x) ∼ x^α` for every `α > 17/30`;
* a prime in `(x, x + x^α]` for all large `x`.
-/

set_option autoImplicit false

namespace RHTower

open Filter Topology

/-- **The zero-density estimate with exponent `30/13`**, unconditionally: for every `0 < ε ≤ 1`
there are `D`, `B`, `T₀` with
`#(zeroHeightBox σ T) ≤ D (1 + log T)^B T^{(30/13 + ε)(1−σ)}` for all `T ≥ T₀`, `σ ∈ [1/2, 1]`. -/
theorem exists_zeroHeightBox_ncard_le_thirtyThirteenths {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ →
      σ ≤ 1 →
      ((zeroHeightBox σ T).ncard : ℝ) ≤ D * (1 + Real.log T) ^ B * T ^ ((30 / 13 + ε) * (1 - σ)) :=
  exists_zeroHeightBox_ncard_le_thirty_thirteenths
    GuthMaynard.guthMaynardLargeValuesBound_holds hε hε1

/-- **The prime number theorem in every short interval of length `x^α`, `α > 17/30`**,
unconditionally. -/
theorem tendsto_psi_short_window_div_seventeenThirtieths {α : ℝ} (hα : 17 / 30 < α)
    (hα1 : α < 1) :
    Tendsto (fun x : ℝ => (Chebyshev.psi (x + x ^ α) - Chebyshev.psi x) / x ^ α) atTop (𝓝 1) :=
  tendsto_psi_short_window_div_seventeen_thirtieths
    GuthMaynard.guthMaynardLargeValuesBound_holds hα hα1

/-- **The `θ`-window lower bound at exponent `17/30`**, unconditionally. -/
theorem exists_theta_window_lower_seventeenThirtieths {α : ℝ} (hα : 17 / 30 < α) (hα1 : α < 1) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y :=
  exists_theta_window_lower_seventeen_thirtieths
    GuthMaynard.guthMaynardLargeValuesBound_holds hα hα1

/-- **A prime in `(x, x + x^α]` for every `α > 17/30` and all large `x`**, unconditionally. -/
theorem eventually_exists_prime_short_interval_seventeenThirtieths {α : ℝ} (hα : 17 / 30 < α)
    (hα1 : α < 1) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x ^ α :=
  eventually_exists_prime_short_interval_seventeen_thirtieths
    GuthMaynard.guthMaynardLargeValuesBound_holds hα hα1

end RHTower
