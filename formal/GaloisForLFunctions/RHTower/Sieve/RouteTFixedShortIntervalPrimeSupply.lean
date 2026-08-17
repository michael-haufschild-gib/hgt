import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinHoheiselEveryBase
import GaloisForLFunctions.RHTower.Sieve.RouteTShortIntervalHandoff

/-!
# Prime supply in every Route-T upper physical window

The Route-T upper physical window at height exponent `mu` has additive width `x^(1-1/mu)`, and
above the handoff height that exponent is at least `3/4 - d/2`, where `d < 1/100` is the Maynard
long global amplitude deficit.  The fixed rational `71/100` lies strictly between the
coefficient-three density threshold `2/3` and that handoff exponent, and every sufficiently large
interval `(x, x + x^(71/100)]` contains a prime.

Consequently there is a *single* threshold `X₀`, independent of `mu`, past which every Route-T
upper physical window contains a prime.  The continuum of route-specific seam widths collapses to
one fixed short-interval prime-supply exponent, with no Riemann hypothesis, no density hypothesis
and no route-specific cancellation input.
-/

namespace RHTower.Sieve

noncomputable section

/-- The fixed exponent sits strictly above the coefficient-three density threshold `2/3`, so it
leaves a positive rational reserve on the classical side as well as on the Route-T side. -/
theorem two_thirds_lt_routeTHoheiselEveryBaseExponent :
    (2 : ℝ) / 3 < routeTHoheiselEveryBaseExponent := by
  unfold routeTHoheiselEveryBaseExponent
  norm_num

/-- The fixed exponent is squeezed strictly between the density threshold and the Route-T
handoff exponent, with fixed rational margins on both sides. -/
theorem routeTHoheiselEveryBaseExponent_mem_margin :
    (2 : ℝ) / 3 < routeTHoheiselEveryBaseExponent ∧
      routeTHoheiselEveryBaseExponent < routeTPhysicalSliceHandoffTheta :=
  ⟨two_thirds_lt_routeTHoheiselEveryBaseExponent, routeTHoheiselEveryBaseExponent_lt_handoff⟩

/-- **Prime supply at the fixed exponent, with an explicit threshold.**  There is a single
`X₀ ≥ 1` past which every interval `(x, x + x^(71/100)]` contains a prime. -/
theorem exists_threshold_routeT_prime_in_fixed_window :
    ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧
        (p : ℝ) ≤ x + x ^ routeTHoheiselEveryBaseExponent := by
  obtain ⟨X₁, hX₁⟩ :=
    (Filter.eventually_atTop.1 exists_eventually_routeT_prime_in_every_base_window)
  refine ⟨max 1 X₁, le_max_left _ _, ?_⟩
  intro x hx
  exact hX₁ x ((le_max_right (1 : ℝ) X₁).trans hx)

/-- **The Route-T fixed short-interval handoff.**  There is one threshold `X₀ ≥ 1`, uniform in the
height exponent, such that for every `x ≥ X₀` and every `mu` above the Route-T physical-slice
handoff there is a prime `p` with `x < p ≤ x + x^(1-1/mu)`.

This deletes Route T's signed over-height true-prime boundary as an independent analytic problem:
the whole upper phase is discharged by one unconditional short-interval prime-supply theorem at a
fixed rational exponent. -/
theorem exists_threshold_routeT_prime_in_every_upperPhase_window :
    ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ mu : ℝ, routeTPhysicalSliceHandoffMu ≤ mu →
      ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x + x ^ (1 - 1 / mu) := by
  obtain ⟨X₀, hX₀, hsupply⟩ := exists_threshold_routeT_prime_in_fixed_window
  refine ⟨X₀, hX₀, ?_⟩
  intro x hx mu hmu
  obtain ⟨p, hp, hlow, hhigh⟩ := hsupply x hx
  have hx1 : (1 : ℝ) ≤ x := hX₀.trans hx
  refine ⟨p, hp, hlow, hhigh.trans ?_⟩
  have hmono : x ^ routeTHoheiselEveryBaseExponent ≤ x ^ (1 - 1 / mu) :=
    Real.rpow_le_rpow_of_exponent_le hx1
      (routeTHoheiselEveryBaseExponent_lt_widthExponent hmu).le
  linarith

/-- The same supply expressed on the Route-T physical window itself: every sufficiently large
upper physical window carries strictly positive Chebyshev prime mass, uniformly in the height
exponent. -/
theorem exists_threshold_routeT_upperPhase_theta_window_pos :
    ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ mu : ℝ, routeTPhysicalSliceHandoffMu ≤ mu →
      0 < Chebyshev.theta (x + x ^ (1 - 1 / mu)) - Chebyshev.theta x := by
  obtain ⟨X₀, hX₀, hsupply⟩ := exists_threshold_routeT_prime_in_every_upperPhase_window
  refine ⟨X₀, hX₀, ?_⟩
  intro x hx mu hmu
  obtain ⟨p, hp, hlow, hhigh⟩ := hsupply x hx mu hmu
  have hx1 : (1 : ℝ) ≤ x := hX₀.trans hx
  exact chebyshevTheta_window_pos_of_prime (by linarith) hp hlow hhigh

end

end RHTower.Sieve
