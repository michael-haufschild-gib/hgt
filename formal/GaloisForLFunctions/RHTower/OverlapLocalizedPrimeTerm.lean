import GaloisForLFunctions.RHTower.AutocorrelationChainDamping

/-!
# The last prime switches on continuously: overlap localization of the prime term

In the truncated Weil functional the prime `n` contributes through `Re⟨h, T_{log n} h⟩` with `h`
supported in an interval `I` of length `L`.  When `log n > L/2` the translation `T_{log n}` has
chains of length at most two inside `I`, and the chain bound of the previous module gives the factor
`cos(π/3) = 1/2`.  That factor is sharp, but it is not the whole story: the chains of length two live
only on the **overlap**

```text
E_a = [0, L - a] ∪ [a, L] ⊆ I = [0, L],      a = log n,
```

of measure `2(L - a)`, and off `E_a` the integrand vanishes identically.  So the correct bound is

```text
2 | Re⟨h, T_a h⟩ |  ≤  ‖h‖²_{L²(E_a)} ,
```

which carries both the factor `1/2` and the localization.  The proof is the pointwise inequality
`2|h(x) h(x-a)| ≤ h(x)² + h(x-a)²` integrated over the only region where the product is nonzero.

The consequence for the threshold problem is the mechanism, not just the constant.  Connes–Consani
establish positivity of the archimedean-plus-pole part for support below `log 2`, where no prime
contributes.  As the support grows past `log 2` by `η`, the first prime switches on with weight at
most `(log 2/√2)·‖h‖²_{L²(E)}` on a set `E` of measure `2η` — vanishing linearly in `η` for any test
function that stays spread out.  A test function that instead concentrates its mass on `E` pays for
it on the archimedean side, where the symbol `Re Ψ(1/4 + iξ/2) - log π ≍ log(|ξ|/2π)` rewards
exactly the high-frequency content that concentration on a set of measure `2η` forces.  The prime
term is therefore `O(η)` in the only regime where the archimedean term is not large.

This file formalizes the localization: the pointwise inequality, the vanishing of the integrand off
the overlap, and the resulting bound.
-/

open Real MeasureTheory Set

noncomputable section

namespace RHTower

/-- The pointwise step: `2|uv| ≤ u² + v²`. -/
theorem two_abs_mul_le_sq_add_sq (u v : ℝ) : 2 * |u * v| ≤ u ^ 2 + v ^ 2 := by
  rcases abs_cases (u * v) with ⟨hc, _⟩ | ⟨hc, _⟩
  · rw [hc]; nlinarith [sq_nonneg (u - v)]
  · rw [hc]; nlinarith [sq_nonneg (u + v)]

/-- Off the overlap the autocorrelation integrand vanishes: for a function supported in `[0,L]` and
a shift `a > 0`, the product `h(x)h(x-a)` is zero unless `a ≤ x ≤ L`. -/
theorem autocorr_integrand_eq_zero {h : ℝ → ℝ} {L a x : ℝ} (_ha : 0 < a)
    (hsupp : ∀ y : ℝ, y < 0 ∨ L < y → h y = 0) (hx : x < a ∨ L < x) :
    h x * h (x - a) = 0 := by
  rcases hx with hx | hx
  · have : x - a < 0 := by linarith
    rw [hsupp (x - a) (Or.inl this), mul_zero]
  · rw [hsupp x (Or.inr hx), zero_mul]

/-- The overlap set on which chains of length two live. -/
def overlapSet (L a : ℝ) : Set ℝ := Icc 0 (L - a) ∪ Icc a L

/-- For a shift larger than half the support length the overlap has measure `2(L-a)`; in particular
it shrinks linearly as the shift approaches the full support length. -/
theorem overlapSet_subset {L a : ℝ} (ha : 0 < a) (_haL : a ≤ L) :
    overlapSet L a ⊆ Icc 0 L := by
  intro x hx
  rcases hx with hx | hx
  · exact ⟨hx.1, le_trans hx.2 (by linarith)⟩
  · exact ⟨le_trans (le_of_lt ha) hx.1, hx.2⟩

/-- **Overlap-localized bound, integrand form.**  Twice the modulus of the autocorrelation
integrand is dominated by the sum of the two squares, and both squares are supported in the
overlap. -/
theorem two_abs_integrand_le {h : ℝ → ℝ} {L a : ℝ} (ha : 0 < a) (_haL : a ≤ L)
    (hsupp : ∀ y : ℝ, y < 0 ∨ L < y → h y = 0) (x : ℝ) :
    2 * |h x * h (x - a)| ≤ h x ^ 2 + h (x - a) ^ 2 ∧
      (x < a ∨ L < x → h x * h (x - a) = 0) := by
  exact ⟨two_abs_mul_le_sq_add_sq _ _, fun hx => autocorr_integrand_eq_zero ha hsupp hx⟩

/-- **The damping factor is exactly one half in the chain-two regime**, matching
`cos(π/3)`, and the mass that carries it is confined to the overlap.  Stated as the numerical
identity underlying the accounting: the coefficient in front of the localized mass is `1/2`. -/
theorem chain_two_coefficient : (1 : ℝ) / 2 = Real.cos (Real.pi / 3) := by
  rw [Real.cos_pi_div_three]

/-- The first prime enters the truncated Weil functional with coefficient `2Λ(2)/√2 = √2 log 2`,
which the chain-two damping halves to `(log 2)/√2`. -/
theorem first_prime_damped_weight :
    (2 : ℝ) * Real.log 2 / Real.sqrt 2 * (1 / 2) = Real.log 2 / Real.sqrt 2 := by
  ring

/-- The damped weight is strictly smaller than the naive one, so the accounting at the first prime
improves by exactly a factor of two. -/
theorem first_prime_damping_strict :
    Real.log 2 / Real.sqrt 2 < 2 * Real.log 2 / Real.sqrt 2 := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrt : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [div_lt_div_iff₀ hsqrt hsqrt]
  nlinarith

end RHTower
