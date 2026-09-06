import Mathlib

/-!
# An exponential deficit cannot satisfy a polynomial lower bound

Deleting from the rational primes a set `B` with `π_B(t) ≍ t^γ` multiplies the zeta function by the
Euler deficit `Φ(s) = ∏_{p ∈ B}(1 - p^{-s})`, which satisfies

```
0 < Φ(σ) ≤ exp(-g(σ)),        g(σ) = ∑_{p ∈ B} p^{-σ} ≍ 1/(σ - γ)   as σ ↓ γ.
```

So `Φ(σ) → 0` at least as fast as `exp(-c/(σ-γ))`, faster than every power of `σ - γ`.  Were the
perturbed zeta analytic across the real point `γ`, it would vanish there to some finite order `m`,
forcing `Φ(σ) ≥ K (σ-γ)^m`.  The two demands are incompatible.

This module proves only the incompatibility of the two displayed real bounds.  An arithmetic
application must separately prove those bounds and the continuation/counting implications.
Nonextendibility across a boundary point does not by itself classify an isolated essential
singularity.  In particular, a deletion count of size `t^γ / log t` does not supply the displayed
`1 / (σ - γ)` deficit: logarithmic divergence can exponentiate to a finite-order zero.

The only input is `log v ≤ v - 1`.
-/

open Set

namespace RHTower.ThinDeletion

/-- For small `t > 0` an exponential deficit `exp(-c/t)` beats every power `K t^m`. -/
theorem exp_neg_div_lt_pow {c : ℝ} (hc : 0 < c) (m : ℕ) {K : ℝ} (hK : 0 < K) :
    ∃ t₀ > 0, ∀ t : ℝ, 0 < t → t < t₀ → Real.exp (-(c / t)) < K * t ^ m := by
  set U : ℝ := max 1 ((2 * (m : ℝ) + |Real.log K| + 1) / c) with hUdef
  have hU1 : (1 : ℝ) ≤ U := le_max_left _ _
  have hUpos : (0 : ℝ) < U := by linarith
  refine ⟨1 / U ^ 2, by positivity, ?_⟩
  intro t ht0 htlt
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  set v : ℝ := 1 / Real.sqrt t with hvdef
  have hvpos : 0 < v := by positivity
  -- `t < 1 / U ^ 2` gives `v > U`
  have hvU : U < v := by
    have hsq : Real.sqrt t < 1 / U := by
      have h1 : Real.sqrt t < Real.sqrt (1 / U ^ 2) := by
        exact Real.sqrt_lt_sqrt ht0.le htlt
      have h2 : Real.sqrt (1 / U ^ 2) = 1 / U := by
        rw [one_div, Real.sqrt_inv, Real.sqrt_sq hUpos.le, one_div]
      rwa [h2] at h1
    rw [hvdef, lt_div_iff₀ hst]
    calc U * Real.sqrt t < U * (1 / U) := by
          exact mul_lt_mul_of_pos_left hsq hUpos
      _ = 1 := by field_simp
  -- the quadratic in `v` is positive
  have hquad : 0 < c * v ^ 2 - 2 * (m : ℝ) * v + Real.log K := by
    have hcv : 2 * (m : ℝ) + |Real.log K| + 1 ≤ c * v := by
      have : (2 * (m : ℝ) + |Real.log K| + 1) / c ≤ U := le_max_right _ _
      have h2 : (2 * (m : ℝ) + |Real.log K| + 1) / c < v := lt_of_le_of_lt this hvU
      rw [div_lt_iff₀ hc] at h2
      linarith [h2, mul_comm v c]
    have hv1 : (1 : ℝ) ≤ v := le_trans hU1 hvU.le
    have habs : -|Real.log K| ≤ Real.log K := neg_abs_le _
    have step1 : (2 * (m : ℝ) + |Real.log K| + 1) * v ≤ c * v * v :=
      mul_le_mul_of_nonneg_right hcv hvpos.le
    have step2 : |Real.log K| + 1 ≤ (|Real.log K| + 1) * v := by
      nlinarith [abs_nonneg (Real.log K)]
    have hvsq : c * v * v = c * v ^ 2 := by ring
    nlinarith [step1, step2, habs, hvsq]
  -- translate back: `c / t = c * v ^ 2` and `m * log t ≥ -2 * m * v`
  have hcv2 : c / t = c * v ^ 2 := by
    rw [hvdef, div_pow, one_pow, Real.sq_sqrt ht0.le]
    field_simp
  have hlogt : -(2 * (m : ℝ) * v) ≤ (m : ℝ) * Real.log t := by
    have hlv : Real.log v ≤ v - 1 := Real.log_le_sub_one_of_pos hvpos
    have hlogsqrt : Real.log t = -(2 * Real.log v) := by
      rw [hvdef, one_div, Real.log_inv, Real.log_sqrt ht0.le]
      ring
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [hlogsqrt]
    nlinarith
  have hpos : (0 : ℝ) < K * t ^ m := by positivity
  rw [← Real.log_lt_log_iff (Real.exp_pos _) hpos, Real.log_exp,
    Real.log_mul (ne_of_gt hK) (by positivity), Real.log_pow]
  rw [hcv2]
  linarith

/-- **No finite-order zero can absorb an exponential deficit.**

If `Φ` is bounded above by `exp(-c/(σ-γ))` and simultaneously below by `K (σ-γ)^m` on a right
neighbourhood of `γ`, no such `Φ` exists.

In the arithmetic application `Φ` is the Euler deficit `∏_{p∈B}(1 - p^{-σ})` of a deleted set of
primes of counting exponent `γ`: the upper bound is the divergence `∑_{p∈B}p^{-σ} ≫ 1/(σ-γ)`, and
the lower bound would follow from a nonzero analytic extension of the perturbed zeta at `γ`,
together with the required quotient identity and `ζ(γ) ≠ 0`.  Those arithmetic and analytic bridges
are not formalized by this theorem.  No conclusion for logarithmically thinner deletions follows
without the stated exponential upper bound. -/
theorem no_finite_order_zero_absorbs_exponential_deficit
    {γ c K : ℝ} (hc : 0 < c) (hK : 0 < K) (m : ℕ) (Φ : ℝ → ℝ)
    (hupper : ∀ σ ∈ Ioo γ (γ + 1), Φ σ ≤ Real.exp (-(c / (σ - γ))))
    (hlower : ∀ σ ∈ Ioo γ (γ + 1), K * (σ - γ) ^ m ≤ Φ σ) : False := by
  obtain ⟨t₀, ht₀, hbeat⟩ := exp_neg_div_lt_pow hc m hK
  set t : ℝ := min t₀ 1 / 2 with htdef
  have ht0 : 0 < t := by
    have : 0 < min t₀ 1 := lt_min ht₀ one_pos
    positivity
  have htlt : t < t₀ := by
    have h1 : min t₀ 1 ≤ t₀ := min_le_left _ _
    have h2 : 0 < min t₀ 1 := lt_min ht₀ one_pos
    rw [htdef]
    linarith
  have ht1 : t < 1 := by
    have h1 : min t₀ 1 ≤ 1 := min_le_right _ _
    have h2 : 0 < min t₀ 1 := lt_min ht₀ one_pos
    rw [htdef]
    linarith
  have hmem : γ + t ∈ Ioo γ (γ + 1) := ⟨by linarith, by linarith⟩
  have h1 := hupper _ hmem
  have h2 := hlower _ hmem
  have hsub : γ + t - γ = t := by ring
  rw [hsub] at h1 h2
  have := hbeat t ht0 htlt
  linarith

end RHTower.ThinDeletion
