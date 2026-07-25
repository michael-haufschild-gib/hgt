import GaloisForLFunctions.RHTower.SharpLogDerivativeLowerBound

/-!
# Reaching the Liouville point of the Bohr torus costs height

The two sharp endpoints of the prime symbol sit at different points of the Bohr torus.  The upper
endpoint is at `θ_p = 0` for every `p`, which the Kronecker line meets at `ξ = 0`.  The lower
endpoint is at `θ_p = π` for every `p`, that is at `p^{iξ} = -1` for all `p ≤ N`, equivalently
`n^{iξ} ≈ λ(n)` on `N`-smooth `n` with `λ` the Liouville function.  **The Liouville point is never
on the line**, and approaching it costs height.

The cost is bounded below with no transcendence input at all.  If `ξ log p = bπ + δ₁` and
`ξ log q = aπ + δ₂` with `|δ_i| ≤ ε`, then eliminating `π`,

```text
ξ · |a log p - b log q| = |a δ₁ - b δ₂| ≤ ε (a + b),
```

and `a log p - b log q = log(p^a) - log(q^b)` is the logarithm of a ratio of two **distinct positive
integers** whenever `p ≠ q` are primes.  For distinct positive integers `A > B`, `log u ≥ 1 - 1/u`
gives `log A - log B ≥ (A-B)/A ≥ 1/A`.  Hence

```text
ε  ≥  ξ / ( (a+b) · max(p^a, q^b) ).
```

Since `a, b` grow linearly in `ξ`, the right-hand side decays only exponentially in `ξ`, so the
elementary bound gives `ξ ≳ log(1/ε)`.  Sharpening the linear form in two logarithms by
Baker–Wüstholz or Laurent–Mignotte–Nesterenko, `|a log p - b log q| ≥ exp(-C (log B)²)` with
`B = max(a,b) ≍ ξ`, upgrades this to `ξ ≥ exp(c√(log(1/ε)))`; Dirichlet's box principle gives the
upper bound `ξ ≪ ε^{-2}`, so the truth lies between.

What matters for the programme is the direction: the extremal point at which the sharp lower bound
of the previous module is attained is inaccessible to the Kronecker line at any bounded height.  The
line's arithmetic — not merely its measure-zero-ness — is what keeps it away.  This file formalizes
the elementary, transcendence-free half.
-/

open Real

noncomputable section

namespace RHTower

/-- `1 - 1/u ≤ log u` for `u > 0`: apply `log v ≤ v - 1` at `v = 1/u`. -/
theorem one_sub_inv_le_log {u : ℝ} (hu : 0 < u) : 1 - 1 / u ≤ Real.log u := by
  have hinv : (0 : ℝ) < 1 / u := by positivity
  have h := Real.log_le_sub_one_of_pos hinv
  rw [Real.log_div one_ne_zero (ne_of_gt hu), Real.log_one] at h
  linarith

/-- **Separation of logarithms of distinct positive integers.**  If `B < A` then
`log A - log B ≥ (A - B)/A`, and in particular `≥ 1/A` when `A - B ≥ 1`. -/
theorem log_sub_log_ge_of_lt {A B : ℝ} (hB : 0 < B) (hAB : B < A) :
    (A - B) / A ≤ Real.log A - Real.log B := by
  have hA : (0 : ℝ) < A := lt_trans hB hAB
  have hdiv : (0 : ℝ) < A / B := by positivity
  have h := one_sub_inv_le_log hdiv
  rw [Real.log_div (ne_of_gt hA) (ne_of_gt hB)] at h
  have hrw : 1 - 1 / (A / B) = (A - B) / A := by field_simp
  linarith [hrw ▸ h]

/-- Integer separation: for distinct positive integers the logarithms are at least `1/max` apart. -/
theorem log_sep_of_int_lt {A B : ℝ} (hB : 0 < B) (hAB : B + 1 ≤ A) :
    1 / A ≤ Real.log A - Real.log B := by
  have hA : (0 : ℝ) < A := by linarith
  have hstep := log_sub_log_ge_of_lt hB (by linarith)
  have hmono : 1 / A ≤ (A - B) / A := by
    rw [div_le_div_iff₀ hA hA]
    nlinarith
  linarith

/-- **Reachability lower bound.**  Suppose the Kronecker line at height `ξ` brings the phases of two
primes within `ε` of `π`, in the sense `|ξ log p - bπ| ≤ ε` and `|ξ log q - aπ| ≤ ε` for positive
integers `a, b`.  Eliminating `π` bounds the linear form `a log p - b log q` by `ε(a+b)/ξ`, and the
integer separation bounds it below by `1/max(p^a, q^b)`.  Hence `ε` cannot be smaller than
`ξ / ((a+b)·max)`. -/
theorem reachability_lower_bound {ξ ε a b lp lq A B : ℝ}
    (hξ : 0 < ξ) (ha : 0 < a) (hb : 0 < b)
    (hA : 0 < A) (hB : 0 < B)
    (hlin : ξ * |a * lp - b * lq| ≤ ε * (a + b))
    (hlogA : Real.log A = a * lp) (hlogB : Real.log B = b * lq)
    (hsep : B + 1 ≤ A) :
    ξ / ((a + b) * A) ≤ ε := by
  have hsepl : 1 / A ≤ Real.log A - Real.log B := log_sep_of_int_lt hB hsep
  have hval : 1 / A ≤ a * lp - b * lq := by rw [← hlogA, ← hlogB]; exact hsepl
  have habs : 1 / A ≤ |a * lp - b * lq| := le_trans hval (le_abs_self _)
  have hmul : ξ * (1 / A) ≤ ξ * |a * lp - b * lq| := by
    exact mul_le_mul_of_nonneg_left habs hξ.le
  have hchain : ξ * (1 / A) ≤ ε * (a + b) := le_trans hmul hlin
  have hab : (0 : ℝ) < a + b := by linarith
  rw [div_le_iff₀ (by positivity)]
  have : ξ * (1 / A) = ξ / A := by ring
  rw [this] at hchain
  have hAne : A ≠ 0 := ne_of_gt hA
  rw [div_le_iff₀ hA] at hchain
  nlinarith [hchain, hab, hA]

/-- The elimination step: from `ξ log p = bπ + δ₁` and `ξ log q = aπ + δ₂` with `|δ_i| ≤ ε`, the
linear form `a log p - b log q` is bounded by `ε(a+b)/ξ`. -/
theorem linear_form_bound {ξ ε a b lp lq d₁ d₂ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h₁ : ξ * lp = b * Real.pi + d₁) (h₂ : ξ * lq = a * Real.pi + d₂)
    (hd₁ : |d₁| ≤ ε) (hd₂ : |d₂| ≤ ε) :
    ξ * |a * lp - b * lq| ≤ ε * (a + b) := by
  have hkey : ξ * (a * lp - b * lq) = a * d₁ - b * d₂ := by
    have e₁ : a * (ξ * lp) = a * (b * Real.pi + d₁) := by rw [h₁]
    have e₂ : b * (ξ * lq) = b * (a * Real.pi + d₂) := by rw [h₂]
    nlinarith [e₁, e₂]
  have habs : |ξ * (a * lp - b * lq)| = ξ * |a * lp - b * lq| ∨ ξ ≤ 0 := by
    rcases le_or_gt ξ 0 with h | h
    · exact Or.inr h
    · left; rw [abs_mul, abs_of_pos h]
  rcases habs with h | h
  · rw [← h, hkey]
    calc |a * d₁ - b * d₂| ≤ |a * d₁| + |b * d₂| := abs_sub _ _
      _ = a * |d₁| + b * |d₂| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * ε + b * ε := by
          have h1 : a * |d₁| ≤ a * ε := mul_le_mul_of_nonneg_left hd₁ ha
          have h2 : b * |d₂| ≤ b * ε := mul_le_mul_of_nonneg_left hd₂ hb
          linarith
      _ = ε * (a + b) := by ring
  · have hεa : 0 ≤ |d₁| := abs_nonneg _
    have hε : 0 ≤ ε := le_trans hεa hd₁
    have : ξ * |a * lp - b * lq| ≤ 0 := by
      have habs0 : 0 ≤ |a * lp - b * lq| := abs_nonneg _
      exact mul_nonpos_of_nonpos_of_nonneg h habs0
    nlinarith [this, hε, ha, hb]

end RHTower
