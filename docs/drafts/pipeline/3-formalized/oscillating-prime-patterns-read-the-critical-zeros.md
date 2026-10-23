# Oscillating prime patterns read the critical zeros

- **ID:** oscillating-prime-patterns-critical-zeros
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Programme:** Trans-Horizon Incidence Mechanics (§3.16–3.17, §5 "the parity pair": prime-density
  heuristics at half damping)
- **Statement:** For `a ∈ [−1, 1]`, `t₀ ∈ ℝ` let `f = f_{a,t₀}` be completely multiplicative with
  `f(p) = a cos(t₀ log p)`. The half-damped weight `f(d) d^{-1/2}` is paid iff
  `t₀ = 0 ∧ a < 1/2`, or `t₀ ≠ 0 ∧ (a < 1 ∨ ζ(1/2 + it₀) = 0)`.

## Why it matters

The real-axis prime mean of `f_{a,t₀}` is `0` for `t₀ ≠ 0`, the value at which the constant-sign
model is paid. Yet `f_{1,t₀}` is unpaid unless `1/2 + it₀` is a zero of `ζ`. So the quarter law is
height-local: the receiver reads the prime mean at every height `τ` (`ν(±t₀) = a/2`), the threshold
`1/2` applies to each height, and on the threshold the receiver is decided by `ζ` on the critical line
at that height. No real-axis density datum decides the half-damped receiver.

## Paper proof

Notation: `S = Σ_p p^{-2}`, `F(w) = Σ f(n)n^{-w}`, `C(s) = F(s + 1/2)`, `s = 1/2 + u + it`.

1. **Euler comparison.** `f(p)p^{-w} = (a/2)(p^{-(w−it₀)} + p^{-(w+it₀)})`. The Euler log-modulus of a
   completely multiplicative `g` with `|g(n)| ≤ |n^{-w}|` is `Re Σ_p g(p) + O(S)` (one bracket per
   prime, `|Re(−log(1−v)) − Re v| ≤ |v|²`). Hence on `Re w > 1`
   `|log|F(w)| − (a/2)(log|ζ(w−it₀)| + log|ζ(w+it₀)|)| ≤ 2S`.
2. **`a ≤ 0`, every `t₀`: paid.** `|F| ≤ e^{2S}(1 + 1/|ζ(w−it₀)|)^{1/2}(1 + 1/|ζ(w+it₀)|)^{1/2}`;
   `1/|ζ(v)| ≤ K(1 + |Im v|)^{1/4}` on `1 < Re v ≤ 2` (box + `3–4–1`), and
   `1 + |t ∓ t₀| ≤ (1 + |t₀|)(1 + |t|)`. Bounded at `|t| ≤ 2`, `O(|t|^{1/4})` beyond: the line-energy
   criterion pays.
3. **`0 < a < 1`, `t₀ ≠ 0`: paid.** WLOG `t₀ > 0`; the line integrand is even in `t`. With
   `|ζ(w)||w − 1| ≤ K₀` (`|Im w| ≤ 2`) and `|ζ(w)| ≤ log|Im w| + 5` (`|Im w| ≥ 2`):
   on `0 < t ≤ T = 2t₀ + 2`, `|C(s)|² ≤ A|t − t₀|^{-a}`; on `t ≥ T`, `|C(s)| ≤ e^{2S}(log t + 6)`.
   `|ζ(s)/s|` is bounded on the box and `∫_{t>2}|ζ(s)|²t^{-3/2}dt` is uniformly bounded; `a < 1`
   makes `|t − t₀|^{-a}` integrable. The line energy is bounded uniformly in `u`: paid.
4. **`a = 1`, `ζ(1/2 + it₀) ≠ 0`: unpaid.** Near `t = t₀`: `|ζ(1 + u + i(t−t₀))| ≥ 1/(2|u + i(t−t₀)|)`,
   `|ζ(1 + u + i(t + t₀))| ≥ c₊ > 0` (`ζ(1 + 2it₀) ≠ 0`), `|ζ(s)| ≥ c₀ > 0`, `|s|` bounded; so the
   integrand is `≥ κ/(u + |t − t₀|) − m²/4` on `|t − t₀| ≤ r`, whose integral is `≥ κ log((u+r)/u) − O(1)`,
   against the cap `4πE` of a paid receiver.
5. **`a = 1`, `ζ(1/2 + it₀) = 0`: paid.** `|ζ(s)| ≤ L|u + i(t − t₀)|` near the zero (derivative bound
   on a closed ball) cancels `|ζ(1+u+i(t−t₀))| ≤ K₀/|u + i(t−t₀)|`: the integrand is bounded on
   `0 < t ≤ T`, and step 3 handles `t ≥ T`.
6. **`t₀ = 0`.** `f_{a,0} = a^{Ω}`, the constant-sign model: paid iff `a < 1/2`
   (`receiverBounded_constantSign_iff_full`); `ζ(1/2) ≠ 0`.
7. **Same prime signs, same prime mean, opposite receivers.** For `t₀ ≠ 0`,
   `Σ_p f(p)p^{-w} = (a/2)(Re P(w − it₀) + Re P(w + it₀))` with `Re P(v) = log|ζ(v)| + O(S)` and
   `log|ζ|` bounded on the segments `[1, 3/2] ± it₀`: the prime mean is `0`. With `t₀` small
   (`ζ(1/2) ≠ 0`, continuity), amplitudes `1/2` (paid) and `1` (unpaid) share signs and prime mean.

## Lean

- `OscillatingPrimePatternsReadTheCriticalZeros.lean`: `oscPattern`, `oscWeight`,
  `abs_log_norm_oscSeries_sub_le`, `norm_oscSeries_le_ge`, `exists_lineEnergy_le_of_majorant`,
  `receiverBounded_oscWeight_nonpos`, `receiverBounded_oscWeight_of_lt_one`.
- `OscillatingPrimePatternsArePaidExactlyAtTheCriticalZeros.lean`:
  `receiverBounded_oscWeight_one_of_zero`, `not_receiverBounded_oscWeight_one`,
  `receiverBounded_oscWeight_one_iff`, `receiverBounded_oscWeight_iff`.
- `PrimeSignsAndPrimeMeansDoNotDecideTheHalfDampedReceiver.lean`:
  `exists_abs_tsum_oscPattern_le`, `exists_paid_unpaid_with_same_prime_signs_and_mean`.

## Gates
- [x] 0 → 1  in-progress (corpus search: no oscillating multiplicative pattern; the critical-zero
  detector exists only for the non-multiplicative `d^{-ε}cos(t log d)`)
- [x] 1 → 2  fully-proven on paper
- [x] 2 → 3  formalized (`receiverBounded_oscWeight_iff`, axioms `propext`, `Classical.choice`,
  `Quot.sound`)

## Log
- 2026-10-23 — step 7 formalized (`PrimeSignsAndPrimeMeansDoNotDecideTheHalfDampedReceiver`);
  moved to 3-formalized.
- 2026-10-23 — formalized: `OscillatingPrimePatternsReadTheCriticalZeros` (steps 1–3),
  `OscillatingPrimePatternsArePaidExactlyAtTheCriticalZeros` (steps 4–6), wired into the THIM umbrella.
- 2026-10-23 — created.
