# The centred damping chain is Hilbert–Schmidt above damping (√5−1)/2

- **ID:** saei-chain-l2-golden
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Source:** SAEI README §9 topic 4; improves `saei-chain-l2-root-two` (`η > 1/√2`)
- **Statement:** For `η² + η > 1` (`η > (√5−1)/2 ≈ 0.618`) and `η < 1` the centred damping chain
  is Hilbert–Schmidt; hence bounded in `ℓ²` on finitely supported sequences.

## Goal
Measured progress on the unconditional `ℓ²` range of the receiver chain, from `1/√2` to the golden
threshold, by an elementary short-interval estimate for `c_η(m) = Σ_{d|m} μ(d) d^{−η}` that uses the
divisor structure (not the signs of `μ`). Source-pure; no zeros.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: paper proof below
- [x] 2 → 3  formalized: final audit clean; axioms `propext`, `Classical.choice`, `Quot.sound`
- [ ] 3 → 4  n/a

## Paper proof
Notation: `P = P_η` the centred prefix of `c_η`, `ρ = ρ_η`, `N = n+1`, `K = k+1`, `a = ⌊N/K⌋`,
`a' = ⌊N/(K+1)⌋`, `J = a − a'`, `C₁ = 1 + 1/(1−η) + 1/η`.

**1. Short-interval lemma.** Let `0 < η < 1`, `a' ≤ a`, `2J ≤ a`, `1 ≤ D`, `J ≤ D ≤ a`. Then
`|P(a) − P(a')| ≤ C_s (D^{1−η} + J D^{−η} + a D^{−1−η})`, `C_s = 2 + 1/(1−η) + 5/η`.
In floor form `P(a) − P(a') = Σ_{d ≤ a} μ(d) d^{−η}(n_d − J/d) − J τ_a`, `n_d = ⌊a/d⌋ − ⌊a'/d⌋`,
`τ_a = Σ_{d > a} μ(d) d^{−1−η}`.
- `d ≤ D`: `|n_d − J/d| ≤ 1`; the part is `≤ Σ_{d ≤ D} d^{−η} ≤ (1 + 1/(1−η)) D^{1−η}`.
- `d > D ≥ J`: `n_d ∈ {0, 1}`, so `|term| ≤ [n_d = 1] d^{−η} + J d^{−1−η}`.
  `Σ_{d > D} J d^{−1−η} ≤ J ⌊D⌋^{−η}/η ≤ 2 J D^{−η}/η`. A divisor with `n_d = 1` has its
  multiple at `d e`, `e = ⌊a/d⌋ ≤ a/D`; for fixed `e` such `d` lie in `(⌊a'/e⌋, ⌊a/e⌋]` (at most
  `J/e + 1` of them), each with `d > a'/e ≥ a/(2e)`, so `d^{−η} ≤ (2/a)^η e^η`. Summing over
  `e ≤ a/D` with `Σ_{e ≤ E} e^{η−1} ≤ 1 + E^η/η`: the part is
  `≤ 2((1 + 1/η) J D^{−η} + a D^{−1−η})`.
- `J |τ_a| ≤ J a^{−η}/η ≤ J D^{−η}/η`.

**2. The jump below the square root.** For `K² ≤ N`:
`|P(a) − P(a')| ≤ C_j (J^{1−η} + a^{(1−η)/2})`, `C_j = 2 C_s + 4 C₁`.
- `K ≥ 2`: `a ≤ 2a'` (with `q = a' ≥ 1`, `N < (q+1)(K+1) ≤ (2q+1)K`), so `2J ≤ a`. Take
  `D = max(J, √a)`: `D^{1−η} ≤ J^{1−η} + a^{(1−η)/2}`, `J D^{−η} ≤ J^{1−η}`,
  `a D^{−1−η} ≤ a·a^{−(1+η)/2} = a^{(1−η)/2}`.
- `K = 1`: `J = N − ⌊N/2⌋ ≥ N/2`, and the sign-blind bound gives
  `|P(a) − P(a')| ≤ 2 C₁ N^{1−η} ≤ 4 C₁ J^{1−η}`.

**3. Interpolation.** With `|P(a) − P(a')| ≤ J` and `C_j ≥ 1`:
`|P(a) − P(a')| ≤ C_j J^{1−η} + C_j J^λ a^{(1−η)(1−λ)/2}` for every `λ ∈ [0, 1]`
(`min(J, y) ≤ J^λ y^{1−λ}`).

**4. Kernel squares below the square root.** The kernel majorant (`K/N`)`K^{−η}`(`|ΔP|` + `2ρ`)
squared, with `J ≤ 2N/K²` and `a ≤ N/K`, is at most `3(4C_j² N^{−2η} K^{2η−2} + 4C_j² N^α K^β +
4ρ² K^{2−2η} N^{−2})`, where `α = −2 + 2λ + (1−η)(1−λ)`, `β = 2 − 2η − 4λ − (1−η)(1−λ)`.

**5. Sums below the square root.** If `α < −1` and `α + (β+1)/2 < −1`, then
`Σ_N Σ_{K² ≤ N} N^α K^β ≤ ζ(s) ζ(u)`. Take `t = (max(0, (β+1)/2) + (−1−α))/2 ≥ 0`: on `K² ≤ N`,
`K^{2t} ≤ N^t`, so `N^α K^β ≤ N^{α+t} K^{β−2t}`, with `s = −(α+t) > 1`, `u = 2t − β > 1`.
- Length term: `α = −2η`, `β = 2η − 2`: needs `η > ½`.
- Interpolated term: `α < −1 ⇔ λ(1+η) < η`; `α + (β+1)/2 < −1 ⇔ (1−η)(1−λ) < 2η − 1 ⇔
  λ(1−η) > 2 − 3η`. A `λ ∈ [0,1]` exists iff `max(0, (2−3η)/(1−η)) < η/(1+η)`, i.e.
  `(2−3η)(1+η) < η(1−η) ⇔ η² + η > 1`. Take the midpoint.
- Density term: as in `saei-chain-l2-root-two`.

**6. Above the square root and the mean-value parts.** Unchanged from `saei-chain-l2-root-two`
(`J ≤ 1`, sparse jumps; HS for every `η > ½`). Summing all families gives a finite
Hilbert–Schmidt constant, and Cauchy–Schwarz row by row gives the `ℓ²` bound. ∎

## Lean
- `ShortIntervalSumsOfTheDampedDivisorCoefficients` — `centeredPrefix_sub_eq`, `fiber_card_le`,
  `sum_large_divisors_le`, `abs_moebiusTail_le`, `abs_centeredPrefix_sub_le_short` (step 1).
- `TheChainIsHilbertSchmidtAboveTheGoldenThreshold` — `abs_jump_le_belowSqrt` (step 2),
  `regionA_golden_sq_le` (steps 3–4), `goldenExp_bounds`, `sum_belowSqrt_rpow_le` (step 5),
  `sq_centeredRow_le_goldenMajorant`, `sum_goldenMajorant_le`,
  `centeredOperator_l2_le_of_goldenThreshold`.
- `TheChainIsHilbertSchmidtAboveInverseRootTwo` gained `abs_centeredRow_le_jump` (the kernel
  majorant with the exact source jump), `sum_sum_belowSqrt_le`, `sum_sum_aboveSqrt_le`.

## Remaining gap
`½ < η ≤ (√5−1)/2`. For fixed `K = N^κ` the summability exponent is linear in `λ`, so the best
choice is an endpoint: the bound `J` is square summable for `κ > 1/(1+2η)`, the bound
`a^{(1−η)/2}` for `κ < η/(2−η)`, and the two meet exactly at `η² + η = 1`. The method is sharp
there; below it the window `η/(2−η) ≤ κ ≤ 1/(1+2η)` needs a short-interval bound for `c_η − ρ`
better than `min(J, a^{(1−η)/2})`.

## Log
- 2026-10-23 — created with the paper proof sketch.
- 2026-10-23 — paper proof for the uniform choice `D = max(J, √a)`; formalized.
