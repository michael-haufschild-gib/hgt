# 113 — The two quantitative supplies: Chebyshev window counts, the gap interface, and full defect reachability

[PROVED HERE, Lean: `WindowBudget.lean`] — both open supplies named in doc 112 are now
built: the Chebyshev window-count supply as unconditional theorems, and the PNT-grade
prime-gap supply as a named interface with its unconditional region and full
conditional transfer. The payoff is the reachability theorem: the defect walk hits
every nonnegative target to arbitrary precision.

## The Chebyshev window counts (unconditional)

Mathlib's Chebyshev bounds (`theta_ge'`, `theta_le_log4_mul_x` — upstreamed from the
PrimeNumberTheoremAnd project) pin the log-weighted prime mass of any multiplicative
window:

- `sum_log_windowPrimes` — the window's log-prime mass IS the θ-increment;
- `windowPrimes_card_ge` — the count of primes in `(x, y]` is at least
  `((y−1)log 2 − log(y+2) − 2√y·log y − x·log 4)/log y`, which for `y = e^L·x` grows
  like `x·(e^L·log 2 − log 4)/log x`: **positive threshold exactly `L > log 2`** — the
  same threshold as Bertrand, but now with divergent counts instead of one prime.

## The gap interface (the PNT-grade supply, named)

- `PrimeWindowSupply L` — beyond some threshold every logarithmic window of length `L`
  contains a prime. `primeWindowSupply_of_log_two_lt`: unconditional for `L > log 2`.
  For arbitrary `L > 0` this is the short-gap consequence of PNT (`log(p'/p) → 0`) —
  mathlib holds no PNT, so this is the honest named input, per the tree's interface
  discipline.
- `exists_prime_sin_pos_of_supply` / `_neg_of_supply` — given the supply at length
  `π/(2τ)`, the quarter-offset windows give primes with `sin(τ log q) ≥ √2/2` (resp.
  `≤ −√2/2`) beyond any bound — a UNIFORM sine floor at EVERY height `τ > 0`.
- `exists_prime_mirrorTiltIncrement_pos_of_supply` / `_neg_of_supply` — **the steering
  wheel at every height, conditional on the gap supply**, closing the height
  restriction of doc 112 up to the named input.

## Full reachability (the payoff)

Supporting bricks: `anchorMirrorDefect_eq_sum` (the defect is literally the sum of its
per-prime steps), `arctan_ge_half_self` (linear floor on `[0,1]`),
`exists_subset_sum_between` (greedy accumulation: a pool of nonnegative steps each
`≤ ε` with total `≥ T` has a sub-pool summing into `[T, T+ε]`), `rpow_neg_anti`,
`log_le_mul_rpow` (`log t ≤ m·t^(1/m)` — the filter-free asymptotics).

**`anchorMirrorDefect_reachable_nonneg`** — for every strip point with
`0 < Im s < π/(2 log 2)`, every target `T ≥ 0` and tolerance `ε > 0`, there is a
finite set of primes `P` with

```
T ≤ anchorMirrorDefect P s ≤ T + ε.
```

Proof shape, fully explicit (no filters, no asymptotic notation): one late
quarter-offset sine window `(x, Cx]`, `C = e^{π/(2τ)}`, carries — by the Chebyshev
count — at least `(A₀/2)x/log y` primes once `x` beats an explicit threshold
(`A₀ = C log 2 − log 4 > 0`; the lower-order Chebyshev terms are absorbed by
`log t ≤ m·t^{1/m}` into `K·x^{3/4} ≤ (A₀/2)x`); each such prime's increment lies
between the explicit floor `y^{−Re s}·√2/8` (arctan linear bound) and the ceiling
`4x^{−σ₀} ≤ ε`; the window budget therefore exceeds any `T` once
`x^{(1−Re s)/2} ≥ T/c₉`, and the greedy accumulation stops inside `[T, T+ε]`.

## Route state

| supply (doc 112) | status |
|---|---|
| sign-steering below `π/log 2` | PROVEN (doc 112, Bertrand) |
| sign-steering at ALL heights | PROVEN conditional on `PrimeWindowSupply(π/2τ)`; interface unconditional for `τ < π/(2log2)` |
| divergent window budgets | PROVEN (Chebyshev, threshold `L > log 2`) |
| full defect reachability | **PROVEN unconditionally for `0 < Im s < π/(2 log 2)`**, to every `T ≥ 0` within every `ε` |

Next objects: (i) the mirrored negative-target reachability (same proof at window
offset `5π/4`; mechanical); (ii) reachability at all heights conditional on a counting
strengthening of `PrimeWindowSupply` (interface + transfer, same greedy); (iii) the
meeting argument itself — with the defect now provably steerable onto any nonnegative
angle at Chebyshev heights, the incompatibility question is fully quantitative: what
boundary-orientation positions can an odd class occupy as the defect sweeps `[0, ∞)`
mod the `2π`-quantization of `anchorMirrorDefect_int_of_lineReflection`?
