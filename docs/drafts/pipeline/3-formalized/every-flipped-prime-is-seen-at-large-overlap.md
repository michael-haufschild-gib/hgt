# Every flipped prime is seen at a finite overlap

- **ID:** every-flipped-prime-is-seen-at-large-overlap
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** EAHT §9 Q5 ("for the remote flips the threshold `c*(p)` is open"); obstacle I2 (flip
  selectivity beyond `ω_11`); `1-in-progress/bounded-overlap-complete-weil-and-prime-flips.md` item 2.
- **Statement:** For every admissible profile and every prime `p` there is `c₀(p)` such that for
  every `c ≥ c₀`, eventually in `N`, the Weil form twisted by `λ(n) = (−1)^{v_p(n)}Λ(n)` is negative on
  the prime-square trial `F_p(n)/√n` at width `c/N`. For the tilted unit spline, `ζ`'s complete form
  is eventually positive definite at the same overlaps.

## Proof
`Q_λ(f) − Q(f) = Σ_{k odd} (2 log p/p^{k/2}) pairing_f(p^k)`, and on an atomic test
`pairing_f(k) = 2 Σ_{a,b} x_a x_b A_g(log k − log(b/a))`. Exact ratios `b = ka` give
`‖g‖²(P_N(x) − P_N(εx))`. The first prime gives `(4 log p/p)(−1 + 2/p²)` per `log N`; the higher odd
powers `p^{2j+3}` meet trial value one on `p²`-multiples and cost at most `2τ_p(1 − 1/p + 1/p²)`,
`τ_p = 2 log p/(p(p² − 1))` (`sharpFlipBound`); the total `4 log p (−p⁴ + 4p² − p − 1)/(p³(p² − 1))`
is negative for every prime. Off-ratio pairs have `|b − ka| ≤ 3wka`, `b ≥ ka/3`, so each lag costs
`≤ 72 c ‖g‖²/√k` and all flipped lags `≤ 144 c log p ‖g‖²`, independent of `N`. The trial is
`√log N Σ_{m | p²} β_m v_m`, so `ζ`'s energy per `log N` tends to `Σ β_m² E_m(c)` (norm quasimodes),
which tends to `0` as `c → ∞` (`E_m(c) → 0`).

## Lean
`RAPT/EveryFlippedPrimeIsSeenAtLargeOverlap.lean`: `pairing_atomicTest`, `weilQuadTw_flip_sub_eq`,
`abs_flipWindow_le`, `tendsto_inner_sum_quasimodes`, `trial_eq_sqrt_log_smul`,
`eventually_flip_negative_of_energy`, `exists_flip_negative_at_every_large_overlap`,
`tiltedUnitSpline_flip_selective`. Axioms standard.

## Non-uniformity in `p`
At a fixed overlap the flip moves Weil's form by at most `(8 log p/√p) ∫ f²` (each lag pairing is
`≤ 2∫f²` by Cauchy–Schwarz), the atomic `L²` mass is `≤ (1 + 2c e^c)‖g‖² Σ x²`, and `ζ`'s form is
eventually `≥ (E(c)/2)‖g‖² Σ x²` (bottom of the spectrum). So every prime with
`8(1 + 2c e^c) log p/√p < E(c)/2` stays positive at overlap `c`: the threshold `c*(p)` is finite for
every `p ≥ 3` and unbounded in `p`. Lean: `RAPT/NoFixedOverlapSeesEveryFlip.lean`
(`eventually_flip_posDef_of_large_prime`, `tiltedUnitSpline_flip_threshold_finite_and_unbounded`).

## Open
The growth rate of `c*(p)`.

## Log
- 2026-10-30 — formalized; non-uniformity in `p` formalized.
