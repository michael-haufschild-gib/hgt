# FCRJ active prime-weight Mertens ultraviolet bound

- **ID:** FCRJ-APWMUB
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (paper-proven; Lean implementation complete, lint promotion pending)
- **Source:** `critical-multiplicative-compensated-cancellation-rh.md` · Conjecture loop 65
- **Statement:** Activity localizes every selected prime below `exp k`; elementary Mertens control
  removes finite-set weight `W` from raw FCRJ ultraviolet bound.

## Goal

For nonempty active packet prove

```text
W <= k + log 4.                                         (MW1)
```

For arbitrary finite active packet, `A>0`, `N>=1`, prove

```text
N sum_(n>N)|a_n|^2
  <= (2A/pi) N(k-m)(k+log 4)^2.                         (MW2)
```

## Gates

- [x] 0 → 1 in-progress: corpus search, primary-literature audit, frozen source statement
- [x] 1 → 2 fully-proven: dependency-closed paper proof and hostile constant audit
- [x] 2 → 3 formalized: exact Lean theorem, direct check, targeted build, and standard-axiom audit; global lint blocked only by unrelated modules
- [ ] 3 → 4 publication-ready: independent expert priority review

## Corpus frontier `[CORPUS]`

1. Active endpoint definitions imply `0<end<=k-log p`, hence `log p<k` and `p<exp k`.
2. `mertens_first_upper` proves symbolically
   `sum_(p<=n) log p/p <= log n + log 4`.
3. Loop 64 proves raw tail `<= (2A/pi)N(k-m)W^2`.
4. Corpus search found no theorem combining physical activity with Mertens mass to eliminate `W`.

## External frontier `[LITERATURE]`

Mertens' first upper bound and exponential support localization are classical. Targeted search found
no clipped prime-log FCRJ formula `(MW1)--(MW2)`. Novelty claim is restricted to coefficient-faithful
source specialization and exact moving-scale obstruction.

## Conjecture loop A — uniform `W` bound

`[FALSE]` Physical endpoint weights are not summable over all primes; corpus formally proves this.
Any `W` bound must retain active upper endpoint `k`.

## Conjecture loop B — activity-localized Mertens law

`[PAPER-PROVED] [LEAN-PROVED] [POSITIVE SURVIVOR]` `(MW1)--(MW2)` hold.

### Paper proof plan

Let `n=floor(exp k)`. Activity gives every selected prime `p<=n`, and nonemptiness gives `n>=1`.
Embed selected primes into all primes at most `n`; positivity and `mertens_first_upper` give
`W<=log n+log 4`. Since `n<=exp k`, `log n<=k`, proving `(MW1)`. Square `(MW1)` and substitute into
loop-64 bound. Empty packet has zero amplitude and is handled separately, proving `(MW2)` without a
nonemptiness premise.

### Hostile audit

- Nonemptiness is necessary for `(MW1)` when `k+log 4<0`; `(MW2)` handles empty packet directly.
- No PNT/asymptotic estimate is used; only corpus elementary Mertens upper law.
- Activity is used only for literal support localization and existing differentiation identity.
- `(MW2)` still requires moving-scale `N(k-m)(k+log 4)^2 -> 0`.

## Open core

Lean implementation is complete in
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeEndpointActiveMertensUltravioletEnergy.lean`.
Direct checking, targeted build, axiom audit, and umbrella wiring pass; capstones depend only on
`propext`, `Classical.choice`, and `Quot.sound`. Global lint remains blocked by unrelated concurrent
unwired modules, so Stage-3 promotion is withheld. Remaining moving-scale source condition is
`N(k-m)(k+log 4)^2 -> 0`.
