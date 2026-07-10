# Locally Infinite Repaired-Frequency Source For Compact Markov Targets

- **ID:** locally-infinite-repaired-frequency-source-for-compact-markov
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / source-admissibility guardrail
- **Source:** `infinite-half-turn-frequency-source-admissibility-split.md`;
  `seam-log-markov-pick-rh-equivalence.md`
- **Statement:** For any compact Stieltjes/Markov target whose representing
  measure is not supported only at `0`, every positive half-turn
  repaired-frequency source realizing its positive moments has infinite mass in
  every neighborhood of frequency `0`.

## Goal

Strengthen the infinite repaired-frequency split. The earlier finite-mass
obstruction showed that a finite positive repaired-frequency source cannot
realize a compact Markov target with nonzero positive moments. This theorem
shows more: local finiteness at the zero-frequency border is already
impossible. Thus the zero-frequency reservoir is forced locally by the
factorial moment transform, not merely by a bad global choice of representing
source.

## Theorem

[PROVED HERE]

Let `nu` be a finite positive measure supported in `[0,R]`, not supported only
at `0`, and define

`S_k = int y^k dnu(y)`, for `k >= 1`.

Assume `mu` is a positive measure on `(0,infty)` with finite positive moments
and

`int x^k dmu(x) = (2k-1)! S_k`, for every `k >= 1`.

Then for every `delta > 0`,

`mu((0,delta)) = infinity`.

## Proof

Set

`dlambda(x) = x dmu(x)`.

Since `int x dmu(x) < infinity`, `lambda` is a finite positive measure on
`(0,infty)`. Its moments are

`int x^n dlambda(x) = int x^(n+1) dmu(x) = (2n+1)! S_(n+1)`.

The shifted factorial moment problem is determinate by the same Carleman
estimate used in `infinite-half-turn-frequency-source-admissibility-split.md`:
compact support gives `S_(n+1) <= C R^(n+1)`, so

`((2n+1)! S_(n+1))^(-1/(2n)) >= C'/n`

for all large `n`, and the Carleman series diverges.

One representing measure for these moments is

`lambda_0 = pushforward of lambda_base(a) x (y dnu(y)) under x = a y`,

where

`dlambda_base(a) = e^(-sqrt(a)) da/2`.

Indeed,

`int a^n dlambda_base(a) = (2n+1)!`,

so

`int x^n dlambda_0(x)
 = int (a y)^n y dlambda_base(a) dnu(y)
 = (2n+1)! S_(n+1)`.

By determinacy, `lambda = lambda_0`. Since `lambda = x mu`, on `(0,infty)`

`dmu(x) = x^(-1) dlambda_0(x)`.

Fix `delta > 0`. Because `nu` is not supported only at `0`, there is `eta > 0`
with `nu([eta,R]) > 0`. For `y in [eta,R]` and `0 < a < delta/R`, one has
`a y < delta`. Therefore

`mu((0,delta))
 >= int_(y in [eta,R]) int_(0<a<delta/R)
      (a y)^(-1) y dlambda_base(a) dnu(y)`

`= nu([eta,R]) int_0^(delta/R) e^(-sqrt(a)) da/(2a)
 = infinity`,

because the integrand is asymptotic to `1/(2a)` as `a -> 0+`.

Thus every zero-frequency neighborhood has infinite `mu`-mass.

## Consequence For The RH Route

The positive repaired-frequency model has only two remaining forms:

1. It permits locally infinite mass at frequency `0`; then a source theorem
   must explain why the Euler/Gamma/FE law selects exactly the needed border
   reservoir without using the target Markov positivity as input.
2. It requires local finiteness, Radon behavior, a finite border counterterm, or
   a finite-part mass at the zero-frequency endpoint; then it cannot realize
   even a compact Markov target not supported only at `0` through this model.

Therefore a source-built proof of the Markov/Pick cone cannot be recovered by
adding a finite border correction to the positive repaired-frequency expansion.
It must either supply a noncircular selection law for a locally infinite border
source or move to the completed boundary/index object.

## Gates

- [x] 0 -> 1 in-progress: local-finiteness loophole isolated inside the
  infinite repaired-source split.
- [x] 1 -> 2 fully-proven: determinate shifted-factorial representing measure
  and local divergence proof completed.
- [ ] 2 -> 3 formalized: measure-theoretic determinacy/local-divergence theorem
  not formalized.

## Log

- 2026-06-24 -- Codex: split from
  `infinite-half-turn-frequency-source-admissibility-split.md` after the
  monotone border audit.
