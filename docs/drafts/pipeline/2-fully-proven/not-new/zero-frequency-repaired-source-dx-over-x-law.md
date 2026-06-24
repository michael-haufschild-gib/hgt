# Zero-Frequency Repaired Source `dx/x` Law

- **ID:** zero-frequency-repaired-source-dx-over-x-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / source-admissibility guardrail
- **Door grade:** BRIDGE (classical measure comparison; route-relevant, not a
  native C5 theorem)
- **Source:** `locally-infinite-repaired-frequency-source-for-compact-markov.md`;
  `zero-frequency-repaired-source-mellin-threshold.md`
- **Statement:** For compact Markov targets not supported only at `0`, the
  forced positive repaired-frequency source has local weighted integrability
  exactly equivalent to integrability against `dx/x` at zero frequency.

## Purpose

The Mellin-threshold card shows that positive powers are too weak and local
finiteness is too strong. This theorem gives the whole local weighted
integrability scale. Any proposed source-admissibility selector based only on
local weighted finiteness near zero frequency is now classified: it either
passes the arbitrary reservoir automatically or rejects the compact Markov
targets themselves.

## Theorem

[PROVED HERE]

Let `nu` be a finite positive measure supported in `[0,R]`, not supported only
at `0`, and define

`S_k = int y^k dnu(y)`, for `k >= 1`.

Assume `mu` is a positive measure on `(0,infty)` with finite positive integer
moments and

`int x^k dmu(x) = (2k-1)! S_k`, for every `k >= 1`.

Then for every `delta > 0` and every nonnegative Borel function `w` on
`(0,delta)`,

`int_(0,delta) w(x) dmu(x) < infinity`

if and only if

`int_0^delta w(x) dx/x < infinity`.

More quantitatively, for every `eta > 0` with `nu([eta,R]) > 0`,

`(nu([eta,R])/2) exp(-sqrt(delta/eta)) int_0^delta w(x) dx/x`

`<= int_(0,delta) w(x) dmu(x)`

`<= (nu((0,R])/2) int_0^delta w(x) dx/x`.

## Proof

As in the local-infinity theorem, set

`dlambda(x) = x dmu(x)`.

Then `lambda` is finite and has moments

`int x^n dlambda(x) = (2n+1)! S_(n+1)`, for `n >= 0`.

Compact support of `nu` gives Carleman determinacy. The representing measure is

`lambda_0 = pushforward of lambda_base(a) x (y dnu(y)) under x = a y`,

where

`dlambda_base(a) = exp(-sqrt(a)) da/2`.

Therefore `lambda = lambda_0`, and since `lambda = x mu`,

`dmu = x^(-1) dlambda_0`.

Equivalently, for every nonnegative Borel function `f`,

`int f(x) dmu(x)
 = int_(0,R] int_0^infty f(a y) exp(-sqrt(a)) da/(2a) dnu(y)`.

Apply this with `f = w 1_(0,delta)` and change variables `x = a y` in the
inner integral. Tonelli's theorem gives

`int_(0,delta) w(x) dmu(x)`

`= (1/2) int_(0,R] int_0^delta
      w(x) exp(-sqrt(x/y)) dx/x dnu(y)`.

Since `0 < exp(-sqrt(x/y)) <= 1`, the upper bound follows:

`int_(0,delta) w(x) dmu(x)
 <= (nu((0,R])/2) int_0^delta w(x) dx/x`.

Because `nu` is not supported only at `0`, there is `eta > 0` with
`nu([eta,R]) > 0`. For `0 < x < delta` and `y in [eta,R]`,

`exp(-sqrt(x/y)) >= exp(-sqrt(delta/eta))`.

Restricting the last double integral to `y in [eta,R]` gives the lower bound:

`int_(0,delta) w(x) dmu(x)`

`>= (nu([eta,R])/2) exp(-sqrt(delta/eta))
    int_0^delta w(x) dx/x`.

The two bounds prove the equivalence of finiteness.

## Consequence For The RH Route

Local weighted integrability at the zero-frequency border has no hidden
selecting power inside the positive repaired-frequency model. A condition

`int_(0,delta) w dmu < infinity`

is automatic for every compact Markov target exactly when `w in L^1(dx/x)` near
zero. If `w` is not in `L^1(dx/x)`, the same condition rejects every compact
Markov target not supported only at `0`.

Thus the source-admissibility law cannot be a local weighted finiteness
condition at zero frequency. It must either:

1. select a particular locally infinite `dx/x`-singular reservoir by source
   structure beyond weighted integrability; or
2. abandon the additive repaired-frequency source model for the completed
   boundary/index object.

## Relation To The Mellin Threshold

Taking `w(x)=x^q` recovers
`zero-frequency-repaired-source-mellin-threshold.md`: `x^q` lies in
`L^1(dx/x)` near zero exactly for `q>0`.

## Gates

- [x] 0 -> 1 in-progress: local weighted-integrability selector isolated.
- [x] 1 -> 2 fully-proven: exact `dx/x` comparison proved from the determinate
  shifted-factorial representing measure.
- [ ] 2 -> 3 formalized: not formalized.

## Log

- 2026-06-24 -- Codex: created as the weighted-integrability strengthening of
  the Mellin-threshold card.

## Corollary: local measure-class nonselection

[PROVED HERE]

Let `nu_1` and `nu_2` be two finite positive compact Markov target measures,
neither supported only at `0`, and let `mu_1`, `mu_2` be positive
half-turn repaired-frequency sources realizing their positive moments. Then for
every `delta>0` there are constants `0<c_delta<=C_delta<infinity` such that for
every Borel set `E subset (0,delta)`,

`c_delta mu_2(E) <= mu_1(E) <= C_delta mu_2(E)`.

Indeed, the theorem gives constants `0<a_i<=b_i<infinity` such that, on
`(0,delta)`,

`a_i int_E dx/x <= mu_i(E) <= b_i int_E dx/x`.

Thus

`(a_1/b_2) mu_2(E) <= mu_1(E) <= (b_1/a_2) mu_2(E)`.

Consequently all compact-target repaired reservoirs have the same local
measure class at zero, and even the same local bounded-equivalence class.

## Consequence For Source Selection

A source-admissibility predicate that depends only on the local null sets,
local absolute-continuity class, or bounded-density equivalence class of the
zero-frequency reservoir cannot select the RH target inside this model. It has
the same value on every compact Markov target not supported only at `0`.

Therefore the source selector, if it stays inside the additive positive
repaired-frequency model, must use data beyond local border measure class:
for example a nonlocal transform, exact Euler/Gamma/FE coupling, global moment
constraints, or a completed boundary/index object.

## 2026-06-24 density/Laplace strengthening

`zero-frequency-reservoir-density-laplace-equivalence.md` strengthens this local comparison by changing representation. The repaired source has density

`h(x)=(1/2) int_(0,R] exp(-sqrt(x/y)) dnu(y)`

with respect to `dx/x`. Thus `h(x)->nu((0,R])/2` as `x->0+`, and

`mu((epsilon,delta))/log(delta/epsilon) -> nu((0,R])/2`.

The full density profile is not independent source data: after `x=t^2`, `2h(t^2)` is the Laplace transform of the pushforward of `nu|_(0,R]` by `y->y^(-1/2)`, so it determines the positive target measure.
