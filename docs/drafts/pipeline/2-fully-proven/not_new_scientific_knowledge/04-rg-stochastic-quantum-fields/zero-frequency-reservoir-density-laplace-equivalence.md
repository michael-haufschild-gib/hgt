# Zero-Frequency Reservoir Density Laplace Equivalence

- **ID:** zero-frequency-reservoir-density-laplace-equivalence
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / source-admissibility guardrail
- **Door grade:** BRIDGE (classical Laplace uniqueness; route-relevant, not a
  native C5 theorem)
- **Source:** `zero-frequency-repaired-source-dx-over-x-law.md`;
  `locally-infinite-repaired-frequency-source-for-compact-markov.md`
- **Statement:** In the compact Markov target case, the local logarithmic
  divergence of the forced zero-frequency repaired source sees only the target
  measure's total positive mass, while the full reservoir density against
  `dx/x` is Laplace-equivalent to the positive target measure.

## Purpose

The `dx/x` law shows that local integrability and local measure class cannot
select the RH target inside the additive repaired-frequency model. This card
identifies the next boundary: the leading local divergence is too coarse, but
the full reservoir density is not an independent source coordinate. It is a
Laplace transform of the target Markov measure after the change of variable
`r = y^(-1/2)`.

## Theorem

[PROVED HERE]

Let `nu` be a finite positive measure supported in `[0,R]`, not supported only
at `0`, and define

`S_k = int y^k dnu(y)`, for `k >= 1`.

Assume `mu` is a positive measure on `(0,infty)` with finite positive integer
moments and

`int x^k dmu(x) = (2k-1)! S_k`, for every `k >= 1`.

Let `nu_+` be the restriction of `nu` to `(0,R]`. Then:

1. `mu` is absolutely continuous with respect to `dx/x`, with density

   `h(x) = (1/2) int_(0,R] exp(-sqrt(x/y)) dnu(y)`.

2. If `m = nu_+((0,R])`, then

   `h(x) -> m/2` as `x -> 0+`,

   and for every fixed `delta > 0`,

   `mu((epsilon,delta)) / log(delta/epsilon) -> m/2`

   as `epsilon -> 0+`.

3. The full function `h(x)` for `x>0` determines `nu_+`. More precisely, if
   `tau` is the pushforward of `nu_+` under `y -> y^(-1/2)`, then

   `2 h(t^2) = int exp(-t r) dtau(r)`, for every `t>0`.

   Hence `2h(t^2)` is the Laplace transform of `tau`, and Laplace uniqueness
   recovers `tau`, hence `nu_+`.

## Proof

The `dx/x` law proves the exact representation

`int f(x) dmu(x)
 = int_(0,R] int_0^infty f(a y) exp(-sqrt(a)) da/(2a) dnu(y)`

for every nonnegative Borel function `f`. Changing variables `x = a y` in the
inner integral gives

`int f(x) dmu(x)
 = int_0^infty f(x)
     [(1/2) int_(0,R] exp(-sqrt(x/y)) dnu(y)] dx/x`.

This proves the density formula.

For each fixed `y>0`, `exp(-sqrt(x/y)) -> 1` as `x -> 0+`, and the integrand is
bounded by `1`. Dominated convergence gives

`h(x) -> (1/2) nu_+((0,R]) = m/2`.

Now write

`mu((epsilon,delta)) = int_epsilon^delta h(x) dx/x`.

Let `c=m/2`. For any `eta>0`, choose `epsilon_0>0` such that
`|h(x)-c|<=eta` for `0<x<epsilon_0`. Splitting
`(epsilon,delta)` into `(epsilon,min(delta,epsilon_0))` and a fixed remaining
interval shows that, after division by `log(delta/epsilon)`, the fixed interval
contributes `0` and the first interval lies between `c-eta` and `c+eta`.
Letting `eta -> 0` proves the logarithmic asymptotic.

Finally define `tau` as the pushforward of `nu_+` under `r=y^(-1/2)`. For
`t>0`,

`2 h(t^2) = int_(0,R] exp(-t y^(-1/2)) dnu(y)
          = int exp(-t r) dtau(r)`.

Thus the reservoir density is exactly the Laplace transform of `tau`. The
standard uniqueness theorem for Laplace transforms of finite positive measures
on `[0,infty)` determines `tau` from this transform on `t>0`. Since the map
`y -> y^(-1/2)` is injective on `(0,R]`, `tau` determines `nu_+`.

## Consequence For The RH Route

The zero-frequency reservoir has no useful local selection invariant between
measure class and full density:

1. Its local logarithmic divergence rate is only `nu_+((0,R])/2`. After fixing
   this scalar normalization, the leading local divergence is universal.
2. Its full density profile is not a softer source coordinate. It is
   equivalent, by Laplace transform, to the positive target Markov measure
   itself.

Therefore a repaired-frequency proof cannot define source admissibility by the
leading local blowup, and cannot treat the full reservoir density as independent
input. A valid source theorem must construct the density from Euler/Gamma/FE
data and then prove the required Markov/Pick positivity, or move to the
completed boundary/index object.

## Gates

- [x] 0 -> 1 in-progress: density representation isolated from the `dx/x`
  law.
- [x] 1 -> 2 fully-proven: local logarithmic asymptotic and Laplace
  equivalence proved.
- [ ] 2 -> 3 formalized: not formalized.

## Log

- 2026-06-24 -- Codex: created by changing representation from local measure
  comparison to Radon-Nikodym density and Laplace transform.

## 2026-06-24 complete-monotonicity admissibility equivalence

`reservoir-density-complete-monotonicity-markov-equivalence.md` classifies the analytic admissibility condition for the reservoir profile. With `H(t)=2h(t^2)`, compact positive Markov targets correspond exactly to finite Laplace transforms supported in `[a,infty)` for some `a>0`; equivalently, `H` is completely monotone with finite `H(0+)`, and `exp(a t)H(t)` is completely monotone for some `a>0`.

Thus complete monotonicity of the reservoir profile is not a weaker source condition. With the compact-support lower-bound condition, it is the Markov cone written in reservoir coordinates.
