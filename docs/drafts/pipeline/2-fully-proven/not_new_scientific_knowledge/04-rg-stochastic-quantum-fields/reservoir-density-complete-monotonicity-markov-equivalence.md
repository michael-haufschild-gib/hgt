# Reservoir Density Complete-Monotonicity Markov Equivalence

- **ID:** reservoir-density-complete-monotonicity-markov-equivalence
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / source-admissibility guardrail
- **Door grade:** BRIDGE (Bernstein/Laplace characterization; route-relevant,
  not a native C5 theorem)
- **Source:** `zero-frequency-reservoir-density-laplace-equivalence.md`;
  `seam-log-markov-pick-rh-equivalence.md`
- **Statement:** A zero-frequency reservoir density comes from a compact
  positive Markov target exactly when its square-root profile is a finite
  Laplace transform with support bounded away from `0`. Equivalently, the
  natural complete-monotonicity admissibility test is the Markov cone in
  reservoir coordinates.

## Purpose

After the `dx/x` and density/Laplace cards, the tempting escape is to ask for a
soft analytic property of the reservoir profile, such as complete monotonicity.
This theorem shows that the soft property is not softer once the compact-support
condition is included. It is exactly the positive Markov target after the change
of variables `x=t^2`, `r=y^(-1/2)`.

## Theorem

[PROVED HERE, using the Bernstein theorem for completely monotone functions]

Let `h : (0,infty) -> [0,infty)` and set

`H(t) = 2 h(t^2)`.

The following are equivalent.

1. There is a finite positive measure `nu` on `[0,R]` for some `R<infinity`,
   with `nu_+=nu|_(0,R]`, such that

   `h(x) = (1/2) int_(0,R] exp(-sqrt(x/y)) dnu(y)`.

2. There is `a>0` and a finite positive measure `tau` supported on
   `[a,infty)` such that

   `H(t) = int_[a,infty) exp(-t r) dtau(r)`.

3. `H` is completely monotone on `(0,infty)`, `lim_(t->0+) H(t)<infinity`,
   and for some `a>0`, the function

   `t -> exp(a t) H(t)`

   is completely monotone on `(0,infty)`.

Under these equivalent conditions, `tau` is the pushforward of `nu_+` under
`y -> y^(-1/2)`, and `nu_+` is the pushforward of `tau` under `r -> r^(-2)`.

## Proof

`1 -> 2`.
Assume `nu` is supported in `[0,R]`. Let `tau` be the pushforward of `nu_+`
under

`r = y^(-1/2)`.

Since `0<y<=R`, the support of `tau` lies in `[R^(-1/2),infty)`. For `t>0`,

`H(t)=2h(t^2)
    = int_(0,R] exp(-t y^(-1/2)) dnu(y)
    = int exp(-t r) dtau(r)`.

Thus `2` holds with `a=R^(-1/2)`.

`2 -> 1`.
Assume `tau` is finite positive and supported on `[a,infty)`. Let `nu_+` be
the pushforward of `tau` under

`y = r^(-2)`.

Then `nu_+` is a finite positive measure supported in `(0,a^(-2)]`. Put any
finite nonnegative atom at `0` if desired; it is invisible to the displayed
positive-moment reservoir. For `x>0`,

`(1/2) int exp(-sqrt(x/y)) dnu_+(y)
 = (1/2) int exp(-sqrt(x r^2)) dtau(r)
 = (1/2) int exp(-sqrt(x) r) dtau(r)
 = h(x)`.

So `1` holds.

`2 -> 3`.
A finite positive Laplace transform is completely monotone by differentiating
under the integral:

`(-1)^n H^(n)(t)=int r^n exp(-tr) dtau(r) >= 0`.

Also `lim_(t->0+)H(t)=tau([a,infty))<infinity`. If `tau` is supported on
`[a,infty)`, define the shifted finite measure `sigma` by pushing `tau` forward
under `r -> r-a`. Then

`exp(a t)H(t)=int exp(-t(r-a)) dtau(r)
             =int exp(-t u) dsigma(u)`,

so `exp(a t)H(t)` is completely monotone.

`3 -> 2`.
If `exp(a t)H(t)` is completely monotone and has finite limit at `0+`, the
Bernstein theorem gives a finite positive measure `sigma` on `[0,infty)` with

`exp(a t)H(t)=int exp(-t u) dsigma(u)`.

Let `tau` be the pushforward of `sigma` under `u -> u+a`. Then `tau` is finite
positive, supported on `[a,infty)`, and

`H(t)=int exp(-t(u+a)) dsigma(u)
     =int exp(-t r) dtau(r)`.

This proves `2`, and hence all equivalences.

The pushforward identifications follow from the injective inverse maps
`y -> y^(-1/2)` on `(0,R]` and `r -> r^(-2)` on `[a,infty)`.

## Consequence For The RH Route

Reservoir-profile admissibility has no middle layer here.

- Local measure class, local weighted finiteness, and leading logarithmic
  blowup are too weak.
- The full density profile, or complete monotonicity of `H(t)=2h(t^2)` with the
  compact-support lower-bound condition, is exactly the positive Markov target
  in another coordinate.

Therefore a source proof cannot take complete monotonicity of the reservoir
profile as an independent axiom. It must derive that complete monotonicity from
Euler/Gamma/FE source constraints, or leave the additive reservoir model for
the completed boundary/index object.

## Gates

- [x] 0 -> 1 in-progress: complete-monotonicity admissibility escape isolated.
- [x] 1 -> 2 fully-proven: Bernstein/Laplace equivalence proved.
- [ ] 2 -> 3 formalized: not formalized.

## Log

- 2026-06-24 -- Codex: created after the density/Laplace card to classify the
  complete-monotonicity version of reservoir admissibility.
