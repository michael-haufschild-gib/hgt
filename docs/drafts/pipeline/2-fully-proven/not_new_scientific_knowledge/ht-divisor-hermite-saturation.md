# Divisor-Hermite saturation by hypertranscendental functions

- **ID:** ht-divisor-hermite-saturation
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) — `[BRIDGE]`; scientifically not new
- **Source:** whole-class hypertranscendence program; `finite-jet-nonidentifiability-ht`;
  `asymptotic-flat-ht-invisibility`; exponential-perturbation literature; Weierstrass interpolation
- **Statement:** Let `S subset C` be discrete, let `m : S -> N`, and let `g` be a nonzero meromorphic
  function holomorphic at every point of `S`. Then the observation fiber

  `F(g;S,m) = {f : div(f)=div(g) and f^(j)(a)=g^(j)(a) for a in S, 0<=j<=m(a)}`

  contains continuum many functions hypertranscendental over `C(z)`. If `g` is differentially
  algebraic, the same fiber contains the DA function `g` and continuum many HT functions. The
  discreteness/sitewise-finite hypothesis is sharp by the identity theorem.

## Goal

Determine how much global analytic constraint data can be fixed while hypertranscendence remains
undetectable. Earlier work proves blindness for finite jets, finite continuous-linear observations,
and complete one-ray asymptotic profiles. This theorem crosses the finite/infinite boundary: it fixes
the complete zero-pole divisor globally and arbitrarily high, but finite, jets at every site of an
arbitrary discrete set.

The object is the observation fiber `F(g;S,m)`, not a generating flow. The construction moves only
by zero-free multiplicative gauges, so the prescribed divisor is fixed identically.

## Medalist lens

- `[SEARCH]` The DA meromorphic functions over `C(z)` form a differential field and differential
  algebraicity is transitive.
- `[SEARCH]` Hölder implies `H0=1/Gamma` is an entire HT function.
- `[SEARCH]` Weierstrass products realize arbitrary locally finite zero sets with prescribed finite
  multiplicities.
- `[BRIDGE]` Exponential perturbations `f exp(h)` are a known theme (Bank; Huang-Ng).
- `[BRIDGE]` A one-parameter exponential gauge has at most one DA member when its exponent is HT;
  this is the rank-one coset selection theorem formalized separately.
- `[BRIDGE]` Nesting the selection theorem with a Weierstrass product yields simultaneous saturation
  of a complete divisor and infinitely many local Hermite conditions.
- `[BRIDGE]` The identity theorem proves that the discrete/sitewise-finite channel is the sharp
  boundary: an accumulation set of value constraints or one full germ collapses the fiber.

## Candidate competition and eliminations

1. Differential-dependence matroids of HT tuples — `[BRIDGE]`; standard differential-algebraic
   pregeometry.
2. Constraint cocycles under argument automorphisms — `[BRIDGE]`; difference Galois/group
   cohomology.
3. Universal representable dependency patterns among HT functions — `[BRIDGE]`; direct basis
   construction.
4. Exponential-gauge affine-coset classification — `[BRIDGE]`; after erasing the vocabulary it is
   the preimage-of-a-subgroup theorem plus the logarithmic derivative.
5. Full divisor plus discrete Hermite fiber — rejected as scientific novelty. It is a clean
   cross-parent corollary, but once posed its proof is routine from differential-field selection and
   Weierstrass interpolation.

## Lemma 1 — one-exception exponential pencil `[PROVED HERE, BRIDGE]`

Let `H` be entire and HT over `C(z)`, and let `0 != q` be meromorphic. Then

`E(q,H) = {c in C : q exp(cH) is DA over C(z)}`

has at most one element.

### Proof

If distinct `c,d` belonged to `E(q,H)`, field closure would give

`exp((c-d)H) = (q exp(cH))/(q exp(dH))`

DA. Its logarithmic derivative `(c-d)H'` would be DA. Since `c-d != 0`, `H'` would be DA; shifting
a differential polynomial for `H'` by one derivative gives a differential polynomial for `H`,
contradicting hypertranscendence. ∎

If `q` is DA, then `0 in E(q,H)`, so `E(q,H)={0}` and every nonzero parameter gives an HT member.

## Lemma 2 — an HT entire function with prescribed discrete zeros `[PROVED HERE]`

Let `S subset C` be discrete and let `r : S -> N` be positive. There exists an entire HT function
`H` whose zero at each `a in S` has order at least `r(a)`.

### Proof

Choose a nonzero entire Weierstrass product `W` with the prescribed zero multiplicities. Fix
`H0=1/Gamma`, which is entire and HT. By Lemma 1, at most one `t in C` makes

`W exp(t H0)`

DA. Choose any other `t` and put `H=W exp(tH0)`. The exponential factor is zero-free, so the zeros
and their multiplicities are those prescribed through `W`; the choice of `t` makes `H` HT. ∎

This lemma is already stronger than multiplying `1/Gamma` by a polynomial: the prescribed set may
be any infinite discrete set and the required orders may be unbounded along it.

## Main theorem — divisor-Hermite saturation `[PROVED HERE, BRIDGE]`

Let `S`, `m`, and `g` be as in the statement. Choose the HT entire function `H` from Lemma 2 with

`ord_a(H) >= m(a)+1`

for every `a in S`. For `c in C`, define

`f_c = g exp(cH)`.

Every `f_c` has exactly the divisor of `g`, because `exp(cH)` is entire and nowhere zero. By Lemma 1,
all but at most one `f_c` are HT.

At each `a in S`,

`exp(cH)-1 = O((z-a)^(m(a)+1))`.

Since `g` is holomorphic at `a`,

`f_c-g = g(exp(cH)-1) = O((z-a)^(m(a)+1))`.

Therefore `f_c^(j)(a)=g^(j)(a)` for `0<=j<=m(a)`. Removing at most one parameter from `C` leaves
continuum many HT functions in `F(g;S,m)`. If `g` is DA, `f_0=g` is DA and every `f_c` with `c != 0`
is HT. ∎

## Corollaries `[PROVED HERE]`

1. **Every divisor supports continuum many HT functions.** Every meromorphic divisor on `C` is
   principal by Weierstrass/Mittag-Leffler; apply the theorem with `S=empty`.
2. **Zero-free saturation.** Taking `g=1` gives continuum many zero-free entire HT functions matching
   the constant `1` to arbitrary finite order at every point of any discrete `S`.
3. **Unbounded observation depth.** The orders `m(a)` may tend to infinity along `S`; only each
   individual order must be finite.
4. **DA/HT indistinguishability.** Whenever the base `g` is DA, one globally infinite observation
   record—complete divisor plus the whole discrete Hermite table—has both a DA representative and
   continuum many HT representatives.
5. **Divisor invariants fail maximally.** Any proposed HT invariant factoring through the meromorphic
   divisor, even after adjoining arbitrary sitewise-finite data on a discrete set, cannot detect HT.

## Sharpness `[PROVED HERE]`

The theorem cannot replace `S` by a set with an accumulation point in `C`. If two holomorphic
functions agree in value on such a set, the identity theorem makes them equal on the connected
domain. It also cannot prescribe an infinite jet at one point: equality of the full Taylor germ
again forces equality.

Thus "arbitrary discrete sites, arbitrary finite order at each site" is the maximal independent
local observation channel. The theorem saturates that entire channel while also fixing the complete
global divisor.

## Scientific-novelty verdict

The scientific-novelty gate fails. The statement is useful and the observation channel is global,
but the proof is a routine composition of established differential-field closure, exponential
perturbation, Weierstrass products, and the identity theorem. Absence from the checked corpus is not
evidence of scientific novelty, and a capable assistant can derive the result once the exact
formulation is supplied. Retain only as a gatekeeper bridge: future native invariants must use data
not factored through this saturated observation channel.

## Formal status

The algebraic selection mechanism is formalized and imported through
`GaloisForLFunctions.ExponentialGaugeSelection`:

- `exceptionalParameters_eq_relationCoset`
- `exceptionalParameters_subsingleton`
- `exceptionalParameters_eq_empty_or_singleton_or_univ`

The narrow Lean file check, module build, and formal lint pass. The concrete analytic layer—the DA
field of meromorphic functions, Hölder's theorem, Weierstrass products, orders of zeros, and Hermite
jet preservation—is not yet available in the Lean tree, so this card remains at stage 2 rather than
misgrading the bridge formalization as a formalization of the new theorem.

## Gates

- [x] 0 -> 1: well-posed observation fiber, deterministic attack, parent reductions
- [x] 1 -> 2: complete proof and sharp boundary; scientific-novelty gate explicitly failed
- [ ] 2 -> 3: formalize the concrete meromorphic/entire specialization and the two nested
  Weierstrass-gauge applications
- [ ] 3 -> 4: comprehensive bibliography and standalone paper

## Sources and source boundary

- Huang and Ng, *Hypertranscendency of Perturbations of Hypertranscendental Functions*, JMAA 491
  (2020), arXiv:2007.10037: perturbation parent and the differential-field property of DA functions.
- Bank's 1977/1980 work, as summarized by Huang-Ng: `Gamma exp(h)` and the role of zeros/poles are
  existing questions.
- Marques, *On the arithmetic nature of hypertranscendental functions at complex points*, Expo.
  Math. 29 (2011): uncountably many HT interpolation constructions for arithmetic exceptional sets,
  adjacent but not the fixed-divisor/discrete-Hermite fiber.
- Hölder's theorem, the Weierstrass product theorem, Mittag-Leffler, and the identity theorem are
  classical inputs.

## Log

- 2026-07-10 — deterministic candidate competition; proved the divisor-Hermite saturation theorem,
  then downgraded it to `[BRIDGE]` because it is a routine cross-parent corollary rather than new
  scientific knowledge; no numerical or random-search discovery.
