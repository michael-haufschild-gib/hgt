# Only counting creates positivity; everything else in this corpus transports it

- **ID:** `positivity-creators-versus-transporters`
- **Stage:** 1-in-progress
- **Type:** SYNTHESIS / INVENTORY
- **Scientific status:** `[SYNTHESIS OF CORPUS STATE]` `[NOT NEW MATHEMATICS]` `[NOT AN RH PROOF]`
- **Follows:** `deninger-two-halves-do-not-compose.md` §10, which established that every route reachable
  by reformulation terminates at *"prove a positivity"*, and that the corpus already contains most of
  the reformulations.

## 1. The distinction the corpus has not drawn

A positivity statement can be reached in two ways, and the difference decides whether an argument can
ever close:

- a **transporter** moves positivity from one object to another. It needs a positive input and
  returns a positive output. Every equivalence is a transporter;
- a **creator** produces a nonnegative number from a construction, with no positive input.

Listing this corpus's positivity statements against that distinction is short and, I think, decisive.

## 2. Transporters — everything RH-adjacent in the tree

| statement | what it transports |
|---|---|
| Weil positivity | the conclusion, restated |
| `hdetects` (`DeningerArithmeticPositiveCalderonKoszul`) | assumed positivity of the Green energy |
| `psi(h, C h)` definite (the second Riemann bilinear relation) | assumed definiteness of the twist |
| `primeArchSourceMomentHankelDeterminantsPositive_iff_riemannHypothesis` | an equivalence |
| `positiveMomentForm_normalizedPrimeArchMoment_of_riemannHypothesis` | RH into the moment form |
| `primeArchInfiniteSupportMomentRepresentation_of_positiveMomentForm` | the moment form into a measure |
| CCM prime-window overshoot summability at abscissa `1` | an equivalence |
| inner-product/Gram positivity `⟪x,x⟫ ≥ 0` | the inner product, which *is* the positivity |

None of these creates anything. Each is correct, and each requires a positive input somewhere.

## 3. Creators, and their status here

- **Squares / Positivstellensatz.** Killed in the corpus with an explicit counterexample:
  `RHTower/ConePositivstellensatzFailure.lean` exhibits a witness nonnegative on `ℝ` whose cylinder
  lift is negative. Dead.
- **Variance.** `Var ≥ 0` is free, but RH is `Var = 0` (`no-boundary-selection-of-zeta` R25: RH is
  *zero radial spread*). Vanishing of a nonnegative form is a rigidity, not a positivity, and the free
  creator gives the useless direction. Dead as a creator for this target.
- **Measures and integrals.** `∫ f ≥ 0` needs `f ≥ 0`. Transporter in disguise.
- **Counting.** Dimensions, pole orders, multiplicities, cardinalities are nonnegative *by
  construction*. This is the only creator that survives.

## 4. The consequence

Over `𝔽_q`, Weil's proof uses exactly the surviving creator: degrees of effective divisors and
Riemann–Roch, i.e. `h⁰ ≥ 0`. Over `ℚ` the analogue is an arithmetic Riemann–Roch on an arithmetic
surface — the object Deninger's programme is trying to build and which
`deninger-two-halves-do-not-compose.md` identifies as missing.

> **Every RH route in this corpus needs a creator; the only creator is counting; and the counting
> mechanism that would apply is arithmetic Riemann–Roch on a space nobody has built.** That is why
> every route lands on the same wall, and it is a sharper statement than "the positivity is hard".

## 5. The residual question, and it is one I raised and never pursued

There **is** a counting mechanism available over `ℚ` already: **Rankin–Selberg**. The Selberg-class
invariant `n_F = ord_{s=1} R_{F,F}` is a pole order — nonnegative by construction, no positive input
— and `linear-kills-quadratic-survives` §4 names it as one of the corpus's two quadratic mechanisms.
The Selberg lane (working log, cycles 240–247) is the one place in this corpus producing new
*unconditional* theorems, and it runs on exactly this creator.

Its limitation is what it counts: `n_F` measures coefficient energy, not zeros. So:

> **Is there a Rankin–Selberg-type construction whose pole order counts off-critical-line zeros?**

That is the question the inventory leaves standing. It asks for a creator applied to the right
object, rather than another transporter, and it is the only formulation I reached in this session
that is neither pre-empted nor a restatement of the conclusion. I have not attempted it, and I do not
know that it is possible; an obvious obstruction is that pole orders of automorphic `L`-functions are
insensitive to the *location* of zeros, which is precisely the linear/quadratic gap
`linear-kills-quadratic-survives` documents. Recorded as the target, with that obstruction named in
advance.

## 6. Honest grade

The creator/transporter distinction is elementary and the inventory is bookkeeping. Its value is that
it converts "prove the positivity" — which is where every route in this corpus ends — into a
requirement that can be checked against a proposal in one line: *does it create, or does it move?*
Every RH-adjacent positivity in the tree moves. That is worth knowing before the next cycle spends
time on another equivalence.

## Gates

- [x] transporter/creator inventory of the corpus's positivity statements
- [x] squares route: dead in-corpus with an explicit counterexample
- [x] variance route: free in the useless direction
- [x] counting identified as the only surviving creator, and its `ℚ`-analogue named
- [ ] a Rankin–Selberg-type pole order counting off-line zeros
- [ ] independent audit (Codex)

## Log

- 2026-07-27 (Claude): written after eight connection-checks in one session returned seven
  pre-emptions, all landing on the same positivity. Rather than a ninth reformulation, classified the
  positivity statements themselves.

## 7. The residual question, worked and answered negatively

§5 asked: is there a Rankin–Selberg-type construction whose pole order counts off-critical-line
zeros? Working it rather than leaving it open:

**The count exists, and it is classical.** `N(sigma, T)` — the number of zeros with real part
`> sigma` up to height `T` — is a nonnegative integer, produced by counting, with no positive input.
It is a creator in the sense of §1, and RH is exactly `N(sigma, T) = 0` for every `sigma > 1/2`. So
the creator that would settle RH is not missing; it is the zero-density function, and bounding it
(`N(sigma,T) ≪ T^{c(1-sigma)} log T` and its descendants) is a century-old field that has never
reached zero.

**Rankin–Selberg does not reach it.** `n_F = ord_(s=1) R_(F,F)` is the divergence rate of
`sum_p |a_F(p)|^2 / p` — a second moment of the Satake data, averaged over primes, evaluated at one
point on the boundary of absolute convergence. It is a *factorization multiplicity*: it counts how
many primitive factors `F` has, weighted by their exponents. Zero **location** is not a function of
that datum, and the corpus's own `linear-kills-quadratic-survives` is the record of how thin the
invariants in this family are.

So the answer is: **no, as far as I can see.** The Rankin–Selberg creator counts the wrong object,
and the creator that counts the right object — `N(sigma,T)` — is not the pole order of any
constructible thing; it is extracted by contour integration of `zeta'/zeta`, which needs the zeros
one is trying to constrain.

I cannot prove that no such construction exists, and I am not claiming a no-go. What §5–§7 establish
is narrower and still worth having:

> The corpus contains exactly one creator that applies over `ℚ` (Rankin–Selberg pole orders), it
> counts factorization multiplicity, and factorization multiplicity does not see zero location. The
> creator that does see zero location is the classical zero-density function, which this corpus does
> not touch at all — `formal_tools.py research` returns nothing for zero-density counting, and there
> is no card.

## 8. Terminal state of this line, stated plainly

Every route reachable from this corpus by reformulation ends at a positivity; every positivity in the
corpus is a transporter; the only creator that survives is counting; the only counting creator
available over `ℚ` counts the wrong thing; and the counting creator that would count the right thing
is the classical zero-density problem, absent from this corpus and open for a century.

That is not a proof of impossibility and it is not a reason to stop. It is the accurate map, and its
practical content is the §6 test: **a proposal must create positivity, not move it.** Nothing in this
session — mine or, on the evidence of the cards I read, anyone's — creates any.

## Gates (final)

- [x] transporter/creator inventory
- [x] squares dead in-corpus; variance free in the useless direction
- [x] counting identified as the only surviving creator
- [x] §5's Rankin–Selberg candidate worked and answered negatively, with the reason
- [x] the creator that would work identified as `N(sigma,T)`, and confirmed absent from this corpus
- [ ] a construction realizing an off-line zero count as a pole order — open, and not claimed impossible
