# Full differential-translation orbit freeness of a completed logarithmic derivative

- **ID:** `completed-logderiv-full-translation-orbit-freeness`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) — `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The full constant-coefficient differential-translation orbit of `xi'/xi` is
  free modulo the differential field of meromorphic functions DA over `C(s)`.  Equivalently,
  every nonzero finite combination

  `sum_(j,k) c_(j,k) D^k((xi'/xi)(s+h_j))`

  with arbitrary distinct complex shifts `h_j` is hypertranscendental.

## Goal

Upgrade one completion-stripping identity into a global constraint law.  A mixed completed
carrier has an archimedean mode that obstructs direct Dirichlet-series arguments.  If one fixed
translation filter removes that mode and leaves an arithmetically thick Dirichlet source, then
apply the same filter to every alleged DA relation among arbitrary translates.  The source filter
turns the relation into an exponential polynomial sampled on prime logarithms.  Prime-log sample
density prevents any nonzero finite stencil from erasing almost all primes.

This is a law about constrained HT carriers, not a flow: a single source-stripping constraint
forces the full translation representation to be free modulo DA.

## General source-stripping differential-orbit law

Let `K` be a differential field of meromorphic functions, stable under every translation.  Let
`u` be meromorphic.  Suppose there is a fixed nonzero translation polynomial `A(T)` such that

`A(T)u = r + sum_(n>=1) b_n n^(-s)`

on a right half-plane, where `r in K`, the series has finite abscissa of absolute convergence,
and the prime coefficients `b_p` are nonzero for all but finitely many primes.

Assume also the following sampling condition: for every nonzero exponential polynomial with
polynomial coefficients

`E(x)=sum_(j=1)^m P_j(x) exp(-h_j x)`, `P_j in C[x]`,

with distinct `h_j in C`, there are infinitely many primes `p` for which `E(log p)!=0`.

Then the differential translates `{D^k u(s+h):h in C, k>=0}` are linearly independent modulo
`K`, provided every ordinary Dirichlet series with infinitely many prime divisors in its nonzero
support lies outside `K`.

### Proof `[PROVED HERE]`

Suppose distinct `h_1,...,h_m` and polynomials

`P_j(D)=sum_k c_(j,k)D^k`,

not all zero, satisfy

`w(s)=sum_j P_j(D)u(s+h_j) in K`.

Translations commute, so stability of `K` gives

`A(T)w(s)=sum_j P_j(D)(A(T)u)(s+h_j) in K`.

Its non-Dirichlet part `sum_j P_j(D)r(s+h_j)` lies in `K`.  Termwise differentiation is valid
on a common right half-plane.  Subtracting the non-Dirichlet part leaves the ordinary
Dirichlet series

`sum_(n>=1) b_n E(log n)n^(-s)`,

where

`E(x)=sum_j P_j(-x) exp(-h_j x)`.

Distinct exponents make this polynomial-coefficient exponential polynomial nonzero.  By the sampling
hypothesis, `b_p E(log p)` is nonzero for infinitely many primes, so the filtered series lies
outside `K`.  This contradicts the preceding membership in `K`.  Therefore no relation exists.

## Prime-log sampling lemma

Every nonzero polynomial-coefficient exponential polynomial

`E(x)=sum_j P_j(x) exp(-h_j x)`

has `O(X)` zeros on the real interval `[0,X]`.

Indeed `E` is an entire function of exponential type up to a polynomial factor.  Choose `x_0`
with `E(x_0)!=0`; Jensen's formula on disks centered at `x_0`, together with
`log max_(|z-x_0|<=R)|E(z)|=O(R)+O(log R)=O(R)`, gives
`N_E(R)=O(R)` for its disk zero count.  The real zero count is no larger.

On the other hand, the number of prime samples `log p` in `[0,X]` is `pi(exp X)`, which is
asymptotic to `exp(X)/X` by the prime number theorem.  Hence the prime-log set cannot be contained,
up to finitely many points, in the zero set of `E`.  Infinitely many prime samples survive.

Only the lower bound `pi(exp X)/X -> infinity` faster than `X` is needed; Chebyshev's estimates
suffice in place of the full prime number theorem.

## Xi specialization

Let

`u=xi'/xi`, `T f(s)=f(s+2)`, and `A(T)=T-1`.

The exact identity formalized in
`formal/GaloisForLFunctions/RHTower/XiShiftPrimeExposure.lean` is

`(T-1)u = r + sum_(n>=2) Lambda(n)(1-n^(-2))n^(-s)`,

where

`r(s)=1/(s+2)+1/(s+1)-1/(s-1)`

is rational.  At every prime `p`,

`b_p=log(p)(1-p^(-2)) != 0`.

Take `K` to be the differential field of DA meromorphic functions over `C(s)`.  It is stable
under translations.  Ostrowski's theorem says an ordinary Dirichlet series in Reich's class `D`
with infinitely many prime divisors in its nonzero support is HT, hence lies outside `K`.
The general theorem and prime-log sampling lemma give:

**Theorem.** For distinct `h_1,...,h_m in C` and polynomials
`P_1,...,P_m in C[D]`, not all zero,

`sum_j P_j(D)(xi'/xi)(s+h_j)`

is hypertranscendental over `C(s)`.

### Immediate corollaries

1. `xi'/xi` is HT (one translate).
2. For every `h!=0`, `(xi'/xi)(s+h)-(xi'/xi)(s)` is HT.  Thus its exact DA translation
   stabilizer is `{0}`.
3. It satisfies no nontrivial finite constant-coefficient differential-difference equation with a
   DA forcing term, for any derivative orders and any collection of complex step sizes.
4. Its class in `Mer(C)/DA` generates a free module over the differential group algebra
   `C[D][C_add]`.
5. By logarithmic-derivative equivalence, `xi` itself is HT.

## Exact RH-route consequences

The theorem excludes every concrete implementation whose decisive carrier assertion is a finite
differential-translation stencil of `xi'/xi` with a DA, holonomic, or fixed finite algebraic-state
residual.  Derivative orders are unrestricted and the shift sizes may be arbitrary complex numbers
with no lattice hypothesis.  This includes finite translation/dilation-coordinate reductions
embedded inside Li, explicit-formula, spectral-trace, or canonical-system proposals when they make
that exact assertion.

It does not exclude the full Li, Weil, Nyman--Beurling, Hilbert--Polya, Connes, or de Branges routes.
Those criteria are infinite-dimensional or RH-equivalent and need not factor through a finite
translation stencil.

## Candidate competition

1. Even-shift polynomial freeness — proved but weaker; subsumed by this theorem.
2. Exact DA translation stabilizer `{0}` — two-translate corollary; significant but not the full
   orbit law.
3. Full arbitrary-shift orbit linear freeness — proved and subsumed by item 4.
4. Full differential-translation orbit linear freeness — proved here.
5. Nonlinear differential-algebraic independence of several orbit elements — not proved by the
   present linear filtering argument and not claimed.

## Attack list

- [x] Verify common half-plane convergence after arbitrary complex shifts: move sufficiently far
  right; finite shift sets preserve finite abscissa.
- [x] Verify the filtered coefficient at a prime is exactly
  `log(p)(1-p^(-2))E(log p)`.
- [x] Verify a nonzero exponential polynomial has `O(X)` real zeros by exponential type/Jensen.
- [x] Verify prime-log samples outgrow `O(X)` by Chebyshev/PNT.
- [x] Verify Ostrowski/Reich class `D` needs infinitely many prime divisors, not nonzero values at
  every prime.
- [x] Search exact literature: completed xi/logarithmic derivative, translation orbit modulo DA,
  and source-stripping arguments.
- [x] Apply the severe parent-theory gate.  The theorem is a routine synthesis of
  Ostrowski/Nagoshi, Chiang--Feng, Jensen zero count, and Chebyshev, so it is graded as a bridge
  despite the exact completed-logarithmic-derivative statement being absent from the searched
  corpus.
- [x] Determine whether the arbitrary-complex-shift scope exceeds Nagoshi's real-shift theorem in a
  scientifically non-mechanical way: it does not.  The exponential-polynomial sampling extension
  is short once the source stripper is present.
- [x] Inspect and strengthen the Lean substrate without pretending the analytic Ostrowski step is
  formalized.

## Primary parents already identified

- Ostrowski 1920 / Reich: infinite-prime-support Dirichlet series are HT.
- Nagoshi 2016: strong difference--differential independence for real translates of automorphic
  L-functions and class-`D` Dirichlet series.
- Chiang--Feng 2006: algebraic difference independence of the Riemann zeta function for arbitrary
  complex shifts over the small-growth meromorphic coefficient field.
- Classical zero counting for exponential polynomials of exponential type.
- Chebyshev/PNT lower bounds for prime density.

## Novelty verdict

`[NOVELTY VERDICT: FAIL]`.  The arbitrary-complex differential-translation statement is stronger
than the real-shift scope printed in Nagoshi, and no exact theorem for `xi'/xi` was located.
Nevertheless, the proof is generated directly by four standard parents: the already exposed
Dirichlet source, Ostrowski's class-`D` obstruction, linear independence and Jensen zero counting
for exponential polynomials, and prime density.  Chiang--Feng already demonstrates that arbitrary
complex zeta shifts are the natural difference-independence scope.  The result is therefore a
useful fully proved route boundary, but not genuinely new scientific knowledge under the project's
routine-parent test.

## Formalization status

The exact source-stripping identity is fully formalized in
`formal/GaloisForLFunctions/RHTower/XiShiftPrimeExposure.lean`.  The full theorem here is not at
stage 3: its proof requires an analytic Ostrowski/Reich theorem, exponential-polynomial zero
counting, and prime-density input not formalized in the local tree.  Moving only the algebraic
shell would violate the pipeline's full-claim rule.

## Log

- 2026-07-11 -- Opened after the even-shift augmentation law.  The fixed `T_2-1` source stripper
  converts every arbitrary-shift relation into a prime-log sampled exponential polynomial.
- 2026-07-11 -- Strengthened from translates to arbitrary finite mixtures of derivatives and
  translates.  The coefficient filter becomes a polynomial-coefficient exponential polynomial,
  whose real zero count is still `O(X)`.
- 2026-07-11 -- Exact parent audit found Nagoshi's real-shift difference--differential theorem and
  Chiang--Feng's arbitrary-complex zeta difference theorem.  The remaining extension is routine;
  novelty fails and the complete paper theorem is filed as a stage-2 bridge.
