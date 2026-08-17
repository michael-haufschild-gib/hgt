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

Fully formalized.  The three inputs that were missing from the local tree — an analytic
class-`D` hypertranscendence criterion applicable after filtering, exponential-polynomial zero
counting, and the prime-density comparison — are now Lean theorems; see the Lean formalization
section below.

## Log

- 2026-07-11 -- Opened after the even-shift augmentation law.  The fixed `T_2-1` source stripper
  converts every arbitrary-shift relation into a prime-log sampled exponential polynomial.
- 2026-07-11 -- Strengthened from translates to arbitrary finite mixtures of derivatives and
  translates.  The coefficient filter becomes a polynomial-coefficient exponential polynomial,
  whose real zero count is still `O(X)`.
- 2026-07-11 -- Exact parent audit found Nagoshi's real-shift difference--differential theorem and
  Chiang--Feng's arbitrary-complex zeta difference theorem.  The remaining extension is routine;
  novelty fails and the complete paper theorem is filed as a stage-2 bridge.

## Lean formalization — 2026-08-17

`formal/GaloisForLFunctions/RHTower/XiTranslationOrbitFreeness.lean`, resting on
`formal/GaloisForLFunctions/RHTower/PrimeSourceCancellationBudget.lean` and the three modules it
introduced.  Every theorem below is unconditional
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`).

| Paper step | Lean name |
|---|---|
| the filter `L = ∑ⱼ Pⱼ(D) T_{hⱼ}` acting on the carrier | `RHTower.upperEndOrbitCombination` |
| `L` is additive and commutes with every translation | `upperEndOrbitCombination_add`, `upperEndOrbitCombination_sub`, `upperEndTranslationMeroEquiv_orbitCombination` |
| `L` preserves differential algebraicity | `differentialAlgebraicOver_upperEndOrbitCombination` |
| `L` acts on a Dirichlet carrier by coefficient scaling | `upperEndOrbitCombination_finiteAbscissaLSeries`, `orbitSource_eq_filteredSource` |
| the filtered coefficient at `n` is `b_n E_L(log n)` | `PrimeCancellation.filterAction`, `PrimeCancellation.filterSymbol` |
| prime-log sampling lemma (`O(X)` zeros on `[0,X]`) | `HTGeometry.CExpPoly.exists_zeroCount_linear`, `PrimeCancellation.exists_cancelledPrimes_count_le_log` |
| distinct exponents make `E_L` nonzero | `HTGeometry.CExpPoly.exists_cexpFn_ne_zero` |
| prime samples outgrow the zero count (Chebyshev) | `RHTower.exists_chebyshev_primeLog_count_gt_linear`, used through `PrimeCancellation.eq_zero_of_exponentialType_of_cofinite_primeLog_zeros` |
| infinitely many prime samples survive | `PrimeCancellation.infinite_survivingPrimes` |
| class-`D` step: the filtered source is HT | `PrimeCancellation.filteredSource_differentialIndependent`, `RHTower.xiFilteredUpperEndCarrier_hypertranscendentalOver` |
| the source-stripping identity `(T−1)u = r + F` | `RHTower.xiLogDerivRotatedUpperEnd_translation_defect` (pre-existing) |
| **Theorem** (all blocks nonzero) | `RHTower.xiLogDerivRotatedUpperEndCarrier_orbitCombination_hypertranscendentalOver` |
| **Theorem** (blocks not all zero) | `RHTower.xiLogDerivRotatedUpperEndCarrier_orbitCombination_hypertranscendentalOver'` |
| corollary 1, `xi'/xi` is HT | `RHTower.xiLogDerivRotatedUpperEndCarrier_hypertranscendentalOver` (pre-existing) |
| corollary 2, trivial DA translation stabilizer | `RHTower.xiLogDerivRotatedUpperEndCarrier_translation_difference_hypertranscendentalOver` |
| corollary 3, no finite differential-difference equation with DA forcing | `RHTower.xiLogDerivRotatedUpperEndCarrier_orbitCombination_not_differentialAlgebraic` |
| corollary 4, freeness of the orbit modulo DA | the same theorem: no nonzero filter lands in the DA field |
| corollary 5, `xi` is HT | `RHTower.xiRotatedUpperEndCarrier_hypertranscendentalOver` (pre-existing) |

Four notes on the formal route.

1. **Coordinates.**  The corpus realizes the carrier in the upper-end meromorphic field after the
   rotation `s = -I z`.  There the Dirichlet shift `s ↦ s + a` is translation by `I·a`
   (`finiteAbscissaLSeriesToUpperEndGerm_dirichletShift`) and `d/ds = I·δ`.  A polynomial in `d/ds`
   is therefore exactly a polynomial in `δ` after the invertible coefficient rescaling
   `c_k ↦ I^k c_k`, so quantifying over all nonzero polynomial blocks in `δ` is quantifying over
   all nonzero polynomial blocks in `d/ds`.  The rescaling is carried explicitly by
   `RHTower.dirichletTwist` when the filter is pushed onto the arithmetic source.
2. **The class-`D` step is proved, not cited.**  The card cites Ostrowski/Reich.  The formal proof
   instead runs the corpus's prime-valuation leading-echelon law, which had to be weakened from
   "nonzero private coefficient at every prime" to "at infinitely many primes"
   (`HTGeometry.primeValuationLeadingEchelonInfinite`), precisely because a filter can annihilate
   prime coefficients.  That weakening is what makes the sampling lemma usable.
3. **The sampling hypothesis is discharged.**  The card assumes, as a hypothesis of its general
   law, that every nonzero exponential polynomial is nonzero at infinitely many prime logarithms.
   In Lean this is a theorem (`PrimeCancellation.infinite_survivingPrimes`), obtained from finite
   exponential type, the Jensen zero count, and the corpus Chebyshev comparison; the polynomial
   trick of `eq_zero_of_exponentialType_of_cofinite_primeLog_zeros` removes the finitely many
   exceptional primes.
4. **Scope of the general law.**  The abstract statement quantifies over an arbitrary
   translation-stable differential field `K` and an arbitrary meromorphic `u` with a stripping
   operator.  Its arithmetic core is formalized in that generality
   (`PrimeCancellation.filteredSource_differentialIndependent`: any positive-prime-power-supported
   source with cofinitely many nonzero prime coefficients stays differentially independent after
   any nonzero finite filter).  The transfer half is formalized at the concrete differential field
   the corpus owns — the upper-end meromorphic field with its rational coordinate base — where the
   translation stability, the commutation of the filter with the stripper, and the rationality of
   the correction term are all theorems rather than hypotheses.

## Log

- 2026-08-17 Formalized in Lean 4 and promoted to stage 3.  The three previously missing analytic
  inputs are now theorems in the tree; the full arbitrary-complex-shift, arbitrary-order orbit
  freeness of `xi'/xi` modulo the differentially algebraic field is unconditional in Lean, together
  with the trivial translation stabilizer and the no-differential-difference-equation corollaries.
