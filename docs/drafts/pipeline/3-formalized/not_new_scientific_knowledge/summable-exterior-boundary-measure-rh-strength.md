# Summable Exterior Boundary Measures Are RH Strength

- **ID:** summable-exterior-boundary-measure-rh-strength
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / route normalization
- **Source:** `finite-prolate-channel-boundary-rh-strength.md`,
  `test-space-closure-q0-visible-rh.md`,
  `finite-boundary-ideal-q0-rh-equivalence.md`
- **Statement:** Adding a finite-total-variation exterior boundary measure,
  supported away from the reciprocal nontrivial-zero atoms, cannot hide an
  off-line reciprocal atom. Positivity of the repaired all-order form is still
  RH-strength. This covers the summable full trivial-zero/prolate tail as a
  boundary measure.

## Setup

Let `Y` be the folded reciprocal nontrivial-zero support of the completed
Riemann `xi`, with positive folded multiplicities `M_y`, conjugation symmetry,
and

`sum_y M_y |y| < infinity`.

Let `B` be a countable real exterior boundary set such that:

1. `B cap Y = empty`;
2. the only possible accumulation point of `B union Y` is `0`.

Let `(beta_b)_{b in B}` be real coefficients with

`sum_{b in B} |beta_b| < infinity`.

For real polynomials `p`, set

`Q_0[p]=sum_y M_y y p(y)^2`

and

`R_beta[p]=Q_0[p]+sum_{b in B} beta_b p(b)^2`.

The prolate/trivial-zero exterior tail is of this type: the points

`b_N=-(2N+1/2)^{-2}`

accumulate only at `0`, and the Gamma weights are summable.

## Theorem

If

`R_beta[p]>=0 for every real polynomial p`,

then RH holds.

If RH holds and `beta_b>=0` for every `b`, then `R_beta[p]>=0` for every real
polynomial `p`.

## Proof

Set

`K = Y union B union {0}`.

This compact set is countable and has only `0` as a possible accumulation point.
Its complement is connected, so real polynomials are uniformly dense in the
continuous conjugation-symmetric functions on `K`, after symmetrization.

The boundary term is continuous for the uniform norm on `K`, because

`|sum_b beta_b (f(b)^2-g(b)^2)|
 <= sum_b |beta_b| ||f-g||_infty (||f||_infty+||g||_infty)`.

The same continuity estimate holds for `Q_0` by `sum_y M_y |y| < infinity`.
Therefore positivity on real polynomials passes to continuous symmetric
functions on `K`.

Suppose first that `a in Y` is real and negative. Since `a` is isolated in `K`,
there is a continuous function `e_a` on `K` with

`e_a(a)=1`, `e_a=0` on `K \\ {a}`.

For this isolator the boundary term vanishes, and

`R_beta[e_a]=Q_0[e_a]=M_a a < 0`,

contradicting positivity.

Now suppose `a in Y` is non-real. Choose `zeta in C` with

`Re(a zeta^2)<0`.

Let `e_{a,zeta}` be the conjugation-symmetric isolator with value `zeta` at
`a`, value `conjugate(zeta)` at `conjugate(a)`, and `0` elsewhere on `K`. Again
the boundary term vanishes, while

`R_beta[e_{a,zeta}]
 = Q_0[e_{a,zeta}]
 = 2 M_a Re(a zeta^2) < 0`,

a contradiction.

Thus no reciprocal atom lies outside `R_{>0}`. This is RH.

Conversely, under RH every reciprocal atom lies in `R_{>0}`, so `Q_0[p]>=0`.
If all `beta_b>=0`, the boundary term is also nonnegative, hence `R_beta[p]>=0`.

## Consequence for the RH Route

The finite-channel theorem did not cover the full trivial-zero/prolate tail
because that tail is infinite and accumulates at the hard edge `0`. This theorem
does cover it when the tail enters as a finite-total-variation exterior boundary
measure.

Therefore the full summable Gamma/prolate exterior measure is still not a
softer positivity target. If the repaired all-order form is positive for all
polynomials, RH follows by the same atom-isolation mechanism.

To escape this guardrail, a proposed semilocal proof must use boundary data that
are not merely a summable measure on exterior points: for example, a genuinely
nonlocal source operator, a non-finite-variation boundary distribution, or a
source theorem that controls the finite-place correction before reciprocal
atoms are read. Each such object needs its own zero-feeding audit.

## Theatre Test

For any infinite exterior-channel repair:

1. Is the boundary term a finite-total-variation measure on exterior points?
2. Is its support disjoint from the reciprocal nontrivial-zero support?
3. If yes, why does the proof not reduce to this theorem and hence to an
   RH-strength all-order positivity chart?
4. If no, what source theorem defines the non-measure or nonlocal boundary
   object without reading zero locations?

## Gates

- [x] 0 -> 1 in-progress: infinite summable exterior-channel case isolated.
- [x] 1 -> 2 fully-proven: compact-support atom-isolation proof completed.
- [x] 2 -> 3 formalized: `RHTower/ReciprocalAtomPolynomialApproximation.lean`.

## Log

- 2026-06-24 -- Codex: created to classify the full summable trivial-zero /
  prolate exterior tail after the fixed finite-channel guardrail.

## 2026-06-24 atom-local reading

`continuous-counterterm-atom-locality.md` explains the same result in local language. A summable exterior boundary measure has no mass on reciprocal nontrivial atoms, so its quadratic term vanishes on every reciprocal atom-isolator. Therefore it cannot repair an off-line atom contribution.

## 2026-08-16 Lean closure

`RHTower/ReciprocalAtomTestSpaceClosure.lean` and
`RHTower/ReciprocalAtomPolynomialApproximation.lean` build the reciprocal-atom layer on the actual
`xi` divisor, unconditionally: `xiZeroCopyReciprocalSquare` is the multiplicity-exact folded
reciprocal atom, `xiReciprocalAtomSet` is `Y`, `xiReciprocalTestSet` is `K = Y union {0}`,
`summable_norm_xiZeroCopyReciprocalSquare` is `sum_y M_y |y| < infinity`, `xiQZero` is `Q_0`, and
`xiPolynomialTest p` is the test function of a real polynomial.

The Mergelyan input is replaced by the elementary `exists_realPolynomial_isolator_approx_on`: for
any conjugation-invariant set with only finitely many points outside each disc around `0`, the
Lagrange basis polynomial at `a` over the finitely many points of norm at least `||a||/2`, times
`(z/a)^N`, coefficientwise symmetrized, is a real polynomial approximating the
conjugation-symmetric isolator uniformly, with any prescribed vanishing order at `0`.

Axioms of every theorem listed: `propext`, `Classical.choice`, `Quot.sound`.

Card-specific.  `riemannHypothesis_of_summableBoundaryMeasure` is the card's theorem: for a family
of real boundary points `b_i` disjoint from the reciprocal support and accumulating only at `0`,
and summable real weights `beta_i`, nonnegativity of `Q_0[p] + sum_i beta_i p(b_i)^2` on all real
polynomials implies RH.  The approximation is run on the enlarged set
`K union range b`, which still satisfies the finiteness hypothesis of
`exists_realPolynomial_isolator_approx_on`; the isolator vanishes at every `b_i`, so the boundary
term along the approximating sequence is bounded by `(sum_i |beta_i|) * eps^2` and the transfer of
positivity with vanishing slack is `xiQZero_re_nonneg_of_slack_approx`.
`summableBoundaryMeasure_nonneg_of_riemannHypothesis` is the second clause: under RH a nonnegative
boundary measure keeps the repaired form nonnegative.
