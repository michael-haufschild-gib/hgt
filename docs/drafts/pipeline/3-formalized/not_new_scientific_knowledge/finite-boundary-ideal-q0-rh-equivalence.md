# Finite Boundary Ideal Q0 RH Equivalence

- **ID:** finite-boundary-ideal-q0-rh-equivalence
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / route normalization
- **Source:** `uvarov-kernel-pregate-rh-equivalence.md`,
  `source-aware-q0-alone-reciprocal-positivity.md`, and
  `shifted-reciprocal-moments-determine-divisor.md`
- **Statement:** For the actual reciprocal divisor, restricting the all-order
  shifted `Q_0` test to any finite boundary ideal that does not vanish on the
  reciprocal support is still equivalent to RH. Finite exterior boundary
  conditions do not make the all-order positivity target softer.

## Setup

Let `Y` be the folded reciprocal nontrivial-zero support of the completed Riemann
`xi`, with positive folded multiplicities `M_y` and

`sum_y M_y |y| < infinity`.

Set

`Q_0[p] = sum_y M_y y p(y)^2`

for real polynomials `p`. Let `h in R[y]` be a nonzero real polynomial such that

`h(y) != 0 for every y in Y`.

Define the ideal-restricted form

`Q_h[q] = Q_0[h q] = sum_y M_y y h(y)^2 q(y)^2`.

The one-point Uvarov pre-gate is the special case `h(y)=y+4/25`.

## Theorem

The following are equivalent:

1. RH.
2. `Q_h[q] >= 0` for every real polynomial `q`.

Consequently, for any finite real boundary set

`B={b_1,...,b_r}` disjoint from `Y`,

all-order positivity on the ideal of polynomials vanishing on `B`,

`Q_0[prod_j (y-b_j) q] >= 0 for every real q`,

is equivalent to RH.

## Proof

If RH holds, then every reciprocal atom lies in `R_{>0}`. Since `h` has real
coefficients, `h(y)^2 >= 0` for real `y`, and by the no-vanishing assumption
`h(y)^2>0` on `Y`. Therefore every coefficient

`M_y y h(y)^2`

is positive, so `Q_h[q]>=0` for every real polynomial `q`.

Conversely, suppose some atom `a in Y` is not in `R_{>0}`. Let

`K = Y union {0}`.

As in `source-aware-q0-alone-reciprocal-positivity.md`, `K` is compact,
countable, has empty interior, and has connected complement, so real polynomials
are uniformly dense in the continuous conjugation-symmetric functions on `K` after
symmetrization.

There are two cases.

1. `a` is real and negative. Since `h(a) != 0`, the coefficient

   `M_a a h(a)^2`

   is negative. Approximate the continuous symmetric function that is `1` at `a`
   and `0` on `K\\{a}` by real polynomials `q_n`. Dominated convergence gives

   `Q_h[q_n] -> M_a a h(a)^2 < 0`.

2. `a` is non-real. Then `conjugate(a)` is an atom with the same multiplicity, and
   `h(conjugate(a))=conjugate(h(a))`. Since `a h(a)^2 != 0`, choose `zeta in C`
   such that

   `Re(a h(a)^2 zeta^2) < 0`.

   Approximate the continuous symmetric function with values `zeta` at `a`,
   `conjugate(zeta)` at `conjugate(a)`, and `0` elsewhere by real polynomials
   `q_n`. Dominated convergence gives

   `Q_h[q_n] -> 2 M_a Re(a h(a)^2 zeta^2) < 0`.

Thus positivity of `Q_h` excludes every reciprocal atom outside `R_{>0}`. That is
equivalent to RH.

The finite-boundary statement follows by taking

`h(y)=prod_j (y-b_j)`.

## Consequence for the RH Route

This theorem generalizes the first-trivial-zero kernel result. Any proof that
assumes all-order positivity after forcing finitely many exterior boundary
vanishings has assumed an RH-equivalent divisor-localization chart, provided the
boundary polynomial does not vanish on the nontrivial reciprocal support.

Therefore finite boundary conditions, finite Uvarov channels, finite pole/protector
vanishing conditions, and finite Christoffel-style deflations do not create a
weaker all-order target. They only multiply the source-aware divisor measure by a
nonzero square on the support, which preserves the ability to isolate every bad
atom.

The non-mirror theorem must instead prove one of these equivalent positive cones
from independent source data: Euler/local-factor orientation, completed explicit
formula, geometric polarization, or another source rigidity principle not already
phrased as reciprocal-divisor positivity.

## Source Boundary

The proof is a direct adaptation of the compact polynomial-density argument used
for source-aware `Q_0`, with a nonvanishing real-polynomial square inserted. It
does not prove RH. It classifies a family of finite-boundary all-order targets as
RH-equivalent charts.

## Gates

- [x] 0 -> 1 in-progress: checked no existing finite-boundary ideal card.
- [x] 1 -> 2 fully-proven: ideal-restricted positivity equivalence proved.
- [x] 2 -> 3 formalized: `RHTower/ReciprocalAtomPolynomialApproximation.lean`.

## Log

- 2026-06-24 -- Codex: created as the finite-boundary generalization of the
  `y=-4/25` Uvarov pre-gate theorem. The key invariant is that a finite boundary
  polynomial with no zero on `Y` cannot hide a bad reciprocal atom.

## 2026-06-24 support-vanishing complement

`support-vanishing-q0-filter-visible-rh.md` proves the complementary statement: for an arbitrary real polynomial filter `h`, filtered positivity of `Q_0[hq]` for every real polynomial `q` is equivalent to positivity of the reciprocal divisor only on the visible support `{y in Y : h(y) != 0}`.

This explains why the nonvanishing hypothesis in the present theorem is essential. A finite boundary polynomial whose zeros avoid `Y` preserves RH-strength. A filter with zeros on `Y` deflates those atoms and cannot certify their location without an independent source argument.

## 2026-06-24 prolate-channel specialization

`finite-prolate-channel-boundary-rh-strength.md` applies this ideal theorem to the pole/trivial-zero `4N+1` prolate channels. Any fixed finite set of exterior channels gives a boundary ideal whose all-order positivity is still RH-equivalent, because the boundary polynomial is nonzero on the nontrivial reciprocal support.

Therefore finite prolate-channel Schur matrices are useful finite coordinates, but not weaker all-order proof targets.

## 2026-08-16 Lean closure

`RHTower/ReciprocalAtomTestSpaceClosure.lean` and
`RHTower/ReciprocalAtomPolynomialApproximation.lean` build the reciprocal-atom layer on the actual
`xi` divisor, unconditionally: `xiZeroCopyReciprocalSquare` is the multiplicity-exact folded
reciprocal atom, `xiReciprocalAtomSet` is `Y`, `xiReciprocalTestSet` is `K = Y union {0}`
(compact by `isCompact_xiReciprocalTestSet`), `xiQZero` is `Q_0`, and `xiPolynomialTest p` is the
test function of a real polynomial.

The Mergelyan input of the paper proof is replaced by the elementary
`exists_realPolynomial_atomIsolator_approx`: since `K` has only finitely many points of norm at
least `||a||/2`, the Lagrange basis polynomial at `a` over that finite set, multiplied by
`(z/a)^N` and symmetrized in its coefficients, is a real polynomial approximating the
conjugation-symmetric atom isolator uniformly on `Y`.

Axioms of every theorem listed: `propext`, `Classical.choice`, `Quot.sound`.

Card-specific.  `xiFilteredForm h q = Re Q_0[h q]` is `Q_h`.
`xiFilteredForm_nonneg_iff_riemannHypothesis` is the card's theorem: if the real polynomial `h`
does not vanish at any reciprocal atom, then nonnegativity of `Q_h` on all real polynomials is
equivalent to RH.  `xiBoundaryIdeal_nonneg_iff_riemannHypothesis` is the finite-boundary corollary:
for a finite real set `B` disjoint from the reciprocal support, all-order positivity on the ideal
generated by `prod_{b in B} (y - b)` is equivalent to RH.  Both follow from the general visibility
dichotomy `xiFilteredForm_nonneg_iff`.
