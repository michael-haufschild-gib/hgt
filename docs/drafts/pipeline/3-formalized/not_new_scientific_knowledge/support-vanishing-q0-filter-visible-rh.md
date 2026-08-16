# Support-Vanishing Q0 Filter Visible RH

- **ID:** support-vanishing-q0-filter-visible-rh
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / route normalization
- **Source:** `finite-boundary-ideal-q0-rh-equivalence.md`,
  `source-aware-q0-alone-reciprocal-positivity.md`
- **Statement:** Multiplying the source-aware `Q_0` test by a real polynomial
  filter proves RH exactly on the reciprocal atoms where the filter does not
  vanish. Atoms in the filter zero set are deleted from the test.

## Setup

Let `Y` be the folded reciprocal nontrivial-zero support of the completed Riemann
`xi`, with positive folded multiplicities `M_y`, conjugation symmetry, and

`sum_y M_y |y| < infinity`.

For real polynomials `p`, set

`Q_0[p] = sum_y M_y y p(y)^2`.

Let `h in R[y]` be a real polynomial and define the filtered form

`Q_h[q] = Q_0[h q] = sum_y M_y y h(y)^2 q(y)^2`.

Write

`Y_h = { y in Y : h(y) != 0 }`

for the visible reciprocal support of the filter.

## Theorem

The following are equivalent:

1. `Q_h[q] >= 0` for every real polynomial `q`.
2. Every visible atom lies on the positive real axis:

   `Y_h subset R_{>0}`.

Consequently, if `E = Y cap {h=0}`, the filtered test proves RH for the
deflated divisor `Y \ E` and says nothing about atoms in `E`.

## Proof

If `Y_h subset R_{>0}`, then each visible term has positive coefficient

`M_y y h(y)^2 > 0`,

and each hidden term has `h(y)=0`. Hence `Q_h[q]>=0` for all real polynomials
`q`.

Conversely, suppose there is a visible atom `a in Y_h` not lying in `R_{>0}`.
Let

`K = Y union {0}`.

As in `source-aware-q0-alone-reciprocal-positivity.md`, `K` is compact,
countable, has empty interior, and has connected complement. Real polynomials
are uniformly dense in the continuous conjugation-symmetric functions on `K`
after symmetrization. Since `h` is bounded on `K`, the summability assumption
gives dominated convergence for the filtered sums.

There are two cases.

1. `a` is real and negative. Because `h(a) != 0`, the coefficient

   `M_a a h(a)^2`

   is negative. Approximate the continuous symmetric function that is `1` at
   `a` and `0` on `K \ {a}` by real polynomials `q_n`. Then

   `Q_h[q_n] -> M_a a h(a)^2 < 0`,

   contradicting positivity.

2. `a` is non-real. Then `conjugate(a)` is also a visible atom with the same
   multiplicity, and

   `h(conjugate(a)) = conjugate(h(a))`.

   Since `a h(a)^2 != 0`, choose `zeta in C` such that

   `Re(a h(a)^2 zeta^2) < 0`.

   Approximate the continuous symmetric function with values `zeta` at `a`,
   `conjugate(zeta)` at `conjugate(a)`, and `0` elsewhere by real polynomials
   `q_n`. Then dominated convergence gives

   `Q_h[q_n] -> 2 M_a Re(a h(a)^2 zeta^2) < 0`,

   again contradicting positivity.

Thus positivity of `Q_h` excludes exactly the bad atoms that remain visible to
`h`. This proves the equivalence.

## Consequence for the RH Route

This is the complement of `finite-boundary-ideal-q0-rh-equivalence.md`.
There, the hypothesis `h(y) != 0` on the whole reciprocal support made filtered
positivity equivalent to RH. Here the same proof shows why that hypothesis is
load-bearing: if `h` vanishes on a reciprocal atom, that atom is removed from the
square test.

Therefore a Christoffel or boundary-filter proof has two distinct regimes:

1. `h` has no zeros on `Y`. The all-order filtered positivity test is still
   RH-strength.
2. `h` vanishes on part of `Y`. The test is no longer faithful to those atoms.
   It proves RH only after an independent source theorem rules out bad atoms in
   the hidden set `Y cap {h=0}`.

A filter chosen from the zero divisor can always delete the obstruction it needs
to hide. Such a filter is not a source selector. A non-mirror proof must either
derive a nonvanishing source filter before seeing the divisor, or prove from
source data that every hidden atom is already on the critical line.

## Theatre Test

For any proposed multiplier, Christoffel, Uvarov, or boundary-ideal proof, ask:

1. Who supplies `h`?
2. Is `h` proved nonzero on the reciprocal support from source data?
3. If not, what independent source theorem controls the hidden atoms in
   `Y cap {h=0}`?

If these questions are not answered before positivity is invoked, the argument
has not selected RH; it has changed the visibility of the divisor chart.

## Gates

- [x] 0 -> 1 in-progress: filtered support statement isolated.
- [x] 1 -> 2 fully-proven: complete atom-isolation proof.
- [x] 2 -> 3 formalized: `RHTower/ReciprocalAtomPolynomialApproximation.lean`.

## Log

- 2026-06-24 -- Codex: created to classify the case omitted by the
  finite-boundary nonvanishing theorem. The key point is that a support-vanishing
  filter deletes exactly the atoms it vanishes on.

## 2026-06-24 continuous-preconditioner generalization

`continuous-preconditioner-q0-visible-rh.md` generalizes this polynomial-filter theorem. The same visibility dichotomy holds for any bounded continuous conjugation-symmetric preconditioner `g` on `K=Y union {0}`: all-order positivity of `sum_y M_y y g(y)^2 q(y)^2` detects exactly the atoms where `g(y) != 0`.

Polynomial filters are therefore not a special loophole. The real invariant is support visibility: nonzero source weights preserve RH-strength, while zeros of the weight delete evidence.

## 2026-08-16 Lean closure

`RHTower/ReciprocalAtomTestSpaceClosure.lean`, `RHTower/ReciprocalAtomCounterterm.lean` and
`RHTower/ReciprocalAtomPolynomialApproximation.lean` build the reciprocal-atom layer on the actual
`xi` divisor, unconditionally.

`xiZeroCopyReciprocalSquare` is the multiplicity-exact folded reciprocal atom, `xiReciprocalAtomSet`
is `Y`, `xiReciprocalTestSet` is `K = Y union {0}`,
`summable_norm_xiZeroCopyReciprocalSquare` is `sum_y M_y |y| < infinity`,
`isCompact_xiReciprocalTestSet` proves `K` compact, and `xiQZero` is `Q_0`.
`xiPolynomialTest p` is the reciprocal test function of a real polynomial and
`xiQZero_polynomialTest_eq_hankel` proves the card's Hankel identity
`Q_0[p] = sum_{i,j} c_i c_j T_{i+j+1}` with `T_{k+1} = xiReciprocalMoment k`.

**The Mergelyan input is replaced by an elementary construction.**
`exists_realPolynomial_atomIsolator_approx` proves directly that every conjugation-symmetric atom
isolator is a uniform limit on `Y` of real polynomials, and with any prescribed vanishing order at
the hard edge `0`.  The construction: `K` has only finitely many points of norm at least
`||a||/2` (`finite_xiReciprocalTestSet_norm_ge`), so the Lagrange basis polynomial at `a` over that
finite set is exact there; multiplying by `(z/a)^N` keeps those values, contributes the prescribed
vanishing order at `0`, and makes the polynomial uniformly small on the remaining points, all of
norm at most `||a||/2`; symmetrizing the coefficients produces a real polynomial.  No compactness
theorem beyond boundedness of a polynomial on a disc is used, and no Mergelyan or Lavrentiev
theorem is invoked.

Axioms of every theorem listed: `propext`, `Classical.choice`, `Quot.sound`.

Card-specific.  `xiFilteredForm h q = Re Q_0[h q]` is the filtered form `Q_h`, and
`xiFilteredForm_nonneg_iff` is the card's equivalence: `Q_h[q] >= 0` for every real polynomial `q`
if and only if every atom with `h(y) != 0` is a nonnegative real.  The forward direction rescales
the isolator weight by `h(a)`: `xiPolynomialTest_mul_atomIsolator` proves
`h . e_{a, zeta/h(a)} = e_{a, zeta}` exactly on `K`, so a real polynomial approximating
`e_{a, zeta/h(a)}` gives `h q` approximating `e_{a, zeta}`, with the uniform bound of `h` on the
compact test set absorbing the error.  The converse is the termwise sign computation: visible atoms
are nonnegative reals and hidden atoms contribute `0`.
