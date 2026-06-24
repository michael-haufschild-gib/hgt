# Support-Vanishing Q0 Filter Visible RH

- **ID:** support-vanishing-q0-filter-visible-rh
- **Stage:** 2-fully-proven
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
- [ ] 2 -> 3 formalized: optional; same approximation dependency as
  `source-aware-q0-alone-reciprocal-positivity.md`.

## Log

- 2026-06-24 -- Codex: created to classify the case omitted by the
  finite-boundary nonvanishing theorem. The key point is that a support-vanishing
  filter deletes exactly the atoms it vanishes on.

## 2026-06-24 continuous-preconditioner generalization

`continuous-preconditioner-q0-visible-rh.md` generalizes this polynomial-filter theorem. The same visibility dichotomy holds for any bounded continuous conjugation-symmetric preconditioner `g` on `K=Y union {0}`: all-order positivity of `sum_y M_y y g(y)^2 q(y)^2` detects exactly the atoms where `g(y) != 0`.

Polynomial filters are therefore not a special loophole. The real invariant is support visibility: nonzero source weights preserve RH-strength, while zeros of the weight delete evidence.
