# Continuous Preconditioner Q0 Visible RH

- **ID:** continuous-preconditioner-q0-visible-rh
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / route normalization
- **Source:** `support-vanishing-q0-filter-visible-rh.md`,
  `source-aware-q0-alone-reciprocal-positivity.md`
- **Statement:** Any bounded conjugation-symmetric source preconditioner on the
  reciprocal support preserves the same visibility dichotomy as polynomial
  filters: nonzero weights leave the `Q_0` positivity test RH-strength, while
  zero weights delete exactly the atoms they vanish on.

## Setup

Let `Y` be the folded reciprocal nontrivial-zero support of the completed Riemann
`xi`, with positive folded multiplicities `M_y`, conjugation symmetry, and

`sum_y M_y |y| < infinity`.

Set

`K = Y union {0}`.

Let `g:K -> C` be continuous and conjugation-symmetric:

`g(conjugate(z)) = conjugate(g(z))`.

In particular, `g(x)` is real for real `x in K`. For real polynomials `q`,
define the preconditioned square test

`Q_g[q] = sum_y M_y y g(y)^2 q(y)^2`.

This value is real: conjugate atoms have the same multiplicity, `q` has real
coefficients, and `g` is conjugation-symmetric.

Write

`Y_g = { y in Y : g(y) != 0 }`

for the visible reciprocal support.

## Theorem

The following are equivalent:

1. `Q_g[q] >= 0` for every real polynomial `q`.
2. Every visible atom lies on the positive real axis:

   `Y_g subset R_{>0}`.

Consequently, if `g` is nonzero on all of `Y`, then all-order positivity of
`Q_g` is equivalent to RH. If `g` vanishes on a subset of `Y`, the test proves RH
only for the deflated support `Y_g` and says nothing about the hidden atoms.

## Proof

Since `g` is continuous on compact `K`, it is bounded. Therefore

`sum_y M_y |y| |g(y)|^2 < infinity`,

so all filtered sums are absolutely controlled by the same finite shifted total
variation used for `Q_0`.

If `Y_g subset R_{>0}`, then for visible atoms `y` the number `g(y)` is real and
nonzero, so

`M_y y g(y)^2 > 0`.

Hidden atoms contribute zero. Hence `Q_g[q]>=0` for every real polynomial `q`.

Conversely, suppose there is a visible atom `a in Y_g` not lying in `R_{>0}`.
As in `source-aware-q0-alone-reciprocal-positivity.md`, real polynomials are
uniformly dense on `K` in the continuous conjugation-symmetric functions, after
symmetrization. The boundedness of `g` gives dominated convergence for `Q_g`.

There are two cases.

1. `a` is real and negative. Since `g(a)` is real and nonzero,

   `M_a a g(a)^2 < 0`.

   Approximate the continuous symmetric function that is `1` at `a` and `0` on
   `K \ {a}` by real polynomials `q_n`. Then

   `Q_g[q_n] -> M_a a g(a)^2 < 0`,

   contradicting all-order positivity.

2. `a` is non-real. Then `conjugate(a)` is also a visible atom with the same
   multiplicity, and

   `g(conjugate(a)) = conjugate(g(a))`.

   Since `a g(a)^2 != 0`, choose `zeta in C` such that

   `Re(a g(a)^2 zeta^2) < 0`.

   Approximate the continuous symmetric function with values `zeta` at `a`,
   `conjugate(zeta)` at `conjugate(a)`, and `0` elsewhere by real polynomials
   `q_n`. Dominated convergence gives

   `Q_g[q_n] -> 2 M_a Re(a g(a)^2 zeta^2) < 0`,

   again contradicting positivity.

Thus positivity of `Q_g` excludes exactly the bad visible atoms and no hidden
atoms. This proves the equivalence.

## Consequence for the RH Route

This theorem closes the non-polynomial preconditioner variant of the finite
boundary loophole. A source proof may replace `Q_0` by a weighted or normalized
square test only in two regimes:

1. The source preconditioner is proved nonzero on the reciprocal support. Then
   the all-order positivity target is still RH-strength.
2. The source preconditioner vanishes on part of the reciprocal support. Then the
   positivity target is weaker only because it has stopped seeing those atoms,
   and an independent source theorem must control the hidden set.

Thus a bounded analytic gauge, scalar normalization, Christoffel weight, or
preconditioned Markov/Stieltjes transform does not by itself make the RH
positivity wall softer. It either preserves the same atom-isolation power or
deletes evidence. The missing theorem remains source-side: prove the relevant
positive cone from Euler/Gamma/FE constraints without feeding in the reciprocal
divisor.

## Theatre Test

For any source preconditioner `g`, ask before invoking positivity:

1. Is `g` defined from source data before the zero divisor is read?
2. Is `g` conjugation-symmetric and real on the real reciprocal axis?
3. Is `g` proved nonzero on `Y` from source data?
4. If not, what source theorem controls the hidden support `{y in Y : g(y)=0}`?

Failure to answer these questions means the argument has not proved RH. It has
changed which reciprocal atoms the test can see.

## Gates

- [x] 0 -> 1 in-progress: continuous preconditioner variant isolated.
- [x] 1 -> 2 fully-proven: atom-isolation proof completed.
- [x] 2 -> 3 formalized: `RHTower/ReciprocalAtomPolynomialApproximation.lean`.

## Log

- 2026-06-24 -- Codex: created to generalize polynomial boundary filters to
  bounded conjugation-symmetric preconditioners on the reciprocal support.

## 2026-06-24 summable hard-edge extension

The continuity assumption is convenient but not essential. The same theorem holds for any function

`g:Y -> C`

satisfying:

1. `g(conjugate(y)) = conjugate(g(y))`;
2. `sum_y M_y |y| |g(y)|^2 < infinity`.

The second condition is exactly the finiteness needed for `Q_g[1]` to be well-defined in absolute value. Under these hypotheses, define

`Q_g[q] = sum_y M_y y g(y)^2 q(y)^2`

for real polynomials `q` and `Y_g={y in Y : g(y) != 0}`. Then

`Q_g[q] >= 0 for every real polynomial q`

is equivalent to

`Y_g subset R_{>0}`.

Proof. Conjugation symmetry again makes `Q_g[q]` real on real polynomials. If `Y_g subset R_{>0}`, visible terms are positive and hidden terms vanish. Conversely, if a visible bad atom `a` exists, use the same polynomial approximation to isolate `a` or the pair `{a, conjugate(a)}`. Dominated convergence is now supplied by the summable majorant `M_y |y| |g(y)|^2 sup_K |q_n|^2`, not by boundedness of `g`. The negative limiting value is `M_a a g(a)^2` in the negative-real case and `2M_a Re(a g(a)^2 zeta^2)` in the non-real case.

Consequence: a hard-edge singular preconditioner near `0` does not bypass the visibility gate if its square test is finite. If it is nonzero on all atoms, the target is RH-strength; if it vanishes on atoms, those atoms are hidden; if `sum_y M_y |y| |g(y)|^2` diverges, the claimed all-order positivity is not even defined on the constant test without an additional renormalization. Any such renormalization must be stated as new source data and audited separately.

## 2026-06-24 test-space closure generalization

`test-space-closure-q0-visible-rh.md` generalizes the preconditioner theorem from multiplicative weights to arbitrary closed test spaces. A source-built operator image `S` is governed by its uniform closure on `K=Y union {0}`: positivity on `S` detects exactly the atoms that this closure can isolate.

Multiplicative preconditioners are the special case where the closed image is the weighted test space. More general differential, difference, Christoffel, boundary, or renormalized operators require the same visibility audit: dense image means RH-strength; non-dense image means hidden atoms.

## 2026-06-24 finite counterterms at the hard edge

`finite-hard-edge-counterterm-q0-rh-strength.md` complements the singular-weight extension. If a divergent hard-edge preconditioner is replaced by a finite-jet counterterm at `0`, the resulting positivity statement is still RH-strength: polynomials can vanish to the required finite order at `0` and isolate any bad atom away from `0`.

Thus a finite hard-edge counterterm is not a hidden-support mechanism. Hidden support can arise only from an infinite-order or nonlocal restriction of the closed test space.

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

Card-specific.  `xiPreconditionedForm g q = Re Q_0[g . q]` is `Q_g`, and
`xiPreconditionedForm_nonneg_iff` is the card's equivalence, for an arbitrary preconditioner `g`
that is bounded and conjugation-symmetric on the reciprocal support: nonnegativity of `Q_g` on all
real polynomials holds if and only if every atom with `g(y) != 0` is a nonnegative real.
Continuity on the compact `K` is not needed — only the boundedness it supplies, so the Lean
statement is more general than the card's.  The forward direction rescales the isolator weight:
`xiPreconditioner_mul_atomIsolator` proves `g . e_{a, zeta/g(a)} = e_{a, zeta}` exactly, so a real
polynomial approximating `e_{a, zeta/g(a)}` gives `g q` approximating `e_{a, zeta}` with the bound
of `g` absorbing the error.  The polynomial-filter case is the corollary
`xiFilteredForm_nonneg_iff`.
