# Finite Hard-Edge Counterterm Q0 RH Strength

- **ID:** finite-hard-edge-counterterm-q0-rh-strength
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / route normalization
- **Source:** `test-space-closure-q0-visible-rh.md`,
  `reciprocal-seam-admissible-domain-q1.md`,
  `pole-cancellation-not-stieltjes-positive.md`
- **Statement:** Adding an arbitrary finite-jet counterterm at the reciprocal
  hard edge `0` cannot hide an off-line reciprocal atom from the shifted `Q_0`
  test. If the renormalized all-order form is positive, then RH already follows.

## Setup

Let `Y` be the folded reciprocal nontrivial-zero support of the completed Riemann
`xi`, with positive folded multiplicities `M_y`, conjugation symmetry, and

`sum_y M_y |y| < infinity`.

Set

`K = Y union {0}`.

For real polynomials `p`, define the shifted source-aware form

`Q_0[p] = sum_y M_y y p(y)^2`.

Let `m >= 1`. Let `C` be any real quadratic form on `R[y]` such that

`C[p] = 0 whenever p in y^m R[y]`.

This includes the usual case in which `C` depends only on the finite hard-edge
jet

`p(0), p'(0), ..., p^(m-1)(0)`.

Define the finite-counterterm renormalized form

`R_C[p] = Q_0[p] + C[p]`.

## Theorem

If

`R_C[p] >= 0 for every real polynomial p`,

then RH holds.

More generally, for any closed conjugation-invariant set `E subset K`, a
counterterm that vanishes on all polynomials whose restriction to `E` is zero
cannot affect atom-isolation outside `E`. Positivity of the renormalized form
forces every reciprocal atom outside `E` to lie in `R_{>0}`.

## Proof

Assume first that `E={0}` and `C` vanishes on `y^m R[y]`.

Suppose there is a bad reciprocal atom `a in Y`.

If `a` is real and negative, define a continuous conjugation-symmetric function
`h` on `K` by

`h(a)=a^(-m)`, `h=0` on `K \ {a}`.

By the same Mergelyan/symmetrization argument used in
`source-aware-q0-alone-reciprocal-positivity.md`, choose real polynomials
`r_n` uniformly approximating `h` on `K`. Set

`p_n(y)=y^m r_n(y)`.

Then `p_n in y^m R[y]`, so `C[p_n]=0`, and `p_n` converges uniformly on `K` to
the atom-isolator `e_a` with `e_a(a)=1` and `e_a=0` elsewhere. Therefore

`R_C[p_n] = Q_0[p_n] -> M_a a < 0`,

contradicting positivity for all large `n`.

If `a` is non-real, then `conjugate(a)` is also an atom with the same
multiplicity. Choose `zeta in C` such that

`Re(a zeta^2) < 0`.

Define a continuous conjugation-symmetric function `h` on `K` by

`h(a)=zeta/a^m`,
`h(conjugate(a))=conjugate(zeta)/conjugate(a)^m`,
`h=0` elsewhere.

Choose real polynomials `r_n -> h` uniformly on `K` and set `p_n(y)=y^m r_n(y)`.
Again `C[p_n]=0`, and `p_n` converges to the symmetric isolator with values
`zeta` and `conjugate(zeta)` at the conjugate pair. Hence

`R_C[p_n] = Q_0[p_n] -> 2 M_a Re(a zeta^2) < 0`,

contradicting positivity.

Thus no bad atom exists, so every reciprocal atom lies in `R_{>0}`. This is RH.

For the closed-set variant, replace `y^m R[y]` by a test subspace whose uniform
closure contains the atom-isolators for all atoms outside `E` while vanishing on
`E`. The same argument applies because the counterterm is zero on that subspace.

## Consequence for the RH Route

Finite hard-edge renormalization is not an escape from the shifted `Q_0` wall.
A counterterm depending on finitely many data at the accumulation point `0` can
change low-order presentation, finite sections, or unshifted `T_0` bookkeeping.
It cannot repair a negative contribution from an isolated reciprocal atom away
from `0`, because that atom can be isolated by polynomials vanishing to arbitrary
prescribed finite order at `0`.

Therefore a proposed proof of positivity for

`Q_0[p] + finite hard-edge counterterm`

is still RH-strength. Under RH it additionally requires the counterterm itself
to be nonnegative on the hard-edge jet directions; otherwise even RH would not
make the renormalized form positive. But if positivity of the renormalized form
is asserted for all polynomials, the counterterm has not weakened the RH
obligation.

The only possible escape is an infinite-order or nonlocal renormalization whose
closed test space fails to isolate some atoms. That case is exactly the
test-space closure audit: the hidden atoms and their source control must be
identified explicitly.

## Theatre Test

For any hard-edge renormalized positivity argument, ask:

1. Does the counterterm depend only on finitely many jets at `0`?
2. If yes, why does the argument not reduce to this theorem?
3. If no, what is the closed test space after the infinite-order/nonlocal
   renormalization?
4. Which reciprocal atoms can no longer be isolated, and what source theorem
   controls them?

## Gates

- [x] 0 -> 1 in-progress: finite hard-edge counterterm loophole isolated.
- [x] 1 -> 2 fully-proven: complete atom-isolation proof with arbitrary finite
  vanishing order at `0`.
- [x] 2 -> 3 formalized: `RHTower/ReciprocalAtomPolynomialApproximation.lean`.

## Log

- 2026-06-24 -- Codex: created to close the finite hard-edge counterterm route.
  The proof is atom isolation through the ideal `y^m R[y]`.

## 2026-06-24 finite-rank quotient distinction

`finite-rank-counterterm-kernel-visibility.md` explains why the finite hard-edge theorem is stronger than a generic finite-rank statement. A hard-edge finite-jet counterterm vanishes on `y^m R[y]`, and that kernel still contains approximants to every atom-isolator away from `0`. Hence it remains RH-strength.

A general finite-rank counterterm need not have this property. If its quotient evaluates at a bad atom, it can cancel that atom. Therefore finite-rank repairs require an explicit kernel/quotient audit.

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

Card-specific.  `riemannHypothesis_of_hardEdge_counterterm` is the card's theorem: for any `m` and
any counterterm `C` vanishing on the hard-edge ideal `X^m R[X]`, nonnegativity of
`xiRepairedForm C` on every real polynomial implies RH.  The proof uses the vanishing-order clause
of `exists_realPolynomial_atomIsolator_approx`: every atom isolator is a uniform limit of real
polynomials that already lie in `X^m R[X]`, so the counterterm is identically zero along the
approximating sequence.  The counterterm is an arbitrary real functional, which is more general
than the card's real quadratic form.  The closed-set variant is
`xiReciprocalAtom_nonneg_of_dense_vanishing` in `ReciprocalAtomTestSpaceClosure.lean`.
