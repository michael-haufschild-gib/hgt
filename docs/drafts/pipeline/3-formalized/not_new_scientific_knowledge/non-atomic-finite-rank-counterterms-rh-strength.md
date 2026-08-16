# Non-Atomic Finite-Rank Counterterms Are RH Strength

- **ID:** non-atomic-finite-rank-counterterms-rh-strength
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / route normalization
- **Source:** `finite-rank-counterterm-kernel-visibility.md`,
  `test-space-closure-q0-visible-rh.md`
- **Statement:** A continuous finite-rank counterterm whose boundary functionals
  have no point-mass component on the reciprocal support cannot hide any
  off-line reciprocal atom. Positivity of `Q_0` plus such a counterterm is still
  RH-strength.

## Setup

Let `Y` be the folded reciprocal nontrivial-zero support of the completed Riemann
`xi`, with positive folded multiplicities `M_y`, conjugation symmetry, and

`sum_y M_y |y| < infinity`.

Set

`K = Y union {0}`.

Let `C_sym(K)` be the real vector space of continuous conjugation-symmetric
functions on `K`, and set

`Q_0[f] = sum_y M_y y f(y)^2`.

Let

`L:C_sym(K) -> R^r`

be a continuous real-linear map, let `B` be a real quadratic form on `R^r`, and
set

`C[f] = B(Lf)`, `R_C[f]=Q_0[f]+C[f]`.

Assume that `L` annihilates every reciprocal atom-isolator:

1. for every real `a in Y`, `a<0`, the function `e_a(a)=1`, `e_a=0` on
   `K \ {a}` satisfies `L(e_a)=0`;
2. for every non-real `a in Y` and every `zeta in C`, the symmetric isolator
   with values `zeta` at `a`, `conjugate(zeta)` at `conjugate(a)`, and `0`
   elsewhere satisfies `L(e_{a,zeta})=0`.

This hypothesis is satisfied if each component of `L` is represented by a finite
signed Borel measure on `K` whose point masses vanish at every point of `Y`.

## Theorem

If

`R_C[f] >= 0 for every f in C_sym(K)`,

then RH holds.

The same conclusion holds if positivity is first proved on real polynomials and
then passed to `C_sym(K)` by uniform density and continuity.

## Proof

The atom-isolator hypothesis says that every bad atom isolator lies in `ker L`.
Therefore the counterterm vanishes on every atom-isolator:

`C[e]=B(Le)=0`.

If `a in Y` is real and negative, positivity gives

`0 <= R_C[e_a] = Q_0[e_a] = M_a a < 0`,

a contradiction.

If `a in Y` is non-real, choose `zeta in C` such that

`Re(a zeta^2) < 0`.

For the corresponding symmetric isolator `e_{a,zeta}`, positivity gives

`0 <= R_C[e_{a,zeta}]
   = Q_0[e_{a,zeta}]
   = 2 M_a Re(a zeta^2) < 0`,

again a contradiction.

Thus no reciprocal atom lies outside `R_{>0}`. This is RH.

For the measure-representation sufficient condition, the isolator of an isolated
point integrates to exactly the point mass of the representing measure at that
point. If all such point masses vanish on `Y`, then `L` annihilates every
reciprocal atom-isolator.

## Consequence for the RH Route

This theorem converts the finite-rank quotient warning into a source-facing
test. A finite-dimensional counterterm can hide an off-line reciprocal atom only
if its boundary map sees the atom's isolator. For continuous boundary
functionals, that means a point-mass component at the reciprocal atom.

Therefore a finite-rank repair whose source data are non-atomic on the reciprocal
support remains RH-strength. It cannot be sold as a softer positivity theorem.
To make the target weaker, the finite quotient must contain atom-evaluation
data on `Y`; that is precisely the zero-feeding risk unless those evaluations
are constructed and controlled by an independent source theorem.

## Theatre Test

For any proposed finite-rank source repair, inspect the representing boundary
functionals:

1. Do they have point masses at reciprocal atoms?
2. If not, the repair is still RH-strength by this theorem.
3. If yes, what source construction supplies those atom evaluations without
   reading the zero divisor?
4. Which quotient inequalities replace the hidden atom-isolation tests?

## Gates

- [x] 0 -> 1 in-progress: non-atomic finite-rank criterion isolated.
- [x] 1 -> 2 fully-proven: atom-isolator proof completed.
- [x] 2 -> 3 formalized: `RHTower/ReciprocalAtomCounterterm.lean`.

## Log

- 2026-06-24 -- Codex: created to sharpen the finite-rank quotient audit. The
  theorem identifies point-mass atom visibility as the exact finite-rank
  zero-feeding risk.

## 2026-06-24 continuous-counterterm generalization

`continuous-counterterm-atom-locality.md` is the non-finite-rank version of this result. The non-atomic finite-rank theorem forces the boundary map to annihilate atom-isolators. The general theorem says any continuous quadratic counterterm is harmless exactly at the atoms where its restriction to the isolator subspace vanishes.

## 2026-08-16 Lean closure

`RHTower/ReciprocalAtomTestSpaceClosure.lean` and `RHTower/ReciprocalAtomCounterterm.lean` build the
reciprocal-atom layer on the actual `xi` divisor, unconditionally.  `xiZeroCopyReciprocalSquare` is
the multiplicity-exact folded reciprocal atom, `xiReciprocalAtomSet` is `Y`,
`xiReciprocalTestSet` is `K = Y union {0}` (compact by `isCompact_xiReciprocalTestSet`),
`xiQZero` is `Q_0`, and `xiAtomIsolator a zeta` is the conjugation-symmetric isolator, continuous on
`K` by `continuousOn_xiAtomIsolator`.

`riemannHypothesis_of_boundaryMap_kills_isolators` is this card's theorem: for a real linear
boundary map `L` into `R^r` and a real quadratic form `B`, if `L` annihilates every reciprocal
atom-isolator, then nonnegativity of `xiRepairedForm (B . L)` implies RH.  Its proof is
`riemannHypothesis_of_counterterm_atomLocal` — a counterterm vanishing on every atom-isolator
subspace is RH-transparent — together with the atom detection
`xiQZero_atomIsolator_re_neg` and the corpus criterion
`riemannHypothesis_iff_forall_xiZeroCopyReciprocalSquare_nonnegative`.  The exact local readings
`M_a a zeta^2` and `2 M_a Re(a zeta^2)` are `xiQZero_atomIsolator_re_of_eq_conj` and
`xiQZero_atomIsolator_re_of_ne_conj`, using `xiAtomMultiplicity_conj` for the equality of
conjugate multiplicities.

The measure-representation sufficient condition is `integral_xiAtomIsolator_eq_zero`: a boundary
functional given by integration against a Borel measure with no point mass at the atom or at its
conjugate annihilates that isolator, so a signed boundary functional with vanishing point masses on
`Y` does too, componentwise.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
