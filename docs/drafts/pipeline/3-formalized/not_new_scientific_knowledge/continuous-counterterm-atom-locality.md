# Continuous Counterterms Are Atom-Local At Obstructions

- **ID:** continuous-counterterm-atom-locality
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / route normalization
- **Source:** `test-space-closure-q0-visible-rh.md`,
  `finite-rank-counterterm-kernel-visibility.md`,
  `non-atomic-finite-rank-counterterms-rh-strength.md`
- **Statement:** Any continuous quadratic counterterm can affect an off-line
  reciprocal atom only through its restriction to the finite-dimensional
  atom-isolator subspace for that atom. If the counterterm vanishes on all such
  subspaces, positivity of `Q_0` plus the counterterm is still RH-strength.

## Setup

Let `Y` be the folded reciprocal nontrivial-zero support of the completed
Riemann `xi`, with positive folded multiplicities `M_y`, conjugation symmetry,
and

`sum_y M_y |y| < infinity`.

Set

`K = Y union {0}`.

Let `C_sym(K)` be the real vector space of continuous conjugation-symmetric
functions on `K`, and set

`Q_0[f]=sum_y M_y y f(y)^2`.

Let `C` be a continuous real quadratic form on `C_sym(K)`, and define

`R_C[f]=Q_0[f]+C[f]`.

For a real atom `a in Y`, let `E_a` be the one-dimensional real subspace spanned
by the isolator `e_a` with `e_a(a)=1` and `e_a=0` on `K\\{a}`.

For a non-real atom `a in Y`, let `E_a` be the two-dimensional real subspace of
conjugation-symmetric isolators supported on `{a,conjugate(a)}`:

`e_{a,zeta}(a)=zeta`,
`e_{a,zeta}(conjugate(a))=conjugate(zeta)`,
`e_{a,zeta}=0` elsewhere.

## Theorem

If

`R_C[f]>=0 for every f in C_sym(K)`,

then for every atom `a in Y`, the finite-dimensional local form

`(Q_0+C)|_{E_a}`

is positive semidefinite.

Consequently, if `C|_{E_a}=0` for every reciprocal atom `a`, then positivity of
`R_C` on `C_sym(K)` implies RH.

The same conclusion holds if positivity is proved first on real polynomials and
then extended to `C_sym(K)` by uniform density and continuity.

## Proof

The first statement is immediate: each `E_a` is a real subspace of `C_sym(K)`,
so positivity of `R_C` on the whole space restricts to positivity on `E_a`.

Assume now that `C|_{E_a}=0` for every atom.

If `a` is real and negative, then `e_a in E_a`, and positivity gives

`0 <= R_C[e_a] = Q_0[e_a] = M_a a < 0`,

a contradiction.

If `a` is non-real, choose `zeta in C` such that

`Re(a zeta^2)<0`.

For the corresponding isolator `e_{a,zeta} in E_a`, positivity gives

`0 <= R_C[e_{a,zeta}]
   = Q_0[e_{a,zeta}]
   = 2 M_a Re(a zeta^2) < 0`,

again a contradiction.

Therefore no reciprocal atom lies outside `R_{>0}`. This is RH.

For the polynomial-first version, `Q_0` and `C` are continuous for the uniform
norm, and real polynomials are uniformly dense in `C_sym(K)` after conjugation
symmetrization. Hence positivity passes to `C_sym(K)` before applying the
preceding argument.

## Consequence for the RH Route

This theorem is the general atom-local audit for nonlocal or infinite-rank
counterterms. A counterterm does not become source-selecting merely because it
is nonlocal, infinite-dimensional, or written as a semilocal operator. At each
bad reciprocal atom, the proof must answer what the counterterm does on the
atom-isolator subspace.

There are only two possibilities:

1. The counterterm vanishes on every atom-isolator subspace. Then the repaired
   positivity theorem is still RH-strength by this card.
2. The counterterm is nonzero on some atom-isolator subspace. Then it can affect
   the local obstruction only by supplying atom-local data, and the route must
   prove that data is source-built without reading the reciprocal divisor.

Thus the remaining semilocal route must provide a source theorem for the
counterterm's atom-local restrictions, or prove that its nonlocal action forces
the faithful index without ever using reciprocal atom evaluations as input.

## Theatre Test

For any continuous nonlocal or semilocal counterterm:

1. What is the restriction of the counterterm to each atom-isolator subspace
   `E_a`?
2. Does it vanish there? If yes, the repaired positivity is still RH-strength.
3. If it does not vanish, what source construction supplies those atom-local
   values without reading the zero divisor?
4. Does the proof prove a faithful index theorem before evaluating these local
   forms, or does it repair the local obstruction after seeing it?

## Gates

- [x] 0 -> 1 in-progress: general continuous-counterterm atom-local audit
  isolated.
- [x] 1 -> 2 fully-proven: restriction-to-isolators proof completed.
- [x] 2 -> 3 formalized: `RHTower/ReciprocalAtomCounterterm.lean`.

## Log

- 2026-06-24 -- Codex: created to classify the remaining nonlocal/infinite-rank
  counterterm escape hatch after the finite-rank and summable exterior-measure
  guardrails.

## 2026-06-24 local domination threshold

`continuous-counterterm-local-domination-threshold.md` handles the complementary case where a continuous counterterm is nonzero on an atom-isolator subspace. Positivity then forces an exact atom-local bill: for a negative real atom, `C[e_a] >= -M_a a`; for a non-real pair, `C|_{E_a} >= -Q_0|_{E_a}` in the real two-dimensional Loewner order.

Thus nonzero atom-local action is not a vague reserve. It is the precise scalar or matrix domination that any source-built repair must explain before the reciprocal divisor is used.

## 2026-08-16 Lean closure

`RHTower/ReciprocalAtomTestSpaceClosure.lean` and `RHTower/ReciprocalAtomCounterterm.lean` build the
whole reciprocal-atom layer on the actual `xi` divisor, unconditionally.

Setup.  `xiZeroCopyReciprocalSquare` is the inverse square of the centered spectral coordinate,
indexed by the multiplicity-exact divisor copies, so folded multiplicities are automatic;
`xiReciprocalAtomSet` is `Y` and `xiReciprocalTestSet` is `K = Y union {0}`.
`summable_norm_xiZeroCopyReciprocalSquare` is the card's `sum_y M_y |y| < infinity`, and
`isCompact_xiReciprocalTestSet` proves `K` compact.  `xiQZero f = sum_q y_q f(y_q)^2` is `Q_0`.
`xiZeroCopyReciprocalSquare_conjEquiv` gives the conjugation symmetry of the folded support with
equal multiplicities (`xiAtomMultiplicity_conj`).

Isolators.  `xiAtomIsolator a zeta` is the card's `e_a` and `e_{a,zeta}`;
`xiAtomIsolator_conjSymm` proves conjugation symmetry (with `zeta` real at a real atom),
`xiReciprocalTestSet_singleton_mem_nhdsWithin` proves every nonzero point of `K` is isolated, and
`continuousOn_xiAtomIsolator` therefore places the isolator in `C_sym(K)`.

Continuity of `Q_0`.  `norm_xiQZero_sub_le` is the card's uniform estimate
`|Q_0[f]-Q_0[g]| <= (||f||+||g||) ||f-g|| sum_y M_y |y|`, and
`xiQZero_re_nonneg_of_uniform_approx` passes nonnegativity to uniform limits.

Atom detection.  `xiQZero_atomIsolator_re_neg` proves that a strictly negative isolator reading
forces `Q_0` strictly negative, and `xiReciprocalAtom_nonneg_of_isolator` converts that into the
card's dichotomy through the corpus criterion
`riemannHypothesis_iff_forall_xiZeroCopyReciprocalSquare_nonnegative`.  The exact local readings are
`xiQZero_atomIsolator_re_of_eq_conj` (`M_a a zeta^2`) and `xiQZero_atomIsolator_re_of_ne_conj`
(`2 M_a Re(a zeta^2)`).

Axioms of every theorem listed: `propext`, `Classical.choice`, `Quot.sound`.

Card-specific.  `xiRepairedForm_nonneg_on_isolator` is the first statement: nonnegativity of `R_C`
on all test functions restricts to every atom-isolator subspace `E_a`.
`riemannHypothesis_of_counterterm_atomLocal` is the consequence: if `C` vanishes on every
atom-isolator subspace, then `R_C >= 0` implies RH.  No continuity or finite rank is needed for
either statement — the counterterm is an arbitrary real functional on test functions, which is
strictly more general than the card's continuous quadratic `C`.
