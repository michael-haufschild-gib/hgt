# Test-Space Closure Q0 Visible RH

- **ID:** test-space-closure-q0-visible-rh
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / route normalization
- **Source:** `source-aware-q0-alone-reciprocal-positivity.md`,
  `support-vanishing-q0-filter-visible-rh.md`,
  `continuous-preconditioner-q0-visible-rh.md`
- **Statement:** Replacing the full polynomial test space by the image of an
  operator weakens `Q_0` positivity only by changing which reciprocal atoms are
  visible in the uniform closure of that test space. Dense test spaces remain
  RH-strength.

## Setup

Let `Y` be the folded reciprocal nontrivial-zero support of the completed Riemann
`xi`, with positive folded multiplicities `M_y`, conjugation symmetry, and

`sum_y M_y |y| < infinity`.

Set

`K = Y union {0}`.

Let `C_sym(K)` be the real vector space of continuous functions `f:K -> C`
satisfying

`f(conjugate(z)) = conjugate(f(z))`.

For `f in C_sym(K)`, define

`Q_0[f] = sum_y M_y y f(y)^2`.

The series is absolutely controlled by `sum_y M_y |y| ||f||_infty^2`, and
conjugation symmetry makes `Q_0[f]` real.

Let `S` be a real vector subspace of `C_sym(K)`. In applications, `S` is the
uniform closure on `K` of a source-built polynomial test space, such as the image
of a differential, difference, Christoffel, or boundary operator.

## Definitions

A real negative atom `a in Y` is `S`-visible if the function

`e_a(a)=1`, `e_a=0` on `K \ {a}`

lies in the uniform closure of `S`.

A non-real atom `a in Y` is `S`-visible if for some `zeta in C` with

`Re(a zeta^2) < 0`,

the conjugation-symmetric function

`e_{a,zeta}(a)=zeta`,
`e_{a,zeta}(conjugate(a))=conjugate(zeta)`,
`e_{a,zeta}=0` elsewhere on `K`

lies in the uniform closure of `S`.

## Theorem

If

`Q_0[f] >= 0 for every f in S`,

then every `S`-visible atom lies in `R_{>0}`.

In particular:

1. If `S` is uniformly dense in `C_sym(K)`, then positivity on `S` is equivalent
   to RH.
2. If `E subset K` is closed and conjugation-invariant, and `S` is uniformly
   dense in

   `{ f in C_sym(K) : f|E = 0 }`,

   then positivity on `S` is equivalent to RH for the visible support `Y \ E`;
   atoms in `Y cap E` are hidden from the test.

## Proof

The functional `Q_0` is continuous for the uniform norm on `C_sym(K)`:

`|Q_0[f]-Q_0[g]|
 <= sum_y M_y |y| |f(y)^2-g(y)^2|`

and the right side is bounded by

`sum_y M_y |y| ||f-g||_infty (||f||_infty+||g||_infty)`.

Thus positivity on `S` extends to the uniform closure of `S`.

Suppose a real negative atom `a` is `S`-visible. Then `e_a` belongs to the
closure of `S`, so positivity gives

`0 <= Q_0[e_a] = M_a a < 0`,

a contradiction.

Suppose a non-real atom `a` is `S`-visible. Since `conjugate(a)` has the same
multiplicity, positivity gives

`0 <= Q_0[e_{a,zeta}]
   = M_a a zeta^2 + M_a conjugate(a) conjugate(zeta)^2
   = 2 M_a Re(a zeta^2) < 0`,

again a contradiction.

Therefore positivity on `S` excludes every bad atom that the closed test space
can isolate.

If `S` is dense in all of `C_sym(K)`, every bad atom is visible, and the preceding
paragraph proves RH. The converse is immediate: under RH, every reciprocal atom
lies in `R_{>0}`, so `Q_0[f]>=0` for every `f in C_sym(K)` and hence for every
`f in S`.

For the closed-set variant, every atom outside `E` is isolated in `K` and has an
isolator lying in `{f in C_sym(K): f|E=0}`. The same argument detects all bad
atoms in `Y \ E`, while atoms in `Y cap E` cannot be tested by a space whose
closure vanishes on `E`. Positivity is therefore equivalent to RH on the visible
support `Y \ E`.

## Consequence for the RH Route

This theorem is the operator-image version of the preconditioner and boundary
filter results. A proposed source-built operator `A` acting on polynomial tests
does not create a softer positivity target merely by replacing `p` with `A p`.
The decisive question is the closed image of the test space on `K`.

There are only three possibilities:

1. The closed image is all of `C_sym(K)`. Then positivity on `A`-tests is
   RH-strength.
2. The closed image vanishes on a hidden set `E`. Then the test proves RH only on
   `Y \ E`; hidden atoms require a separate source theorem.
3. The closed image has another obstruction. Then the operator proof must state
   that obstruction explicitly and prove it from source data before positivity is
   invoked.

Thus differential, difference, Christoffel, boundary, or renormalized test-space
operators do not by themselves bypass the atom-isolation wall. They must either
have dense source range, which keeps the RH wall intact, or expose exactly which
atoms their range cannot see.

## Theatre Test

For any operator-image positivity route, ask:

1. What is the operator `A` on test functions?
2. What is the uniform closure of `A(R[y])` on `K=Y union {0}`?
3. Which reciprocal atoms can this closed image isolate?
4. Which atoms are hidden, and what source theorem controls them?

Without these answers, an operator-image proof has not built a landscape; it has
changed the test space without accounting for the lost visibility.

## Gates

- [x] 0 -> 1 in-progress: closed-test-space invariant isolated.
- [x] 1 -> 2 fully-proven: complete closure/atom-isolation proof.
- [x] 2 -> 3 formalized: `RHTower/ReciprocalAtomTestSpaceClosure.lean`.

## Log

- 2026-06-24 -- Codex: created to classify source-built operator-image
  positivity routes. The invariant is the uniform closed test space on the
  reciprocal compact support, not the syntactic form of the operator.

## 2026-06-24 finite hard-edge counterterm specialization

`finite-hard-edge-counterterm-q0-rh-strength.md` records the finite-jet counterterm specialization. If a counterterm vanishes on `y^m R[y]`, then atom-isolators can be approximated inside that ideal by writing `p(y)=y^m r(y)`. Therefore positivity of `Q_0[p]+C[p]` for all polynomials still forces RH.

This is the closed-test-space theorem with the closed image containing all atom-isolators away from the hard edge `0` despite arbitrary prescribed finite vanishing order at `0`.

## 2026-06-24 finite-rank counterterm kernel case

`finite-rank-counterterm-kernel-visibility.md` is the finite-rank counterterm form of this closure theorem. If `C[f]=B(Lf)`, positivity of `Q_0+C` gives `Q_0>=0` on the closed test space `ker L`. The visible atoms are exactly those whose isolators lie in that kernel; all other atoms are quotient-hidden and require separate source control.

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

Card-specific.  `xiReciprocalAtom_nonneg_of_visible` is the main theorem: every `S`-visible atom
lies in `R_{>0}`.  `riemannHypothesis_of_visible_all` and
`xiQZero_nonneg_on_iff_riemannHypothesis` are clause 1 (a uniformly dense conjugation-symmetric test
space makes positivity equivalent to RH), and `xiReciprocalAtom_nonneg_of_dense_vanishing` is
clause 2 (a test space dense only in the functions vanishing on a set `E` still forces every atom
outside `E`; atoms inside `E` are untested).  The converse direction uses
`xiQZero_re_nonneg_of_riemannHypothesis`: under RH every atom is a nonnegative real and every
conjugation-symmetric bounded test gives a nonnegative form.
