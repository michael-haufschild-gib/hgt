# Finite-Rank Counterterm Kernel Visibility

- **ID:** finite-rank-counterterm-kernel-visibility
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / route normalization
- **Source:** `test-space-closure-q0-visible-rh.md`,
  `finite-hard-edge-counterterm-q0-rh-strength.md`,
  `finite-rank-one-selector-no-free-lunch.md`
- **Statement:** A finite-rank counterterm can only give source-free information
  on the kernel of its boundary map. Any bad reciprocal atom not isolable in
  that kernel has been moved into the finite-dimensional quotient and requires
  a separate source theorem.

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

be a continuous real-linear map, and let `B` be a real quadratic form on `R^r`.
Define the finite-rank counterterm

`C[f] = B(Lf)`

and the renormalized form

`R_C[f] = Q_0[f] + C[f]`.

## Theorem

If

`R_C[f] >= 0 for every f in C_sym(K)`,

then

`Q_0[f] >= 0 for every f in ker L`.

The same conclusion holds if positivity is first proved only on real
polynomials, provided `L` is the restriction of the continuous map above: real
polynomials are uniformly dense in `C_sym(K)`, and `R_C` is continuous for the
uniform norm.

Consequently, every reciprocal atom that is visible to the closed test space
`ker L` lies in `R_{>0}`. In particular, if `ker L` contains the atom-isolators
for all atoms outside a closed conjugation-invariant set `E`, then positivity of
`R_C` forces RH on `Y \ E`; atoms in `Y cap E` are quotient-hidden.

## Proof

If `f in ker L`, then `C[f]=B(0)=0`, so

`0 <= R_C[f] = Q_0[f]`.

Thus `Q_0` is positive on the closed test space `ker L`. The atom-isolation
conclusion is exactly `test-space-closure-q0-visible-rh.md` applied to
`S=ker L`.

If `ker L` contains the isolators for all atoms outside `E`, then the same
closure theorem excludes every bad atom in `Y \ E`. Atoms whose isolators are
not in `ker L` are not tested by this kernel argument; they have been moved into
the finite-dimensional quotient `R^r`.

## Countermodel: Finite Rank Can Hide a Bad Atom

The kernel condition is necessary. In an abstract reciprocal-divisor model with
one negative real atom `a<0` of multiplicity `M`, take

`Q_0[f] = M a f(a)^2`.

Let `L(f)=f(a)` and

`C[f] = -M a L(f)^2`.

Then `C` has rank one and

`R_C[f] = 0`

for every test function, although the atom is off the positive real axis. The
counterterm succeeds only because it is zero-fed: its quotient is exactly the
bad atom evaluation.

For a non-real conjugate pair `a, conjugate(a)`, the same construction uses the
real two-dimensional quotient `f(a) in C` and the counterterm

`C[f] = -2M Re(a f(a)^2)`,

which cancels the pair contribution.

These examples do not prove anything about the actual zeta divisor. They show
that finite rank is not by itself a source certificate. A finite-rank repair must
explain why its quotient is source-built and why no bad atom is hidden there.

## Consequence for the RH Route

Finite-rank boundary or renormalization language has two distinct parts:

1. **Kernel theorem.** On `ker L`, the counterterm disappears. Positivity there
   is a usual `Q_0` visibility test.
2. **Quotient theorem.** Any atom whose isolator has nonzero image under `L`
   lives in the finite-dimensional quotient. Positivity in that quotient is a
   Schur/Weyl/Krein statement and can be zero-fed unless `L` and `B` are
   constructed from source data before the divisor is read.

Thus a finite-rank repair is not automatically a proof engine and not
automatically harmless. It is harmless only for atoms visible in the kernel; it
can hide atoms precisely in its quotient. A non-mirror RH proof must therefore
give a source theorem for the quotient, not merely exhibit a finite-rank positive
repair.

## Theatre Test

For any finite-rank counterterm or boundary repair, ask:

1. What is the boundary map `L`?
2. Which reciprocal atom-isolators lie in `ker L`?
3. Which atoms have nonzero image in the finite-dimensional quotient?
4. Is the quotient form source-built before reading the divisor, or does it
   encode the bad atom evaluations it repairs?

Without those answers, finite-rank positivity is a coordinate chart, not a
source selection theorem.

## Gates

- [x] 0 -> 1 in-progress: finite-rank kernel/quotient split isolated.
- [x] 1 -> 2 fully-proven: kernel theorem and zero-fed countermodels proved.
- [x] 2 -> 3 formalized: `RHTower/ReciprocalAtomCounterterm.lean`.

## Log

- 2026-06-24 -- Codex: created to classify finite-rank counterterms after the
  finite hard-edge counterterm theorem. The key point is that finite rank can
  hide atoms in its quotient unless the quotient has a source proof.

## 2026-06-24 non-atomic quotient specialization

`non-atomic-finite-rank-counterterms-rh-strength.md` records the main source-facing specialization of the kernel theorem. If the finite-rank boundary map has no point-mass component at any reciprocal atom, then it annihilates every atom-isolator. Hence positivity of `Q_0+B(L.)` remains RH-strength.

Therefore the quotient can hide bad atoms only by seeing their isolators. In measure terms, that means atom-evaluation content on the reciprocal support.

## 2026-06-24 quotient inertia is a boundary Schur matrix

`finite-rank-boundary-schur-index.md` gives the finite-dimensional quotient algebra complementary to this kernel theorem. The kernel theorem says which atoms remain visible after the boundary map is imposed; the Schur-index theorem says how the finite quotient changes inertia once the boundary form is fixed.

Both parts are necessary. Kernel visibility alone does not prove the quotient sign, and the quotient Schur matrix is source-relevant only if its boundary channels and form are constructed before the reciprocal divisor is read.

## 2026-06-24 general atom-local counterterm audit

`continuous-counterterm-atom-locality.md` generalizes the finite-rank kernel warning. For any continuous quadratic counterterm, finite-rank or not, the decisive local question is its restriction to each reciprocal atom-isolator subspace. If it vanishes there, the repaired positivity remains RH-strength; if it does not, the proof must explain how those atom-local values were source-built.

## 2026-06-24 quotient payments are local domination thresholds

`continuous-counterterm-local-domination-threshold.md` identifies the exact finite-dimensional bill paid by any quotient that sees a bad atom. For a finite-rank repair, the hidden quotient is source-relevant only if its boundary form supplies the required scalar or two-dimensional Loewner domination from source data.

This refines the kernel/quotient split: the kernel leaves atoms visible; the quotient can hide them only by paying the atom-local threshold.

## 2026-08-15 Lean partial formalization

`GaloisForLFunctions.HTGeometry.FiniteRankCountertermKernelVisibility` now proves the closed
algebraic part of this card for arbitrary real modules and quadratic forms:

- `finiteRankCounterterm_eq_base_on_ker`: `Q + B.comp L` equals `Q` on `ker L`.
- `finiteRankCounterterm_nonneg_on_ker` and
  `finiteRankCounterterm_no_negative_kernel_witness`: global repaired nonnegativity forces
  base-form nonnegativity on every kernel witness.
- `finiteRankCounterterm_kernel_isClosed`: the kernel of a continuous linear boundary map is
  closed.
- `rankOneZeroFedCounterterm_cancels` and `rankOneZeroFedBase_one_neg`: an exact rank-one
  negative base square can be cancelled identically by a zero-fed quotient counterterm.
- `RHTower.FiniteRankCountertermXiVisibility` adds the exact Xi-Weil bridge:
  if the correction vanishes on every off-real Xi sign test, then repaired Xi-Weil
  positivity still forces RH.

The full card remains Stage 2. Its compact reciprocal carrier, folded `Q_0`, atom-isolator bridge,
and a valid density theorem are not formalized. In particular, continuity of `L` alone does not
imply the asserted raw-real-polynomial density on an arbitrary complex compact carrier. Also,
an atom-isolator outside `ker L` only defeats this kernel witness argument; it does not by itself
prove that the atom is fully quotient-hidden.

Checks passed: direct `lake env lean`, targeted builds of
`GaloisForLFunctions.HTGeometry.FiniteRankCountertermKernelVisibility` and
`GaloisForLFunctions.RHTower.FiniteRankCountertermXiVisibility`, and `#print axioms`
for the kernel gate, zero-fed cancellation, and Xi bridge (only `propext`,
`Classical.choice`, and `Quot.sound`).

## 2026-08-15 strict kernel pre-gate

`finiteRankCounterterm_pos_on_ker` now also proves the strict form: if the
repaired quadratic form is strictly positive on every nonzero vector, then the
base form is strictly positive on every nonzero vector in `ker L`. This is the
exact reusable strict version required by rank-one Uvarov boundary repairs.
It passed direct source and targeted module checks; its axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.

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

Card-specific.  `xiRepairedForm C f = Re Q_0[f] + C[f]` is `R_C`.  With `C[f] = B(L f)` for a real
linear `L` into `R^r` and a real quadratic form `B`, `xiQZero_re_nonneg_on_ker` is the kernel
theorem: repaired nonnegativity gives bare `Q_0` nonnegativity on `ker L`, because `B(0) = 0`.
`riemannHypothesis_of_finiteRank_kernel_visible` is the visibility consequence: if the kernel test
space still resolves every atom, the finite-rank repair is RH-strength.
`riemannHypothesis_of_boundaryMap_kills_isolators` is the case where `L` annihilates every isolator.
The zero-fed countermodel is `xiAtomFedCounterterm`, which by `xiAtomFedCounterterm_factors_eval`
factors through the single evaluation `f |-> f(a)` — rank one — and by
`xiAtomFedCounterterm_cancels` makes the repaired form vanish identically on that atom's isolator
subspace, with `xiAtomFedCounterterm_eq_of_eq_conj` and `xiAtomFedCounterterm_eq_of_ne_conj`
identifying it with the card's `-M_a a f(a)^2` and `-2 M_a Re(a f(a)^2)`.  The real-quadratic-form
abstraction of the kernel gate remains available in
`HTGeometry/FiniteRankCountertermKernelVisibility.lean`.
