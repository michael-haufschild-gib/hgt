# Same-Hamiltonian qudit-path recurrence--collision law

- **ID:** `qudit-path-same-draw-recurrence-collision-law`
- **Stage:** 3-formalized
- **Type:** theorem / local many-body quantum recurrence
- **Date:** 2026-08-23
- **Status:** `[LEAN-PROVED] [BRIDGE]`

## Exact claim

Fix integers (n,qge 2), put (D=q^n), and take the exact real vector
space of Hermitian onsite and nearest-neighbour interactions on an open path
of (n) (q)-level sites. There is a canonical real coefficient presentation
(H_{n,q}(	heta)) of this space with a nonempty simple-spectrum chart. On
every nonempty connected open simple-spectrum chart (U), one common
full-measure set of coefficients has, for the same static Hamiltonian:

1. maximal balanced projective rank (D-1);
2. stroboscopic anchored-gap first-hit exponent (D-1);
3. first-gap-clock winding exponent (D-2);
4. every positive-weight replica collision mass at the permutation floor;
5. every positive-weight long-time survival-fidelity moment converging to
   that floor;
6. no nonzero exact anchored projective return.

## Frontier and hostile verdict

- `[CORPUS]` `exists_quditPathChain_coordinateFamily` provides one exact
  path-local coefficient family and affine real spectral escape.
- `[CORPUS]` `ae_tendsto_log_firstHit_sortedGap` and
  `ae_tendsto_log_firstHit_sortedGapRatio` give the two almost-everywhere
  exponent events for that family on every chart.
- `[CORPUS]` all-order collision and moment-floor equivalences consume
  maximal projectivity.
- Existing qudit capstones package the two exponent events separately and do
  not state their conjunction with maximality and all collision orders for one
  coefficient draw.

Hostile verdict: `[BRIDGE]` as a new mathematical mechanism, but a necessary
headline strengthening. It removes an artificial qubit restriction from the
paper's same-Hamiltonian law. Novelty remains in the local affine spectral
escape and its unified consequences, not in intersecting conull sets.

## Dependency-closed paper proof

Choose the coordinate family supplied by the exact path-local escape theorem.
It has (D=q^n), consists precisely of the real Hermitian onsite-plus-edge
space after a basis relabelling, and escapes every nonzero balanced real
spectral relation at every affine level.

For each nonzero balanced integer character (k), escape supplies a real
parameter and a simple real root packet (E) for which every relabelled value
(sum_i k_iE_{sigma(i)}) is nonzero. The product of these finitely many
relabelled values is the symmetric spectral-orbit obstruction for (k).
Vieta's identities express this obstruction as a polynomial in
characteristic coefficients, hence as a polynomial in the real Hamiltonian
coefficients. The escape witness shows that polynomial is nonzero. Its real
zero set is closed, nowhere dense, and Lebesgue null. Balanced integer
characters form a countable set, so the complement of the union of all their
zero sets is dense, residual, and full measure. At every coefficient in this
complement the spectrum is maximally projective. This argument uses the same
coordinate family as the metric laws.

On any nonempty connected open simple-spectrum chart, affine escape makes the
ordered anchored-gap map and the first-gap ratio map analytically
nondegenerate. Metric extremality therefore gives a full-measure non-VWA event
for each map. Intersect these two events with the maximal-projectivity event;
the intersection remains full measure. The exact first-hit law gives
exponents (D-1) and (D-2) on this single event.

Maximal projectivity is equivalent to replica rigidity at every order. The
finite multinomial expansion and symmetric-time dephasing identity then give
the permutation collision floor and long-time survival-moment floor for every
strictly positive weight and every replica order. Finally, because (Dge4),
maximal projectivity rules out a nonzero exact anchored projective return.

No paper-proof obligation remains. Formalization realizes both the capstone
conjunction and its reusable parameterwise-witness genericity bridge.

## Lean closure

- `volume_notMaximallyProjective_eq_zero_of_spectrumEscapesRealRelations`
  proves generic maximality from relation-by-relation escape in one exact
  coefficient family.
- `exists_quditPath_everyChart_sameDraw_recurrenceCollisionLaw` proves the
  six-clause conjunction above for arbitrary `n,q >= 2`.
- Direct file elaboration passed.
- Named target build passed; no umbrella target was built.
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- New module contains no `sorry`, `admit`, custom `axiom`, `opaque`, or
  `unsafe` declaration.

## Scope

- Static, finite, closed systems only.
- Full exact onsite-plus-nearest-neighbour Hermitian space; no longer-range
  interactions.
- Almost every coefficient on every connected open simple-spectrum chart,
  not every Hamiltonian.
- First exponent is stroboscopic; second is clock-normalized winding.
- Completed-time moments precede any thermodynamic size limit.
