# Infinite l-bit recurrence--locality tradeoff

- **ID:** `infinite-lbit-recurrence-locality-tradeoff`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Anderson-locality merger for universal recurrence paper
- **Statement:** One infinite quasi-local diagonal field has a volume-uniform
  exponential influence cone while every finite environment of one local
  flip carries the maximal \(2^{|F|}\) temporal rank.

## Goal

Replace finite-volume Anderson coexistence by one genuine infinite law:
spatial propagation and observer-visible temporal dimension are independent
resources. For the already formalized countable l-bit coefficient field,
prove a weighted interaction mass
\[
  K=\sum_A 2^{\operatorname{diam}(A)}|J_A|<\infty
\]
and the all-volume commutator bound
\[
  \|[\tau_t(X_x),X_y]\|
  \le \min\{2,4K |t|2^{-|x-y|}\}.
\]
Combine it, for the same coefficient field, with maximal rank of every
finite packet of coefficients incident on \(x\).

This is not a transfer to a microscopic random-field XXZ or Anderson
Hamiltonian. The diagonal l-bit field itself is the exact model.

## Gates

- [x] 0 → 1 in-progress: exact statement, proof mechanism and hostile
  boundary identified
- [x] 1 → 2 fully-proven: weighted summability, double-flip identity,
  phase-commutator bound and same-field local-rank capstone
- [x] 2 → 3 formalized: unconditional Lean capstone and axiom audit
- [ ] 3 → 4 publication-ready: external priority and Nature significance

## Approach

1. Prove weighted summability from the existing support complexity; the
   dyadic diameter penalty survives multiplication by \(2^{\operatorname{diam}}\)
   because the injective encoding still supplies a summable majorant.
2. Define the Boolean site flip and prove that a double flip annihilates
   every interaction not containing both sites.
3. Bound the double energy difference by four times the incident weighted
   tail. Since \(x,y\in A\) forces \(|x-y|\le\operatorname{diam}(A)\), extract
   exponential distance decay.
4. Convert the energy bound to a phase bound using
   \(|e^{ia}-e^{ib}|\le|a-b|\), then to the uniform norm of the Heisenberg
   flip commutator.
5. Restrict the same coefficient field to every finite environment and
   invoke Walsh inversion plus rational independence for exact
   \(2^{|F|}\) local-flip temporal rank.

## Formalization

Implemented in
`formal/GaloisForLFunctions/HTGeometry/InfiniteLBitRecurrenceLocalitySeparationLaw.lean`.

Capstones:

- `summable_quasiLocalInfiniteLBitWeightedCoefficient`;
- `abs_infiniteLBitEnergyDoubleFlip_le`;
- `norm_quasiLocalInfiniteLBitFlipCommutator_le_min`;
- `quasiLocalInfiniteLBitIncidentRestriction_localFlip_fullRank`;
- `quasiLocalInfiniteLBit_fullRank_and_commutatorBound`.

The theorem acts on continuous complex amplitudes over the infinite Boolean
configuration space with uniform norm. Its commutator estimate is
operator-normalized: it holds for every amplitude with the right-hand side
multiplied by its norm. `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Hostile boundary

- The logarithmic light-cone mechanism of diagonal l-bit models is known;
  novelty can only lie in the exact same-field recurrence-rank/locality
  synthesis and any new sharp tradeoff.
- Current infinite evolution acts on continuous amplitudes with uniform
  norm, not yet on a selected \(L^2\) Hilbert space.
- Tiny independent coefficients contribute exact completed-time rank but
  may be operationally unresolved at finite time.
- No microscopic disorder ensemble or interacting MBL derivation is
  claimed.

## Log

- 2026-07-31 — finite graph-distance envelope rejected as thermodynamically
  cosmetic; infinite weighted l-bit candidate selected.
- 2026-07-31 — weighted summability, double-flip cancellation,
  Heisenberg-flip commutator cone and same-field maximal local rank proved
  and formalized.
