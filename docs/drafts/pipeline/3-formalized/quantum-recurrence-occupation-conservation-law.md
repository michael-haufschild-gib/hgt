# Quantum recurrence occupation--constraint conservation

- **ID:** QROC-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** quantum-recurrence paper revision
- **Statement:** For every nonempty finite spectrum, the small-tolerance exponent of completed projective returns plus the rational rank of exact balanced spectral relations equals the number of energy levels minus one.

## Goal

Prove a premise-complete finite-spectrum geometric identity.  This theorem is
not the manuscript's physical capstone: its occupation exponent is local Haar
dimension and its complementarity with relation rank is rank--nullity.  Its
role is to describe the finite pure-point carrier after the independently
defined stationary survival law has selected that carrier.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `projectiveRecurrenceOccupation_constraint_conservation`, targeted build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + formal certificate + novelty audit)

## Definitions

For a finite spectrum with `N` labelled levels, quotient away global phase.  Let `K` be the closure of the resulting one-parameter projective phase orbit and let `mu_K` be its normalized Haar law.  For projective phase tolerance `delta > 0`, let

`F(delta) = mu_K {x in K : projective phase distance from x to the identity is < delta}`.

Let `alpha` be the logarithmic small-target exponent of `F`, and let `rho` be the rational rank of exact balanced spectral relations.

## Conjecture under attack

`alpha + rho = N - 1`.

Boundary convention is intrinsic rather than patched: for a stationary projective orbit, `F(delta)=1` for every positive `delta`, hence `alpha=0`.

## Approach

1. Present the completed projective orbit as the injective integer image of a finite torus whose dimension is the rational rank of the anchored gaps.
2. Use bi-Lipschitz control of that embedding to squeeze the physical return target between intrinsic torus balls.  Haar small-ball scaling then proves `alpha` equals orbit dimension.
3. Apply projective rank-nullity: orbit dimension plus exact balanced-relation rank equals `N-1`.
4. Identify pushforward Haar measure with the unique completed-time law, so the exponent is a long-time occupation statistic of the actual evolution.

## Proof

**[PROVED HERE]** Let the spectrum have `N=d+1` labelled levels and subtract the
energy of one reference level.  The resulting `d` anchored gaps generate a
finite-dimensional rational vector space of rank `k`.  A rational basis of
that space writes the gap packet as an integer matrix applied to `k`
rationally independent frequencies.  Kronecker equidistribution identifies
the completed projective orbit with the image of Haar measure on the
`k`-torus.  The integer torus map is injective and bi-Lipschitz onto this
image.

For a projective phase ball of radius `delta`, the inverse image under that
bi-Lipschitz map is trapped between intrinsic `k`-torus balls of radii
`a delta` and `b delta` for fixed positive `a,b`.  Haar measure of an
intrinsic small ball is exactly `(2r)^k`; hence the completed return fraction
`F(delta)` satisfies two positive constant multiples of `delta^k`.  Taking
`log F(delta)/log delta` as `delta` decreases to zero gives `alpha=k`.  This
also covers `k=0`, when the torus is a point, `F(delta)=1`, and `alpha=0`.

Finally, rational evaluation of balanced projective characters against the
energy list has image equal to the anchored-gap space and kernel equal to the
rational span of exact balanced spectral relations.  Rank--nullity gives
`k + rho = d = N-1`.  Substituting `alpha=k` proves
`alpha + rho = N-1`.

## Falsifiability and scope

- Exact finite-dimensional theorem; no generic spectrum, simple spectrum, chaos, randomness, or locality premise.
- Predicts a log--log slope for completed-time return occupation and an exact complementarity with independently reconstructed spectral relations.
- Does not assert finite-window convergence rates, environmental isolation, or that a laboratory realizes the model exactly.
- Experiments can test a finite Hamiltonian realization and finite-window convergence; they cannot prove the universal mathematical quantifier.

## Novelty gate

The general recurrence-rate/local-dimension connection is established in
classical dynamics and cannot be claimed as new.  The displayed identity is
principally a complete specialization of local Haar dimension and
rank--nullity to finite quantum phase orbits.  It may be useful inside the
observer and local-Hamiltonian hierarchy, but it must not be advertised as an
independent phenomenological conservation law or as evidence for the physical
carrier theorem.

## Log

- 2026-08-28 — created in 1-in-progress after rejecting the manuscript's conjunction-style "architecture theorem" as a capstone law.
- 2026-08-28 — paper proof closed.  Formalized in `GaloisForLFunctions.HTGeometry.UniversalRecurrenceOccupationConservationLaw`; targeted build passed.  Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-08-28 — demoted from proposed headline law after anti-circularity audit: valid and formally complete, but its dramatic form is dimension theory plus rank--nullity after the return target is defined.
