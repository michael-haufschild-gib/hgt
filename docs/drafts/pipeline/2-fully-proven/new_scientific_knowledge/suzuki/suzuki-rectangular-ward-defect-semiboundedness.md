# Suzuki rectangular Ward-defect semiboundedness reduction

- **ID:** `suzuki-rectangular-ward-defect-semiboundedness`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) + exact RH connector
- **Scientific status:** `[PROVED HERE] [LEAN-PROVED] [SOURCE-SPECIFIC BRIDGE]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Parents:** `suzuki-affine-sewn-weil-robin-far-tail-factorization.md`,
  `explicit-rectangular-two-edge-weil-completeness.md`, Suzuki's unconditional screw-line source
  vector.
- **Statement:** Exact source-to-Weil Gram equality is unnecessary.  On one fixed-width
  logarithmic rectangular mesh, a nonnegative source energy proves RH as soon as its Ward defect
  is eventually bounded below.  Under false RH that defect is cofinally unbounded below for every
  nonnegative source energy.

## Source and corpus input

Fix `L>0`.  The corpus constructs the multiplicity-exact Xi screw curvature

```text
Q_L(n)=Re xiScrewWindowCurvature(L,log n)                 (1)
```

and proves

```text
RH iff Q_L(n) is eventually bounded below
```

on nodes satisfying `L<=log(n)/2`.  More sharply, under false RH, `Q_L(n)` lies below every real
level cofinally.

Suzuki's 2025 source construction gives, without RH, explicit vectors `S_t` in ordinary
`L^2(R)` from the pole-cancelled completed prime--Gamma expression.  Under RH their Gram is the
screw kernel; Suzuki asks for exact equality of source norm and Weil form.  The 2026 operator paper
states the same frontier as equality of kernels of `pi^(-1) P^*P` and the continuous screw
operator.  These are primary-source inputs, not inferred from older model knowledge:

- [On the Hilbert space derived from the Weil distribution](https://arxiv.org/abs/2301.00421),
  especially the unconditional `L^2` source and conditional screw-line identity;
- Suzuki's 2026 finite-aperture operator source, arXiv:2606.09096, especially its stated
  `U^*U=-g''` kernel frontier.

The rectangular two-edge transform is a finite signed combination of the two time orientations
of Suzuki's source vectors.  Denote the resulting actual source vector at logarithmic aperture by
`R_L(n)` and normalize

```text
E_L(n)=||R_L(n)||^2 >= 0.                                (2)
```

No assertion that `(2)` equals `(1)` is made.

## Theorem: semibounded defect is enough

Define Ward defect

```text
Delta_L(n)=Q_L(n)-E_L(n).                                (3)
```

### Forward connector

Assume there are `B in R` and `N0` such that for every admissible `n>=N0`,

```text
B <= Delta_L(n).                                         (4)
```

Since `E_L(n)>=0`, equations `(3)--(4)` give

```text
B <= Delta_L(n) <= Delta_L(n)+E_L(n)=Q_L(n).             (5)
```

Thus `Q_L` is eventually bounded below.  Corpus rectangular completeness gives RH.

### Hostile-audit converse

Suppose RH is false and let `E(n)>=0` be any source energy, not necessarily Suzuki's.  Given
`B,N0`, corpus cofinal divergence supplies admissible `n>=N0` with `Q_L(n)<B`.  Therefore

```text
Q_L(n)-E(n) <= Q_L(n) < B.                               (6)
```

Hence every positive-source Ward defect is cofinally unbounded below.  A positive Gram cannot
hide false RH inside a semibounded error.

## Scientific consequence

Previous open core demanded an exact factorization

```text
Q_L(n)=||B_L(n)||^2,                                     (7)
```

including exact payment of midpoint `d^2`, holonomy, universal far tail, and Gamma channel.
Theorem `(3)--(6)` shows `(7)` is unnecessary.  It suffices to construct any explicit positive
source energy and prove

```text
Q_L(n)=E_L(n)+Delta_L(n),   inf Delta_L(n)>-infinity      (8)
```

on one cofinal arithmetic mesh.  Trace-class or finite-rank completion errors are admissible only
when their quadratic values on this orbit are uniformly lower bounded; ideal membership alone is
not enough.  This is materially weaker than a Christoffel--Darboux identity or an isometry.

## Corrected open core

### `SUZUKI-RECTANGULAR-WARD-DEFECT-SEMIBOUNDED` `[CONJECTURE]`

For one fixed `L>0`, form the rectangular source vector from the exact division-free affine-sewn
Weil--Robin channel:

```text
marked Robin + near-prime entry + universal far tail + polar--Gamma exterior.
```

Use Suzuki's unconditional pole-cancelled `L^2` source realization before taking any critical
boundary limit.  Prove only that defect `(3)` is uniformly lower bounded on
`a=log(n)/2`, `a>=L`.

Predictions and falsifiers:

- far primes must remain collectively mixed with Gamma; atomwise coordinates are ruled out by
  phase-aligned negative diagonals;
- exact equality, orthogonality of zero fibers, and cofinal characteristic convergence are not
  required;
- any decomposition of defect into a nonnegative bulk plus an endpoint term uniformly lower
  bounded on the logarithmic orbit proves conjecture — **formal** as
  `riemannHypothesis_of_suzukiRectangularWardDefect_bulk_endpoint` and its Hilbert-source form, so a
  candidate decomposition can be checked against the connector directly, with neither exactness nor
  orthogonality of the split required;
- one sequence of admissible logarithmic apertures with `Delta_L(n)->-infinity` falsifies it and,
  by `(6)`, is exactly what every off-critical Xi divisor forces — **formal** as
  `suzukiRectangularWardDefect_bddBelow_iff_not_cofinally_unbounded` (the bound and the divergence are
  exact negations) and
  `not_suzukiRectangularWardDefect_bddBelow_of_not_riemannHypothesis` (false RH therefore *refutes*
  the conjecture, for every nonnegative source energy, rather than merely obstructing it);
- a bound proved only after assuming Xi zeros real, Weil positivity, or a Herglotz target is
  circular and rejected.

Proving conjecture feeds the Lean theorem
`riemannHypothesis_of_suzukiRectangularHilbertWardDefect_eventually_bddBelow` directly and proves
RH.

## Novelty audit

Suzuki's source vector, its conditional exact norm identity, and Weil/screw positivity criteria
are prior work.  Corpus fixed-width logarithmic-mesh boundedness criterion is also prior internal
work.  Targeted searches found no source combining them to replace exact Suzuki isometry by the
strictly weaker semibounded Ward-defect condition, nor the universal hostile converse `(6)` for
every positive source energy.  This source-specific reduction is `[CANDIDATE NEW SCIENTIFIC
KNOWLEDGE]`; external priority remains unverified.

## Formal status

Formalized in
`formal/GaloisForLFunctions/RHTower/SuzukiRectangularWardDefectBoundedness.lean`.  Lean proves the
forward connector for arbitrary nonnegative energy and Hilbert norm squares, plus both false-RH
cofinal divergence converses.  It assumes no source factorization and does not formalize the still
open bound `(8)`.

## Log

- 2026-08-01 — audited: the forward connector and both false-RH converses are genuinely formal, and
  the converses hold for *arbitrary* nonnegative source energy and arbitrary seminormed source
  vectors, so "a positive Gram cannot hide false RH inside a semibounded error" is proved in full
  generality rather than for a particular source.  Added the open core's third prediction as a
  theorem: `riemannHypothesis_of_suzukiRectangularWardDefect_bulk_endpoint` shows a nonnegative bulk
  plus a lower-bounded endpoint suffices, chaining straight into the connector.  A named proof route
  is worth carrying as a proved sufficient condition, since that is what a candidate decomposition
  gets checked against.  Two new declarations, targeted build green, axioms
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the falsifiability made exact.
  `suzukiRectangularWardDefect_bddBelow_iff_not_cofinally_unbounded` shows the conjectured bound and
  the named falsifier are precise negations, so a candidate falsification is checked against the
  right statement.  Composing with the converse gives
  `not_suzukiRectangularWardDefect_bddBelow_of_not_riemannHypothesis`: false RH *refutes* the
  conjecture for every nonnegative source energy, not merely obstructs it.  That sharpens the card's
  "(6) is exactly what every off-critical Xi divisor forces" from an observation into an implication.
  Two new declarations, targeted build green, axioms `[propext, Classical.choice, Quot.sound]`.
