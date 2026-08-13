# Finite half-turn repaired packets are never Markov

- **ID:** finite-half-turn-repaired-packets-not-markov
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / source-transfer guardrail
- **Source:** `half-turn-repaired-frequency-not-markov.md`;
  `bounded-half-turn-frequency-packets-fail-hankel.md`;
  `seam-log-markov-pick-rh-equivalence.md`

## Statement

Let `c_i>0` and `x_i>0` be a nonzero finite positive packet of half-turn
repaired squared frequencies. Define

`M_k=sum_i c_i x_i^k`,

and the repaired shifted seam moments

`U_k=M_k/(2k-1)!`, `k>=1`.

Then `(U_k)` is not a Stieltjes/Markov moment sequence on `R_+`. More precisely,
for all sufficiently large `k`,

`U_k U_(k+2) - U_(k+1)^2 < 0`.

Thus every finite positive half-turn repaired packet fails an adjacent `2 x 2`
shifted Hankel gate.

## Proof

Combine equal squared frequencies, so the `x_i` are distinct. Let

`R=max_i x_i`,

and let `C>0` be the total weight at `R`. Then

`M_k = C R^k (1+epsilon_k)`,

where `epsilon_k -> 0` exponentially fast. In particular, for each fixed
`d=0,1,2`,

`k epsilon_(k+d) -> 0`, so

`k (M_k M_(k+2)/M_(k+1)^2 - 1) -> 0`.

Thus, for all sufficiently large `k`,

`M_k M_(k+2)/M_(k+1)^2 < 1 + 1/k`.

Now compute

`U_k U_(k+2)/U_(k+1)^2`

`= (M_k M_(k+2)/M_(k+1)^2)
   * ((2k+1)!^2 / ((2k-1)! (2k+3)!))`

`= (M_k M_(k+2)/M_(k+1)^2)
   * ((2k)(2k+1)/((2k+2)(2k+3)))`.

The rate is essential: convergence to `1` alone would not control a second
factor also tending to `1`. For `k>=1`, the exact comparison is

`(1+1/k) * (2k)(2k+1)/((2k+2)(2k+3))`

`= (2k+1)/(2k+3) < 1`.

Hence the product is strictly less than `1` for all sufficiently large `k`.
Therefore

`U_k U_(k+2) < U_(k+1)^2`

eventually.

A Stieltjes moment sequence must have every adjacent `2 x 2` Hankel determinant
nonnegative, because

`m_k m_(k+2)-m_(k+1)^2
 = int int y^k z^k (z-y)^2 / 2 dnu(y)dnu(z) >= 0`

for any positive representing measure `nu` on `R_+`. The eventual strict
negativity above forbids such a representation. ∎

## Consequence for the RH Route

The half-turn is the nonlocal parity repair needed to move FE-even frequency
coefficients toward the seam-log Markov sign pattern. The earlier cards showed:

1. a single repaired frequency fails the first shifted Hankel gate;
2. narrow finite repaired packets fail the first shifted Hankel gate;
3. broad finite repaired packets can pass the first gate.

This theorem closes the finite positive repaired-packet loophole. Broad spread
can clear the first determinant, but finite support cannot clear all adjacent
Hankel gates: the top frequency eventually dominates, and the factorial
geometry forces log-convexity failure.

Therefore a source-built Markov/Pick proof for RH cannot be assembled from a
finite positive packet of half-turn repaired FE-even frequencies. The surviving
routes require at least one of:

- an infinite unbounded frequency distribution with genuinely all-scale mass;
- signed completed counterterms constrained by the Euler/Gamma/FE source;
- multiplicative correlations rather than additive positive packets;
- a boundary/index object proving the Stieltjes cone without frequency-packet
  decomposition.

## Boundary

This theorem does not rule out infinite positive repaired frequency measures.
That case is genuinely different: unbounded moment growth can defeat the
finite-support top-frequency argument. The theorem only proves that finite
positive repaired packets are not a possible completed source object.

## Theatre Test

For any proposed repaired-frequency RH proof:

1. If the repaired source object has finite positive support, this theorem
   kills it at a sufficiently high adjacent Hankel gate.
2. If the source object has infinite support, the proof must state which
   all-scale distribution law replaces top-frequency domination.
3. Passing finitely many repaired Hankel tests is not evidence of the all-order
   Markov cone; finite support can always fail later.

## Novelty Status

The proof is elementary. Its significance is route control: it closes the broad
finite-packet escape left open by the sharp first-gate threshold.

## Lean Formalization

Module:
`formal/GaloisForLFunctions/HTGeometry/FiniteHalfTurnRepairedPacketNoGo.lean`.

Principal declarations:

- `eventually_finitePositivePacketMoment_weighted_gap` formalizes dominant-node
  asymptotics with the rate needed to beat the factorial correction;
- `halfTurnRepaired_det_neg_of_weighted_gap` converts the weighted gap into the
  adjacent repaired Hankel determinant inequality;
- `finitePositivePacket_halfTurn_det_eventually_neg` proves eventual strict
  negativity;
- `finitePositivePacket_halfTurn_not_stieltjes` rules out a Stieltjes
  representation of the shifted sequence `n |-> U_(n+1)`.

Verification: targeted module build passes. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 -> 1 in-progress: broad finite repaired-packet loophole isolated.
- [x] 1 -> 2 fully-proven: eventual adjacent-Hankel failure proved by
  top-frequency asymptotics.
- [x] 2 -> 3 formalized: finite-support asymptotic rate, adjacent Hankel
  negativity, and Stieltjes no-representation theorem proved in Lean.

## 2026-06-24 infinite-source sequel

`infinite-half-turn-frequency-source-admissibility-split.md` records the infinite counterpart. Finite positive repaired packets always fail an eventual adjacent Hankel gate. Infinite positive repaired sources instead split: Markov positivity forces factorial moment curvature, while arbitrary sigma-finite mass accumulating at zero frequency can manufacture any Stieltjes target and therefore has no source-selecting power.

Thus the surviving repaired-frequency route is not merely "make the support infinite." It must be source-admissible: no arbitrary zero-frequency reservoir, and a source proof of the required all-scale moment curvature and higher Hankel gates.
