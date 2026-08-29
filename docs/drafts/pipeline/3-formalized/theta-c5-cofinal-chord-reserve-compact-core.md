# Theta C5 cofinal chord reserve, intrinsic acceleration, and Riccati compensation

- **ID:** `theta-c5-cofinal-chord-reserve-compact-core`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** literal completed-theta source/product fibres and corpus derivative-decay bounds
- **Statement:** At every positive modular-center radius, source C5 is exactly accumulated
  full-source chord reserve minus a strictly positive likelihood tax density; source C5 is
  unconditionally strict near zero and eventually strict. Every possible failure therefore
  attains a negative stationary local minimum. Its third-jet C5 velocity vanishes, its exact
  fourth-flux C5 acceleration is nonnegative, and the strict theta fourth-Turan ceiling holds.
  After division by the positive accumulated-drop square, C5 is exactly four times the bounded
  cumulative endpoint-mass/elasticity balance. Every failure also attains a negative local
  minimum of this intrinsic balance, where raw C5 is strictly descending. The two critical
  witnesses are necessarily distinct and both strictly overspend the exact likelihood reserve.
  At every intrinsic local minimum, strict fourth-Turan eliminates the fourth jet and forces a
  normalized Riccati compensation budget to be strictly positive after paying an explicit
  fourth-Turan cost and a perfect-square cost.

## Goal

This theorem sharpens the open C5 predecessor in the corpus chain

```text
negative-minimum Riccati-budget upper envelope
  -> literal source rank-four odd wall
  -> physical center-mixed rank four
  -> higher packets plus cofinal no-escape
  -> universal tilt-flux / Xi-Weil positivity
  -> RH.
```

It closes seam and cofinal-tail burdens and eliminates the compact-annulus quantifier at modular
center. It does not prove stationary-locus reserve dominance, off-center transport, higher-packet
positivity, or the source-to-Weil no-escape join.

## Gates

- [x] 0 → 1 in-progress: corpus-derived source coordinates and explicit RH chain
- [x] 1 → 2 fully-proven: dependency-closed algebra, FTC, and decay proof
- [x] 2 → 3 formalized: targeted Lean builds green; axiom audit contains only `propext`,
  `Classical.choice`, and `Quot.sound`
- [ ] 3 → 4 publication-ready: standalone exposition and broader external review

## Approach

Let `F` be the completed first product fibre and `L = R(2+R)` the complete cofinal likelihood
factor. The literal tail jets are

```text
D_tail = D_first*L - F*L',
J_tail = J_first*L + 2*D_first*L' - F*L''.
```

The first fibre is seamed at zero, so the proof constructs its smooth positive-side flux and proves
exact interval-integral identities for first-fibre, source, and higher-tail drops. Expanding the
cofinal budget then gives

```text
driftBudget = firstDrop*tailDrop*chordReserve,
slopeTax + convexityTax = -(firstDrop*tailDrop)*taxDensity.
```

All component drops cancel from the final source sign:

```text
sourceC5(0,t) = integralChordReserve(t) - taxDensity(t),
taxDensity(t) > 0.
```

Corpus exponential bounds for every derivative of `thetaCuspFullSource` imply

```text
t*D(t) -> 0,
t^2*J(t) -> 0,
A(t) -> sourceProduct(0,0),
sourceC5(0,t) -> 24*sourceProduct(0,0)^2 > 0.
```

Combining this tail with the pre-existing strict coalesced C5 theorem yields the exact compact-core
reduction without a numerical cutoff or computation. Differentiating the C5 numerator gives

```text
C5Velocity = 39*A*D + t*A*J - 17*t*D^2 + t^2*(5*A*K - 3*D*J),
K = dJ/dt.
```

If C5 is negative anywhere, continuity and the two strict boundary chambers give a negative
minimum on a compact interval. Its endpoints are positive, so the minimum is interior and Fermat's
theorem forces `C5Velocity = 0`. Differentiating once more gives

```text
C5Acceleration = 22*D^2 + 40*A*J - 39*t*D*J + 11*t*A*K
               + t^2*(2*D*K + 5*A*L - 3*J^2),
L = dK/dt.
```

The minimum has `C5Acceleration >= 0`. Independently, the corpus strict fourth-Turan theorem is
exactly `q4 + 320 < 2*q2^2` in center reflected-action coordinates. Thus global center C5 is
equivalent to reserve dominance only where velocity vanishes and acceleration is nonnegative.

The cumulative-balance corpus identity gives the sharper amplitude-free normalization

```text
IntrinsicC5(t) := sourceC5(0,t)/sourceDrop(0,t)^2
                = 4*cumulativeEndpointMassElasticityBalance(0,t).
```

Strict C5 at both boundary chambers and compact minimization force any failure to attain a
negative local minimum of `IntrinsicC5`. Exact quotient differentiation at such a point gives

```text
C5Velocity*sourceDrop = 2*sourceC5*sourceFlux,
```

so raw C5 is strictly descending there. Conversely, at a negative raw-C5 stationary point the
intrinsic derivative is strictly positive. Therefore one failure forces two distinct critical
tax overspends. Global center C5 is exactly equivalent to reserve dominance only at positive
local minima of `IntrinsicC5`.

For the completed reflected action `q`, define

```text
r   = exp(q)-1,
s   = t*q1/r,
b   = t^2*(q2-q1^2)/r,
rho = t^3*(2*q1*q2-q3)/r,
P0  = 99*s - 123*s^2 + 24*s^4 - 51*b + 36*s*b + 16*s^2*b - 65*b^2.
```

At an intrinsic stationary point, exact algebra and the strict fourth-Turan ceiling give

```text
5*t^2*IntrinsicSecondOrderTuranCeiling
  = sourceDrop^4 *
      (P0 + 100*s*r*rho - 8000*t^4/r - 25*r*(b+2*s^2*r)^2).
```

Every intrinsic local minimum has positive left side. Therefore every possible C5 failure forces
strict normalized Riccati overcompensation after two explicit nonnegative costs, simultaneously
with the already-proved likelihood-tax overspend. This removes the fourth jet from the live burden.

## Lean certificate

- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureCofinalChordReserve`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureCompactCore`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureStationaryLocus`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureStationaryAcceleration`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureIntrinsicBalance`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureIntrinsicAcceleration`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureIntrinsicFourthTuran`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureIntrinsicRiccatiBudget`
- `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_eq_integralReserve_sub_taxDensity`
- `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_iff_taxDensity_le_integralReserve`
- `thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero_pos`
- `tendsto_thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_atTop`
- `exists_thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_compactCore`
- `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_stationary_taxOverspend`
- `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_stationary_taxReserve`
- `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_acceleration_taxOverspend`
- `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_stationary_acceleration_taxReserve`
- `thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_eq_four_cumulative`
- `thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_isLocalMin_velocity`
- `deriv_thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_pos_of_velocity_zero_neg`
- `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_two_distinct_critical_taxOverspends`
- `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_intrinsicBalance_localMin_taxReserve`
- `thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderTuranCeilingAtZero_eq_riccatiBudget`
- `thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero_pos_of_isLocalMin`
- `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_intrinsicRiccatiCompensation`
- `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_negativeIntrinsicMin_riccatiBudget_nonpos`

Targeted builds:

```text
lake build GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureCofinalChordReserve
lake build GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureCompactCore
lake build GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureStationaryLocus
lake build GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureStationaryAcceleration
lake build GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureIntrinsicBalance
lake build GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureIntrinsicFourthTuran
lake build GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureIntrinsicRiccatiBudget
```

## Novelty audit

August 2026 corpus searches found no earlier seam-safe product-fibre drop integral law,
component-drop cancellation, likelihood tax-density factorization, compact-core C5 theorem, or
stationary strict-overspend localization.
The primary-literature audit against Planat--Solé (arXiv:2608.19160) and Michałowski
(arXiv:2602.20313) found no corresponding C5 identity. This is an audit conclusion, not a Lean
theorem.

## Log

- 2026-08-29 — Exact chord-reserve-minus-tax identity and strict tax density formalized.
- 2026-08-29 — Cofinal positive limit and qualitative compact-core reduction formalized.
- 2026-08-29 — Exact C5 velocity and stationary-locus/tax-overspend reduction formalized.
- 2026-08-29 — Exact fourth flux jet and C5 acceleration formalized. Every failure now forces a
  stationary tax overspend with nonnegative acceleration and strict native fourth-Turan ceiling;
  the surviving reserve condition is restricted by an exact iff to that smaller locus.
- 2026-08-29 — Intrinsic drop-square normalization formalized. Every failure now forces two
  distinct critical overspends: an intrinsic-balance local minimum on the descending raw-C5 flank
  and a raw-C5 stationary minimum with nonnegative acceleration. The exact surviving reserve
  condition is restricted further to intrinsic local minima.
- 2026-08-29 — Intrinsic second derivative and strict fourth-Turan ceiling normalized into one
  exact Riccati compensation identity. Every failure now forces a negative intrinsic minimum where
  normalized Riccati growth exceeds the fourth-Turan cost plus a perfect-square cost, while the
  likelihood tax also overspends. Targeted build passed; axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- 2026-08-29 — Added
  `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureRiccatiBackwardDrift`. Exact normalized
  Riccati evolution exposes a strict forward lower drift, while the exact integrating factor
  conjugates it to a strictly increasing charge `exp(2q)*(2*q1*q2-q3)`. The proposed backward
  terminal-zero argument is therefore impossible. Lean also identifies charge with the raw source
  flux Wronskian `P(0)^2/P(t)^4 * -(P*K+D*J)`, proves `P*K+D*J < 0`, and proves the exact iff from
  global modular-center C5 to the charge-envelope inequality at negative intrinsic minima. This is
  a closed no-go plus positive survivor; `C5-RB1` itself remains open. Targeted module build passed;
  axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
