# Route F — all-prime Sonin transfer

- **ID:** `route-f-all-prime-sonin-transfer`
- **Stage:** 5-failed
- **Type:** RETIRED ROUTE / UNCONDITIONAL LEAN NO-GO
- **Statement:** Current Sonin completion route has no surviving source-faithful producer: the full
  geometric Burnol log-shell conductor has only logarithmic canonical-packet response at every
  finite height, while source curvature loss has positive linear order.

## Terminal theorem

For every fixed Sonin annulus, every geometric tower base and ratio, and every function choosing a
finite conductor height at each source scale, Lean theorem
`not_bddBelow_soninCompletedPacketValueVar_soninBurnolLogShellConductorFamily` constructs the
source's explicit admissible schedule and proves the corresponding completed packet values are not
bounded below.

Its load-bearing inputs are also unconditional:

- canonical packet spectral density is uniformly `O(|ξ|⁻¹²)` beyond twice the carrier;
- discarded Fourier energy is uniformly `O(t⁻¹¹)`;
- moving-threshold shell energy is height-independent;
- full position-plus-reflected Burnol conductor pairing is at most `C₀ + C₁ log A`;
- successive-layer curvature energy has an existing positive-linear source schedule.

## Exact scope

This retires current Route F, not every logically imaginable operator. A hypothetical arithmetic
order-one operator is not treated as an unfinished completion lemma: no such source object exists in
the route or located primary literature. Constructing one, or renormalizing away the Sonin
Weyl-volume term before Gamma attachment, starts a new route with a new source handoff.

## No-go closure

- **Exact killing theorem/mechanism:** affine-logarithmic full-conductor response versus
  positive-linear coupling energy, uniformly over arbitrary tower-height schedules.
- **Dead mechanisms:** bounded scalar; fixed operator; uniformly bounded operator family;
  sublinear-image family; every scalar below the proved linear threshold; position log-shell;
  frequency-reflected log-shell; fixed-height Burnol conductor; arbitrary-height full geometric
  Burnol conductor; aperture refinement without source compensation.
- **Strongest positive survivor:** any universal restorer must have packet-diagonal microlocal order
  at least one along the explicit schedule, or must remove the linear Weyl-volume term before an
  order-zero conductor is attached.
- **New insight:** obstruction is an order mismatch, not lack of tower height or insufficient
  regularization. Tate/Burnol conductor order is logarithmic; Sonin curvature defect is linear.
- **Status:** paper proof dependency-closed; exact Lean formalization complete; source modules contain
  no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe`; axiom audit is standard
  `[propext, Classical.choice, Quot.sound]`.

## Formal artifacts

- `RHTower/SoninPacketHighTailPolynomial.lean`
- `RHTower/SoninChannelMovingThreshold.lean`
- `RHTower/SoninBurnolFrequencyLogOrder.lean`
- `RHTower/SoninBurnolFrequencyLogarithmicOrderNoGo.lean`

## Log

- 2026-08-01 — terminal obstruction proved on paper and formalized; Route F retired; order-one or
  Weyl-renormalized positive survivor moved to a fresh backlog card.
