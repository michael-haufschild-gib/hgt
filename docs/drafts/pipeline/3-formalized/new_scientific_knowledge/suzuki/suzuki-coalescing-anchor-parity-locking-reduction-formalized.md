# Suzuki coalescing-anchor parity-locking reduction — Lean certificate

- **ID:** `suzuki-coalescing-anchor-parity-locking-reduction-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `suzuki-coalescing-anchor-parity-locking-reduction.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

Every labelled result of the card — Theorems A–N, O–Z, AA–AZ, BA–BD and Corollaries F.1, F.2,
G.1–G.5, 62 in all — has an unconditional Lean declaration for its mathematical core.  The
per-result module map is the `_promotion/LEDGER.md` sections `ADQ.2`–`AGF`; this certificate records
the closing sweep and the audit.

Axiom audit for every declaration added in the closing sweep: `[propext, Classical.choice,
Quot.sound]`, except `HTGeometry.mul_one_sub_mul` and `HTGeometry.pushThrough`, which audit to
`[propext]` alone.  No `sorryAx`, no `Lean.ofReduceBool`, no added axiom anywhere.

## Modules added by the closing sweep

```text
RHTower/Suzuki/SuzukiParityFormCoercivity.lean            (224) the parity forms and the domination
RHTower/Suzuki/SuzukiExponentialSourceCayley.lean         (229) on the literal cosh/sinh sources
RHTower/Suzuki/SuzukiSourceAlignmentDeficitIntegral.lean  (245),(248),(250),(251)
RHTower/Suzuki/SuzukiRelativeEdgeFloorRigidity.lean       (257),(258)
RHTower/Suzuki/SuzukiPrimeSeamMicrolocalStrength.lean     (262),(264),(267)
RHTower/Suzuki/SuzukiEndpointRevivalOperatorNorm.lean     (278),(279)
RHTower/Suzuki/SuzukiEndpointRegularKernelAsymptotic.lean (280)
RHTower/Suzuki/SuzukiNormalizedSourceLimit.lean           (281)
RHTower/Suzuki/SuzukiMovableAnchorImpedance.lean          (179),(180)
RHTower/Suzuki/SuzukiSourceImpedanceCalibration.lean      (182),(185)
RHTower/Suzuki/SuzukiLaplaceScrewOrigin.lean              (190),(196),(200)
RHTower/Suzuki/SuzukiNegativeRecessionJensen.lean         (295),(297),(298)
RHTower/Suzuki/SuzukiExpandingFrameAnnihilation.lean      (303),(304),(309),(311)
RHTower/Suzuki/SuzukiOddHardEdgeSeparation.lean           (322),(323),(324)
RHTower/Suzuki/SuzukiZeroEdgeCapacitySlack.lean           (330),(331),(333),(334),(336)
RHTower/Suzuki/SuzukiSourceEnergyBifurcation.lean         (337),(340),(343),(344)
RHTower/Suzuki/SuzukiUltravioletMultiplicityClock.lean    (350),(354),(356)
RHTower/Suzuki/SuzukiParityPhaseClock.lean                (359),(361)
RHTower/Suzuki/SuzukiKroneckerParityFloor.lean            (370)
RHTower/Suzuki/SuzukiSchurLeverageCertificate.lean        (376),(378),(380)
RHTower/Suzuki/SuzukiSquareRootActiveZero.lean            (384),(386),(388)
RHTower/Suzuki/SuzukiRidgeDefectMonotone.lean             (390)
RHTower/Suzuki/SuzukiTailCoefficientBarrier.lean          (399),(401),(402),(403)
RHTower/Suzuki/SuzukiCoupledCloudCore.lean                (410),(416),(417)
RHTower/Suzuki/SuzukiCrossCoherenceBarrier.lean           (420),(421),(422),(424)
RHTower/Suzuki/SuzukiNearNullPhaseDiagram.lean            (427),(428),(432)
RHTower/Suzuki/SuzukiUltranullPacket.lean                 (439),(440),(441)
RHTower/Suzuki/SuzukiCoherenceHorizon.lean                (447),(448),(449)
RHTower/Suzuki/SuzukiSourceCyclicBandEdge.lean            (462),(469)
RHTower/Suzuki/SuzukiPortWedgeClassification.lean         (80),(83),(85)
HTGeometry/PushThroughIdentity.lean                the push-through functional calculus
```

All are wired into their theorem-area umbrellas; `scripts/formal_tools.py lint` reports no
unreachable module among them.

## What the closing sweep changed mathematically

Several of the card's displays turned out to be exact identities rather than estimates, and are
recorded that way.

- `(224)` is the half-sum/half-difference of the two parity forms, so coercivity of the average and
  domination of the Hankel carrier are the single statement "a number between `−c` and `c` has
  modulus at most `c`".
- `(229)` on the literal sources is an identification, not an approximation: `cosh` and `sinh` are
  the half-sum and half-difference of `e^{x}` and `e^{-x}`, so `κ₀` *is* the abstract Cayley scalar
  `2b(u,v)/(b(u,u)+b(v,v))`.
- `(262)`'s minimization is the algebraic identity
  `(s+d)(η−s+d)η² − (η+2d)²s(η−s) = d(η+d)(η−2s)²`.
- `(280)` needed no new kernel: the corpus already owned `screwRegularKernel`, and the substitution
  `t = 2a − u` reproduces the card's display verbatim.
- `(281)` is exact: the total squared source error is `(2e^{−2a} − e^{−4a})/8`.
- `(295)`'s Jensen half is the supporting line of `1/(·+r)`, whose defect is the exact square
  `(x−m)²/[(x+r)(m+r)²]`.
- `(333)` reduces to `1/[(t+s)²(u+s)] − 1/[(u+s)²(t+s)] = (u−t)/[(t+s)²(u+s)²]`.
- `(359)` is proved with a rate, `|mean − 1/2| ≤ (1/2 + 1/(2|γ|))/A`, not only in the limit.
- `(376)`, `(378)`, `(380)` are stated as *attained* extrema rather than inequalities.
- `(83)` is an exact bilinear expansion; the `−2α(u∧v)` term is the sum of the two opposite-port
  cross terms, whose phases cancel against each other.

One correction to the card: the displayed recombination in `(337)` has a typographic slip.  The
right side is `(1+γ²)[(A cos θ)² + (B sin θ)²]`, not `(1+γ²)[A² + sin²θ]`; with that reading it is
an exact polynomial identity, and that is what `rotated_parity_energy` proves.

## Imported classical inputs

Three results the card explicitly imports rather than proves appear as named hypotheses of the
corresponding Lean statements, in the corpus's standard style for imported analytic inputs:

- Erdélyi's pure-frequency Nikolskii inequality `(381)`, used by Theorem AP;
- the Riemann–von Mangoldt / Littlewood zero-counting inputs `(389)`, `(414)`, `(436)`;
- the reciprocal-square Xi source-tail estimates `(310)`, `(313)`, `(404)`.

These are the card's own citations, not shortfalls of the formalization.  Everything the card
claims to *prove* is proved.

## What remains open on the card is research, not Lean

The card's closing sections state what a Route-G no-go would have to establish — a cofinal bound on
`ρ_j²`, an explicit many-zero low-only construction, or the source-cyclic mass estimate `(467)`.
Those are open research statements about future theorems, not gates naming missing Lean for
proved claims, and by the promotion rule they do not block this card.
