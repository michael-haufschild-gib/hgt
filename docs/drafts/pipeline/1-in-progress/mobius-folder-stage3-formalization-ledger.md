# Möbius folder stage-3 formalization ledger

- **ID:** `mobius-folder-stage3-formalization-ledger`
- **Stage:** 1-in-progress
- **Type:** PROGRAMME / LEAN SWEEP
- **Goal:** Lean-certify every `[PROVED]` statement of the ten cards in
  `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/mobius/`, then promote each
  card to `3-formalized`.  RH-bearing open gates stay open; only proved content is formalized.

## Cards and their proved payload

| # | Card | Proved payload needing Lean | State |
|---|---|---|---|
| 1 | `mobius-squarefree-reciprocal-projective-transfer` | (1)-(6), (7a)-(7b) | **DONE** |
| 2 | `mobius-critical-exponential-boundary-layer-law` | (1)-(3), (5)-(8), (12)-(15) | **DONE** |
| 3 | `mobius-half-unit-exponential-moment-rh-law` | S2 (5)-(7), S3 (8)-(12), S5 (18)-(21) | open |
| 4 | `mobius-channel-critical-mass-escape-law` | (4)-(12), S5 (14)-(15) | **DONE** |
| 5 | `mobius-schur-centered-boundary-limit-law` | (3)-(5), (11)-(17) | open |
| 6 | `mobius-schur-causal-critical-graph-limit-law` | (5)-(7), (13)-(17) | open |
| 7 | `mobius-prime-aperture-differential-order-profile` | (4), (8), (16)-(18), (20)-(23) | open |
| 8 | `mobius-logarithmic-jet-ht-transfer-li-no-holonomic-route` | transfer thm; non-D-finite; Li | open |
| 9 | `mobius-signed-channel-coisometry-incidence-law` | (5)-(10), (15)-(17), (19)-(23), (25)-(27) | partial: coisometry layer done |
| 10 | `mobius-signed-coisometry-schur-transfer-law` | (4)-(13), (17)-(18), (21)-(23), (23a)-(23i) | partial: Schur + power-sum done |

## New Lean modules added by this sweep

- `RHTower/MobiusChannelCriticalMassEscapePaperCertificate.lean` — card 4 complete.
- `RHTower/MobiusSquarefreeReciprocalProjectivePaperCertificate.lean` — card 1 complete
  (Dirichlet comparison bound, safe-correction holomorphy/nonvanishing/contractivity, the
  completed transfer and its Ward connection `2 dlog T = Q_sq`).
- `RHTower/MobiusSignedSchurComplexMultiplier.lean` — card 10 (9)-(13): the all-prime Schur
  multiplier on the closed right half-plane.
- `RHTower/MobiusPowerSumBoundaryLaplace.lean` — card 10 (14),(17): the causal Laplace transform
  of the shifted power-sum boundary vector, `zeta(1+z)/(1+omega+z)`.
- `RHTower/MobiusCriticalBoundaryLayerQuantiles.lean` — card 2 (7),(12),(13) and the moving
  aperture laws, via portmanteau against the unit exponential law.
- `RHTower/MobiusCriticalExponentialBoundaryLayerPaperCertificate.lean` — card 2 complete.
- `RHTower/VectorSignedChannelCoisometry.lean` — card 9 (5)-(10),(22),(25)-(27): the
  vector-valued signed coisometry, its projection, and closed-operator channel commutation.

## Existing Lean assets found (do not duplicate)

- `RHTower/SquarefreeMoebiusNormalization.lean` — `sum mu(n)^2 n^-s = zeta s / zeta (2s)`,
  arithmetic + LSeries + Euler-product faces.
- `RHTower/InfiniteMobiusSignedChannel.lean` — squarefree mass/probability, signed unit vector in
  `l2`, coisometry, idempotent projection, logarithmic shift average contraction.
- `RHTower/InfiniteMobiusLaplaceMultiplier.lean` — causal Laplace pairing, multiplier
  `= 1/(Z_sigma zeta(sigma+z))`.
- `RHTower/InfiniteMobiusCausalShift.lean` — causal (lower-support) preservation.
- `RHTower/InfiniteMobiusCriticalBoundaryLayer.lean` — exact boundary-layer Laplace transform and
  its `omega -> 0` limit.
- `RHTower/InfiniteMobiusCriticalLaplaceResponse.lean` — `tau/(1+u)` critical response.
- `RHTower/MobiusChannelCriticalMassEscape.lean` — exact contraction norm, coordinate escape, weak
  convergence, no strong convergence, compact-synthesis annihilation.
- `RHTower/MobiusFiniteSchurTransfer.lean`, `RHTower/FiniteSignedChannelCoisometry.lean` — finite
  aperture Schur/coisometry core.
- `RHTower/MobiusSquarefreeReciprocalTransfer.lean`, `RHTower/ZetaTwoShiftContraction.lean` —
  safe squarefree correction and its positive shift-average contraction.
- `RHTower/MobiusCausalMultiplier*.lean`, `MobiusCausalBoundaryEnergy.lean`,
  `MobiusCausalFlatLimit.lean` — coupled causal multiplier `M_omega`, uniform boundary majorant,
  `tendsto_boundary_multiplier_energy` (H^2 convergence to `1/(1+z)`), Fisher flatness.
- `RHTower/ZetaShiftedLineBound.lean` — uniform `1/zeta` and `zeta'/zeta` bounds on
  `Re s = 1+2omega`.
- `RHTower/ZetaVerticalLineBound.lean` — `|zeta| <= log|t| + 5` on `1 <= sigma <= 2`.
- `RHTower/Sieve/PrimeCountingBigO.lean` — PNT with error term.
- `RHTower/MobiusLaplaceMellinPlancherelBridge.lean` — Mellin-Plancherel line energy.

## Log
- 2026-08-19 — ledger created; corpus survey started.
- 2026-08-19 — cards 1, 2, 4 fully certified in Lean; cards 9, 10 partially certified.
