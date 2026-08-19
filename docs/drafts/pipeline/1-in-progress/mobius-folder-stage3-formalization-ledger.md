# Möbius folder stage-3 formalization ledger

- **ID:** `mobius-folder-stage3-formalization-ledger`
- **Stage:** 1-in-progress (COMPLETE: all ten cards promoted to 3-formalized)
- **Type:** PROGRAMME / LEAN SWEEP
- **Goal:** Lean-certify every `[PROVED]` statement of the ten cards in
  `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/mobius/`, then promote each
  card to `3-formalized`.  RH-bearing open gates stay open; only proved content is formalized.

## Cards and their proved payload

| # | Card | Proved payload needing Lean | State |
|---|---|---|---|
| 1 | `mobius-squarefree-reciprocal-projective-transfer` | (1)-(6), (7a)-(7b) | **DONE** |
| 2 | `mobius-critical-exponential-boundary-layer-law` | (1)-(3), (5)-(8), (12)-(15) | **DONE** |
| 3 | `mobius-half-unit-exponential-moment-rh-law` | S2 (5)-(7), S3 (8)-(12), S5 (16)-(21) | **DONE** |
| 4 | `mobius-channel-critical-mass-escape-law` | (4)-(12), S5 (14)-(15) | **DONE** |
| 5 | `mobius-schur-centered-boundary-limit-law` | (3)-(5), (11)-(17) | **DONE** |
| 6 | `mobius-schur-causal-critical-graph-limit-law` | (5)-(7), (13)-(17) | **DONE** |
| 7 | `mobius-prime-aperture-differential-order-profile` | (4), (8), (16)-(18), (20)-(23) | **DONE** |
| 8 | `mobius-logarithmic-jet-ht-transfer-li-no-holonomic-route` | transfer thm; non-D-finite; Li | **DONE** |
| 9 | `mobius-signed-channel-coisometry-incidence-law` | (5)-(10), (15)-(17), (19)-(23), (25)-(27) | **DONE** |
| 10 | `mobius-signed-coisometry-schur-transfer-law` | (4)-(13), (17)-(18), (21)-(23), (23a)-(23i) | **DONE** |

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
- `RHTower/MobiusCoupledFeatureIncidence.lean` — card 9 (13)-(17),(20)-(23): the truncated
  constant boundary mode, the coupled feature and its exact norm, and the cancellation law.
- `RHTower/MobiusSignedChannelIncidencePaperCertificate.lean` — card 9 complete.
- `RHTower/ExponentialIntegralE1.lean` — the exponential integral `E_1` and its logarithmic
  representation (needed by card 7).
- `RHTower/MobiusCenteredSchurBoundary.lean` — cards 5 and 6: the centered Schur quotient, its
  uniform boundary majorant, and the strong Hardy limits of both Hardy components.
- `RHTower/MobiusPrimeApertureRetainedMass.lean` — card 7 (4),(5): the smooth-number Euler product
  for the squarefree channel mass and the cofinal logarithmic Euler sum.
- `RHTower/CausalLaplacePlancherel.lean` — Plancherel for the boundary Laplace transform,
  obtained from the corpus Mellin--Plancherel line law in logarithmic coordinates.
- `RHTower/MobiusWeightedMertensVector.lean` — card 5 (13),(16): the weighted-Mertens vectors, the
  exact centering identity, exponential decay, `L^1 cap L^2` membership, and the exact transfer
  identity `L m_omega = G_omega` on the imaginary axis.
- `RHTower/MobiusCenteredMertensLimit.lean` — card 5 (14),(15),(17): `m_0 in L^2` (unconditional),
  the critical energy identity, and `m_omega -> m_0` in `L^2`, all via Fatou + Plancherel.
- `RHTower/MobiusCausalSourceLimit.lean` — card 5 (11) and card 6 (16).
- `RHTower/MobiusSchurBoundaryPaperCertificate.lean` — cards 5 and 6 complete.
- `RHTower/MobiusSignedSchurTransferPaper.lean` — card 10 complete: (18),(21),(23a),(23b),(23d)-(23g),
  plus the reusable causal shift law in `MobiusPowerSumBoundaryLaplace`.
- `RHTower/MobiusLogarithmicJetLiGenerator.lean` — card 8: the Möbius chart, the jet identity
  `J_r(F) = logDeriv (F o r)`, and the **unconditional** non-holonomicity of the Keiper--Li
  generating function (hence the Li sequence is not P-recursive).

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
- 2026-08-19 — cards 5, 6, 9, 10 fully certified.  18 new Lean modules, zero proof debt, all wired
  into `GaloisForLFunctions.RHTower`.  Remaining: card 3 (half-unit tower), card 7 (critical
  prime-aperture profile `(8)`), card 8 (Möbius logarithmic jet / Li non-holonomicity).


## Card 8 closed

`HTGeometry/MobiusJetTransfer.lean` proves, over an arbitrary characteristic-zero differential
field extension `F` inside `E`:

* `differentialAlgebraicOver_iff_exists_finPoly` — DA over `F` is a nonzero polynomial relation
  among finitely many consecutive jets.
* `DifferentialRescaledEquiv F E` — a field automorphism carrying `F` onto itself and intertwining
  the derivation up to a nonzero factor of `F` (the algebraic form of `(f o r)' = r' * (f' o r)`),
  with `symm` and the conjugated derivation `conjDeriv`.
* `exists_triangular_expansion` — the triangular jet expansion with diagonal the factor powers.
* `differentialAlgebraicOver_map_iff`, `hypertranscendentalOver_map_iff` — exact invariance.
* `mobiusJet`, `mobiusJet_eq_logDeriv`, `hypertranscendentalOver_mobiusJet_iff`,
  `differentialAlgebraicOver_mobiusJet_iff` — the card's general transfer theorem.

`HTGeometry/AnharmonicRatFunc.lean` builds the order-three substitution `X -> 1/(1-X)` as a
`C`-algebra automorphism of `C(z)` and the ring-hom extensionality of `C(z)`.

`HTGeometry/AnharmonicMeromorphicSubstitution.lean` realizes it analytically on the twice-punctured
plane `C \ {0,1}` (stable under `r` and `r^2`), builds the field automorphism of `meroField`,
proves the chain rule on germs and on the fraction field, identifies the factor with `(1-z)^(-2)`,
supplies `C(z)` as a differential base field there, and assembles
`anharmonicRescaledEquiv : DifferentialRescaledEquiv (RatFunc C) (meroField anharmonicDomain)`.

`RHTower/MobiusLiGeneratorHypertranscendence.lean` gives the Li specialization:
`hypertranscendentalOver_liGeneratorMero` — the Keiper--Li generator satisfies no algebraic
differential equation over `C(z)`, unconditionally — together with the identification of the field
element as the quotient of the germs of `(xi o r)'` and `xi o r`, whose pointwise quotient is the
analytic `liGenerator`.

`RHTower/MobiusLogarithmicJetLiGenerator.lean` gives the jet identity and
`liGenerator_not_holonomic_unconditional`.


## Card 3 closed

* `RHTower/CausalL2LaplaceHolomorphy.lean` — the causal Laplace transform of an `L²` boundary
  function is absolutely convergent and holomorphic on the open right half plane.
* `RHTower/MobiusCriticalLaplaceIdentity.lean` — equation `(3)`.
* `RHTower/MobiusWeightedMomentZeroFree.lean` — `M(alpha)` and Section 2.
* `RHTower/MobiusHalfUnitMomentTower.lean` — Section 3, `(ii) -> (i)`.
* `RHTower/MobiusRHDecayMoment.lean` — Section 3, `(i) -> (ii)`, and the capstone
  `riemannHypothesis_iff_forall_weightedMertensMoment`.
* `RHTower/MobiusPrelimitSafeWidth.lean` — equations `(18)` and `(21)`.
* `RHTower/MobiusPrelimitLaplaceIdentity.lean` — equations `(16)` and `(19)`.
