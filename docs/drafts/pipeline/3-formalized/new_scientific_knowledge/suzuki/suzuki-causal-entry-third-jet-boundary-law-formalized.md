# Suzuki causal-entry third-jet boundary law — formalization certificate

- **Stage:** 3-formalized
- **Paper proof:**
  `./suzuki-causal-entry-third-jet-boundary-law.md`
- **Lean modules:**
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCausalEntryThirdJetBoundaryLaw.lean`,
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCausalEntryMovingCutRealization.lean`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Formalized result

Lean encodes denominator-matched near and far delayed-hinge channels and proves moving-boundary
transport from exact derivative hypotheses

```text
A'=-B,  B'=-tau,  H'=exp(I*z*(a-ell))*tau.
```

Near channel differentiates through jets one, two, and three.  At `ell=2a`, near and far jets
agree through order two, while their third-jet difference is exactly

```text
z^2 * exp(I*a*z) * endpointTrace.
```

Affine sewing preserves this law and produces forced marked bracket

```text
z^2*exp(I*a*z)
  *((beta-gamma)*W_beta*tau_alpha-(alpha-gamma)*W_alpha*tau_beta).
```

A common normalized trace factors through complete sewn characteristic rather than cancelling.

Key declarations:

```text
hasDerivAt_suzukiDelayedHingeNearCompletedJet0
hasDerivAt_suzukiDelayedHingeEntryCurrent
hasDerivAt_suzukiDelayedHingeNearCompletedJet1
hasDerivAt_suzukiDelayedHingeNearCompletedJet2
suzukiDelayedHingeCompletedJet3_entryWall_sub
suzukiAffineSewnIntervalPart_entryThirdJet_sub
suzukiAffineSewnEntryThirdJet_commonNormalizedTrace
```

## Moving-cut realization: the derivative hypotheses are theorems

`SuzukiCausalEntryMovingCutRealization` defines the actual moving-cut integrals

```text
suzukiMovingCutMass v a ell        = ∫_{-a}^{a-ell} v,
suzukiMovingCutFirstMoment v a ell = ∫_{-a}^{a-ell} (a-ell-y) v(y) dy,
suzukiMovingCutHighMoment v z a ell = ∫_{a-ell}^{a} v(y) exp(I z y) dy,
suzukiApertureCharacteristic v z a  = ∫_{-a}^{a} v(y) exp(I z y) dy,
```

and proves the three transport laws `(4)` for every continuous source `v`:

```text
hasDerivAt_suzukiMovingCutMass          B' = -v(a-ell)
hasDerivAt_suzukiMovingCutFirstMoment   A' = -B
hasDerivAt_suzukiMovingCutHighMoment    H' = exp(I z (a-ell)) v(a-ell)
```

The first moment is differentiated without differentiating under the integral sign: the identity
`suzukiMovingCutFirstMoment_eq` rewrites it as `(a-ell)·B(ell) − ∫_{-a}^{a-ell} y v(y) dy`, whose
two moving-endpoint contributions cancel.  Instantiating the abstract chain then gives the
hypothesis-free transport theorems

```text
hasDerivAt_suzukiDelayedHingeNearCompletedJet0_movingCut
hasDerivAt_suzukiDelayedHingeEntryCurrent_movingCut
hasDerivAt_suzukiDelayedHingeNearCompletedJet1_movingCut
hasDerivAt_suzukiDelayedHingeNearCompletedJet2_movingCut
```

and the entry-wall classification for the realized channels

```text
suzukiMovingCutMass_entryWall,  suzukiMovingCutFirstMoment_entryWall,
suzukiMovingCutHighMoment_entryWall
suzukiDelayedHingeNearCompletedJet0_movingCut_entryWall
suzukiDelayedHingeNearCompletedJet1_movingCut_entryWall
suzukiDelayedHingeNearCompletedJet2_movingCut_entryWall
suzukiDelayedHingeNearCompletedJet3_movingCut_entryWall_sub
suzukiDelayedHingeNearCompletedJet3_movingCut_entryWall_eq_of_dirichlet
```

The last two are `(12)` and its Dirichlet corollary literally: the wall defect of the realized
channel is exactly `z^2 exp(I a z) v(-a)`, and it vanishes when the source obeys the Dirichlet
boundary condition at `-a`.

## Scope and frontier

This falsifies instantaneous value-, slope-, or curvature-jump Cholesky updates at prime entry.
It identifies discrete endpoint reporter required by
`SUZUKI-RECTANGULAR-WARD-DEFECT-SEMIBOUNDED`; it does not prove remaining lower bound or RH.

## Verification

- direct source check:
  `lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiCausalEntryThirdJetBoundaryLaw.lean`;
- targeted SOTA build: `9452/9452` jobs;
- axiom audit: `propext`, `Classical.choice`, `Quot.sound` only;
- repository formal lint reaches this module but remains red on unrelated concurrent unreachable
  module `GaloisForLFunctions.HTGeometry.CrossingConeSharpCommutativityPhaseLaw`;
- no `sorry`, `admit`, new axiom, `opaque`, `unsafe`, numerical computation, or RH premise.
