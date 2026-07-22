# Suzuki causal-entry third-jet boundary law — formalization certificate

- **Stage:** 3-formalized
- **Paper proof:**
  `../../2-fully-proven/new_scientific_knowledge/suzuki-causal-entry-third-jet-boundary-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SuzukiCausalEntryThirdJetBoundaryLaw.lean`
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

## Scope and frontier

This falsifies instantaneous value-, slope-, or curvature-jump Cholesky updates at prime entry.
It identifies discrete endpoint reporter required by
`SUZUKI-RECTANGULAR-WARD-DEFECT-SEMIBOUNDED`; it does not prove remaining lower bound or RH.

## Verification

- direct source check:
  `lake env lean GaloisForLFunctions/RHTower/SuzukiCausalEntryThirdJetBoundaryLaw.lean`;
- targeted SOTA build: `9452/9452` jobs;
- axiom audit: `propext`, `Classical.choice`, `Quot.sound` only;
- repository formal lint reaches this module but remains red on unrelated concurrent unreachable
  module `GaloisForLFunctions.HTGeometry.CrossingConeSharpCommutativityPhaseLaw`;
- no `sorry`, `admit`, new axiom, `opaque`, `unsafe`, numerical computation, or RH premise.
