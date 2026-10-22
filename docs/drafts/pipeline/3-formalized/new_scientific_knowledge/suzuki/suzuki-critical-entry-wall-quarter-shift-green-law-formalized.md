# Suzuki critical entry-wall quarter-shift Green law — formalization certificate

- **Stage:** 3-formalized
- **Paper proof:**
  `./suzuki-critical-entry-wall-quarter-shift-green-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalEntryWallQuarterShiftGreenLaw.lean`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`

## Formalized result

Lean proves the complete delayed-hinge near/far second jet obeys exact causal transport

```text
(d/dell-I*z) gap'' = z^2*exp(I*a*z)*endpointTrace.
```

This is an all-depth Ward equation, not only an entry-wall jump identity.  For valuation depth
`e`, the prime-power wall aperture is

```text
a_(p,e)=log(p^(e+1))/2,
```

and Lean identifies its causal phase with the conjugated critical Gamma-height phase.  The actual
quarter-shift atom therefore factors uniquely as real endpoint amplitude times entry-wall phase.
After multiplying by the canonical `t^2`, it is exactly the near/far third-jet defect.  These
defects inherit the existing geometric depth recursion and sum to its contractive resolvent.
Off the spectral center, equality of forcing uniquely determines endpoint trace.

Key declarations:

```text
suzukiDelayedHingeCompletedGapJet3_sub_transport
hasDerivAt_suzukiDelayedHingeCompletedGapJet2_eq_transport_add_endpoint
suzukiPrimePowerEntryWallAperture_succ
suzukiOscillatoryKernel_primePowerEntryWall_eq_criticalPhase
suzukiCriticalApertureBoundaryAtom_eq_entryWallAmplitude_mul_kernel
suzukiDelayedHingeCompletedJet3_entryWall_eq_criticalThirdJetAtom
suzukiCriticalEntryWallThirdJetAtom_succ
tsum_suzukiCriticalEntryWallThirdJetAtom_eq_resolvent
suzukiCriticalEntryWallEndpointAmplitude_unique
```

## Scope and frontier

Formalization removes former phase-matching and triple-integration ambiguity.  It does not prove
that Suzuki's concrete restricted-Weil deficiency endpoint trace realizes calibrated amplitude.
Actual open core remains `SUZUKI-RECTANGULAR-WARD-DEFECT-SEMIBOUNDED`: prove that realization after
fixed affine normalization, or prove its residual rectangular Ward form uniformly lower bounded.
RH is not proved.

## Subsequent source correction

`SuzukiCriticalWallFieldSquareRootWeld` proves this card's calibrated amplitude contains an
independently chosen observer feature and cannot literally be an observer-independent Suzuki
deficiency endpoint trace.  Correct bare endpoint candidate is Gamma amplitude before innovation.
The later module preserves every phase/transport theorem here and factors observed forcing as
bare third jet followed by observer innovation.

## Verification

- direct source check:
  `lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalEntryWallQuarterShiftGreenLaw.lean`;
- targeted SOTA build: `9453/9453` jobs;
- axiom audit: `propext`, `Classical.choice`, `Quot.sound` only;
- repository formal lint reaches this module but remains red on eight unrelated concurrent
  unreachable modules (four `RHTower`, four `HTGeometry`);
- no `sorry`, `admit`, new axiom, `opaque`, `unsafe`, numerical computation, or RH premise.
