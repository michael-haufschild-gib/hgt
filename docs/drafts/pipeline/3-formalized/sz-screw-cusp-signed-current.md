# SZ: logarithmic cusp forces both signed source-current excursions

- **ID:** sz-screw-cusp-signed-current
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** SZ, actual canonical-head source sign
- **Statement:** The completed critical Mellin error exceeds every positive and negative constant on every sufficiently late ray. Consequently the complete corrected finite-aperture Fourier symbol has no eventual pointwise lower bound, even at frequency zero.

## Mathematical purpose

Test the proposed producer that proves canonical-head positivity by pointwise nonnegativity of the complete Gamma–polar–prime Fourier symbol. This is a qualitative source obstruction, not a numerical bound improvement. A negative symbol value alone does not give a negative aperture-supported quadratic form. The unresolved hard problem is the correlation between physical support, phase credit and Gamma energy.

## Corpus and novelty audit

The completed error is exactly the Suzuki right slope minus an explicit archimedean correction tending to a constant (`CCMGuinandWeilXiScrewGreenConnection`). Existing `RoutePActivePairedDisplacementEscape` gives absolute unboundedness only. `RoutePCompletedErrorOneSidedLandau` turns either one-sided linear bound into RH. `SuzukiOriginRemainderRegularity` gives an o(t) remainder after the exact t log t cusp. `SuzukiScrewFunctionCriterion` identifies the actual source with its summable critical screw series under RH; `SummableSpectrumScrewAlmostPeriodic` supplies uniform recurrence without independent ordinates. Deep search generation 1223557 had complete source inventory but largely pending/stale compiler coverage; proposed recurrence ingredients were not applicable proof certificates.

## Paper proof

1. Psi(t)/t is unbounded above as t decreases to zero: the prime sum vanishes before log 2, and Psi(t) = -t log(t)/2 - A*t - o(t).
2. Prove the literal right derivative Psi'_+(t) at every t>0, including prime seams. Freeze floor(exp t) in a right neighborhood; differentiate the resulting finite affine hinge sum. Its value is completedError(t) plus the known archimedean correction.
3. Assume one sign of completedError is bounded above on a late ray. Patch the finite head by the existing exponential absolute bound; the signed Landau theorem implies RH.
4. Under RH uniform Bohr recurrence transports any fixed two-point increment arbitrarily far right. An eventual signed derivative upper bound fences every late secant. Transporting either the increment (0,h) or its even reflection (-h,0) back to the cusp contradicts step 1. Thus both signed currents escape every constant.
5. Retain source-local structure: right continuity turns each strict excursion into an interval of the same sign. The resulting late positive-length windows, together with the exact zero-frequency symbol identity, are the positive survivor. No assumption of rational independence or RH remains in the public escape/window conclusion.

## No-go closure

- **Candidate:** eventual pointwise lower bound for the full corrected symbol.
- **Killing mechanism:** both signed completed-error window theorems, verified by final leaf60657 and axiom audit53591.
- **Positive survivor:** cofinal positive-length windows for both signed actual currents, with exact conversion to full Gamma–polar–prime symbol windows. This records arithmetic cancellation geometry rather than merely negating positivity.
- **Status:** dependency-closed paper proof and Lean theorem audited; all three public declarations use only propext, Classical.choice and Quot.sound. RH remains unresolved.

## Audit discipline

One foreground Lean process; scratch name checks and all public axiom checks in /tmp; final leaf via lake --old env lean; no umbrella build, numerical experiment, new axiom, or heartbeat change.

### Dependency-closed paper proof

The sign conventions have been checked against the actual source: Psi is the negative of `suzukiSourceScrew`, so Psi(h)/h tends to positive infinity at the right origin. Its right slope is E(h)+screwLinearCoeff/2-screwLerchTail₁(h). For sign epsilon in {1,-1}, an eventual upper bound on epsilon*E patches to C*(1+t); applying Landau with sign -epsilon gives RH internally. If epsilon=1 use the cusp increment (0,h); if epsilon=-1 use (-h,0). Choose a uniform almost-period with error h/4 at both endpoints and transport beyond the current bound. A cusp secant greater than (C+1)*h contradicts the transported upper bound C*h. The strict current escape extends rightward across a nonzero closed interval because floor(exp t) is locally constant to the right, including at prime seams. This completes the paper argument without RH or an ordinate-independence premise; Lean verification is complete (leaf60657; axioms53591).

### Scratch audit

Scratch2938 passed with no diagnostics. Three public declarations are implemented in `SuzukiCompletedCurrentSignedWindows.lean`: the actual right derivative through prime seams, both signed completed-current windows, and both signed complete-symbol windows at zero frequency. The production leaf is wired once; final direct audit60657 and all public axiom queries53591 passed. Scratch32880 exposed two elaboration issues (pointwise finite sum and an untyped right-neighborhood predicate), both repaired without changing the mathematical argument. No computation or extra axiom was used.

### Consequence for the next sign conjecture

Unbounded slopes and symbol values do not control their integrated signed work or the energy of a supported physical vector. A proposed canonical-head producer must constrain amplitude, phase and duration together. The complete signed Gamma–prime–polar pairing remains the target; replacing it by an eventual pointwise symbol floor is now contradicted by the checked window theorem.

### Production audit

Final direct leaf60657 passed with no diagnostics:

```text
lake --old env lean GaloisForLFunctions/RHTower/SuzukiCompletedCurrentSignedWindows.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/SuzukiCompletedCurrentSignedWindows.olean
```

Public declarations: `RHTower.hasDerivWithinAt_suzukiPsi_right` (line42), `RHTower.criticalMellinCompletedError_two_signed_windows` (line215), `RHTower.correctedCCMSymbol_zero_two_signed_windows` (line228). Umbrella import appears once; no umbrella build was run. All three public axiom queries53591 passed in /tmp, each reporting only propext, Classical.choice and Quot.sound. The printed capstone types quantify only over B and L; neither has an RH premise. Global lint49877 reported only the following unrelated unreachable-module errors; the new leaf had no lint error:

```text
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMApertureChainProfile
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMApertureTranslationChains
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMExponentialRampPrimeMoment
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMExponentialRampSourceDissipation
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMExponentialRampTerminalEntropy
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMRetainedChainKernelLower
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.MertensProductDiamondPintz
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.MoebiusMollifiedCriticalMoment
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.MoebiusMollifiedErrorThreeLines
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PMPowerDampedMobiusBoundaryMoments
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.RoutePNativeMixedLaplaceTransform
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.RoutePNativeMixedWeightedFTC
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ThetaCuspRatioSquareFlow
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ThetaCuspRatioSquareMoments
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ThetaCuspRatioSquareSlope
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ThetaGaussianAmplitudeQuadratic
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ThetaGaussianCovarianceLimit
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ThetaGaussianCovarianceMeasure
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ThetaMovingShellFirstOrderPhase
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ZetaZeroDensityPowerSaving
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.CompactMonoidMeasureAlgebra
```

Final closure: both source and complete-symbol signed-window conclusions are unconditional. Targeted whitespace check passed; all owned build/search/lint processes exited. All eight exact temporary search/proof/axiom/lint files have been removed; audited production olean retained. No full or umbrella build, subagent, numerical experiment, heartbeat change, commit or push was used. RH goal remains active.
