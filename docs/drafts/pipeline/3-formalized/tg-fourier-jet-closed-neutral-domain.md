# TG-C9.6: exact closed neutral domain of the physical Fourier jet

- **ID:** TG-C9.6-20261002-01a0-positive
- **Stage:** 3-formalized
- **Parent:** `../5-failed/tg-fourier-jet-neutral-graph.md`
- **Leaves:** `PrimeBurnolFourierJetPhaseObstruction`, `PrimeBurnolFourierJetNeutralGraph`

## New knowledge

For E(f,g)=(f+Fg,Mf+FMg), let G be the completed even source graph in the physical
input-and-output norm. The original neutral operation N(f,g)=(f,0) is a closed,
unbounded idempotent partial linear operator. Its exact domain is the original even
separately admitted D(M)² source graph, proper dense in G. Its range and zero fibre
are exactly the individually closed first and Fourier channel graphs. These channels
are disjoint and their algebraic sum is nonclosed.

No neutral graph estimate holds even on any single prime's literal depth core.
This answers the stronger-topology question left open by output-only recovery failure.

## Dependency-closed proof

The actual even Schwartz family is sqrt(r) exp(iπx²) exp(-πr²x²), r>0.
Temperate sine/cosine composition admits the phase multiplier; normalized physical
dilation gives constant L2 norm and position-square norm r^-2 times a fixed positive
Gaussian position-square norm. Exact differentiation gives, with a_r=π(i-r²),
Wφ_r=4a_r φ_r+(8π²+8a_r²)x²φ_r.

Multiply any proposed position graph estimate by r². Its left side is fixed positive;
its right side is continuous at zero and vanishes there. This excludes every such
estimate without choosing optimized constants. The exact admitted source (Fφ,-φ)
then converts any neutral graph estimate into the forbidden position estimate.
Closure in both separate multiplication graphs transfers the obstruction to each
literal prime core, retaining the actual Euler amplitudes.

The two source channels are closed by maximal multiplication closedness, even-subspace
closedness and Fourier continuity. Their intersection is zero. The relation
`N z=w iff w belongs to channel A and z-w belongs to channel B` is therefore the graph
of a closed partial linear map, with domain A+B, range A and zero fibre B. The closed
graph theorem and the established unboundedness force A+B to be nonclosed and proper
in its closure. These are properties of the actual source, with no analytic premise.

## Verification

- Foreground `lake --old env lean <leaf> -o <matching olean>` passes for the two new
  leaves and the amended `PrimeBurnolFourierJetClosure`; no warnings or errors.
- Separate /tmp `#print axioms` audit passes all 21 new public theorems: only
  propext, Classical.choice, Quot.sound.
- RHTower umbrella imports both leaves; no umbrella or full build.
- `scripts/formal_tools.py index` exits zero. Scoped whitespace checks clean.
- `scripts/formal_tools.py lint` exits one on unrelated unwired RHTower leaves:
  CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment,
  CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy,
  CCMRetainedChainKernelLower, MobiusDivisorCriticalCompensatedCauchy,
  MobiusDivisorCriticalLogProfileTail, MobiusDivisorCriticalMertensLogError,
  MobiusDivisorCriticalMovingHeadAsymptotic, MobiusDivisorCriticalPrimeTailError,
  MobiusDivisorCriticalPrimeTailSource, MoebiusMollifiedCriticalMoment,
  MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.
  No new TG leaf error. Existing large-file warnings remain.

## Exact limit of the result

This settles neutral boundedness and its surviving domain geometry. It does not prove
that every complete cubic expression is unbounded: cancellation must be tested on the
actual source algebra. Gamma–Xi identification, Hardy-index transfer and the arithmetic
sub-unit producer remain open; RH is neither proved nor falsified here.
