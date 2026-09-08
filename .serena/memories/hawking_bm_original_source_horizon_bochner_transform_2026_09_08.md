# HB actual native source: horizon decay and joint Bochner identity

Goal remains unconditional formal RH proof/falsification, UNPROVED. Frontier map is READ ONLY; do not edit or revert concurrent changes. User requires foreground one owned Lean/Lake process at a time, no umbrella/full builds, new-only axiom checks, cleanup. No numerical experiment was used or indicated.

## Exact result
Proof card: docs/drafts/pipeline/3-formalized/hb-original-source-horizon-bochner-transform.md. Current work card: docs/drafts/pipeline/1-in-progress/hb-joint-causal-laplace-identification.md, updated to current remaining obligations. Universal STATUS unchanged: no new route-independent RH constraint was exposed.

With s=physicalRate q branch, t<0, u=-tanh(t), H(v)=smoothTransition(v)*exp(2s*v), the actual reduced time source is R(tau,t)=C0(t)*H(tau+t)+C1(t)*H'(tau+t), C1=2*radialLiftFirst. Both C0,C1 equal exp(2t)*P_i(u(t)), with actual continuous profiles P_i on [0,1]. Exact identity 1-u(t)=exp(2t)*(1+u(t)). currentRate_re_lt proves Re(2s)<-2 unconditionally.

For EVERY real c<2, proved |R(tau,t)|<=C*exp(-c*tau)*exp((2-c)*t). The radial envelope is L2(radialMeasure). Actual radial and full spatial source vectors satisfy norm<=B*exp(-c*tau), are strongly continuous in their original Hilbert spaces, and retain old causal support tau<=0 -> 0. c=0 gives a fixed L2 majorant for dominated continuity.

Exact frequency factor: reducedCoefficient(s,w,a,T,t)=exp((w+2)*t)*T*(P0(u(t))+w*P1(u(t))). This gives actual frequency-source L2 admission for Re(w)>-2. No maximality claim.

For Re(w)>-2 choose c=1-Re(w)/2: c<2 and Re(w)+c>0. Proved Bochner Laplace integrability of actual radial and spatial source. For every radial L2 test, Holder gives integrability of test*radialEnvelope; product time/radial majorant gives absolute Fubini. All-test identification proves the actual radial Bochner integral equals radialSourceLaplaceVector, retaining onsetTransform(2s,w). The fixed angular tensor CLM commutes with the integral, yielding timeCuspMainVector_laplace: integral_(tau>0) exp(-w*tau) • timeCuspMainVector = cuspMainLaplaceVector. The latter equals the literal reducedCoefficient*actual native squareResidual a.e.

## New audited surface — DO NOT REAUDIT
Seven leaves, 30 public theorems, 567 source lines. Route namespace RHTower.D4BMJointSource, prefix GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSource:
- HorizonFactor (6): exact polynomial/slope horizon factors; sourceHorizonProfile; radial identities.
- TimeDecay (3): timeOnset_pair_bound, timeReducedCoefficient_bound, timeReducedCoefficient_physical_bound.
- VectorDecay (9): horizonEnvelope_memLp; timeRadialSourceVector; its ae, bound, continuity; joint/time coefficient continuity; timeCuspMainVector_separated, continuous, bound.
- TransformChamber (5): reducedCoefficient_frequency_horizon, reducedCoefficient_memLp_horizon; exponent choice; radial/joint Bochner integrability.
- TransformPairing (2): actual radial all-test joint integrability and Laplace pairing.
- VectorLaplace (4): radialSourceLaplaceVector_ae, timeRadialSourceVector_laplace, cuspMainLaplaceVector_ae, timeCuspMainVector_laplace.
Generic GaloisForLFunctions.HTGeometry.L2DominatedContinuity (1), same namespace: continuous_toLp_two_of_dominated for a first-countable parameter space, arbitrary measure and normed target, fixed L2 majorant.

All seven individual canonical leaf lake-build audits passed without warnings. Only requested new module compiled each time; other listed Lake jobs were cached dependencies/targets. Source/artifact byte matches and exact-once umbrella imports passed. New-only scratch #print axioms checked all30: exactly propext, Classical.choice, Quot.sound. No old axioms repeated. No umbrella/full/dependency build. Source index refreshed. Global lint --check-generated failed ONLY on 13 concurrent unwired unrelated modules: CoppoFockRotation, CoppoJosephsonPotential, CoppoKerrPhaseGeometry, CoppoNonlocalNoise, CoppoPartnerEigenspaces, CoppoSSH, QNMAnchorNormalization, QNMHyperboloidalPolynomial, QNMLorentzAuxiliary, QNMQuadraticPencil, QNMBackwardError, QNMMatrixBackwardError, QNMModalResidue. 141 large-file warnings. New HB scoped checks passed. Preserve concurrent work, don't chase its wiring.

## Remaining hard target
Native square-remainder channel now has genuine full vector transform. Three cutoff-principal Green-response channels still need one actual causal time family with every cutoff commutator retained. Then full-source vector transform and convolution with original causal response. Wider SOURCE transform chamber does NOT continue original response inverse. Original time PDE/propagation, endpoint traces, constrained Einstein sectors, left-QNM continuation and multiplicity-matched spin-two/AIME pairing remain. Independent Hawking-clock extinction/RH remain unproved. No Xi-zero restriction follows just from this source identity.

## Efficient Lean details
For pointwise products/smuls inferred by AEStronglyMeasurable APIs, use explicit change to lambda value before rw; Pi applications may hide factors. AEStronglyMeasurable.star exists; AEMeasurable.star does not in this toolchain. FirstCountableTopology needed for continuous_of_dominated. For the physical coefficient's time continuity, applying joint-continuous.comp at an inferred physical rate timed out; use the generic timeReducedCoefficient_time_continuous s a t first and apply it directly. Complex.ofReal_exp is the verified cast lemma. Explicit type for let L : Lp ℂ 2 radialMeasure →L[ℂ] SpatialSpace avoids stuck domain inference.

Canonical audit pattern: isolated package backed by stub packages whose buildDir points to existing cache/lib/lean, leanLibDir="."; exact new leaf lean_lib roots. OMIT globs to default to roots.map Glob.one, or specify exact globs; globs=[] creates an empty library and does NOT check its root. Require a fresh 'Built <requestedmodule>' log and reject other fresh modules/warnings before installing new .olean/.ilean. Use exact leaf builds sequentially, never umbrella.

Temporary scratch /tmp/hb-source-bochner.f480EO and audit /var/folders/h4/zrd73pg91clb__kg1kzrlcph0000gn/T/hb-source-bochner-audit.0gm8fq3z are being removed at turn end. Do not rely on them; all canonical sources, artifacts and proof card are installed.