# HB original causal cusp-source transform — complete batch

RH goal remains ACTIVE and UNPROVED. Do not mark complete/blocked. User frontier map `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` is READ ONLY. No frontier edit by this task. No numerical experiments indicated or run. User requires broad corpus discovery using `scripts/formal_tools.py research 'synonyms ...' --any`; multi-term default is AND. Use OR for discovery, then AND for focused intersections. Preserve that preference.

## Closed result

For each actual XiZeroCopy, physical branch, amplitude and principal i: `RHTower.D4BMJointSource.principalLaplaceProfile_eq_principalDifference` proves actual continuous causal Laplace profile equals original endpoint Green difference on x<0, with T=onsetTransform(2*physicalRate,w) unchanged. Conditions are original strict growth half-plane and PrincipalChamber; no supplied horizon phase, derivative bound or regularity. `principalTimeLaplace_ae_principalDifference` transfers to actual negative-ray L² class.

`causalGreenThreshold q := max (causalPrincipalThreshold q) (principalThreshold q)`.
`causalCuspSourceVector_original_transform` proves, for Re(w)>causalGreenThreshold q, BOTH absolute positive-time Bochner integrability and
 integral exp(-w*tau) • causalCuspSourceVector(q,branch,a,tau)
 = cuspResidualVector(q,branch,w,a,onsetTransform(2*physicalRate,w),hc).
All native square and three cutoff channels retained in actual original SpatialSpace. This is a nonempty full right half-plane, not just real frequencies or a sector. RH, physical left-QNM continuation and independent Hawking-clock extinction remain open.

## Proof mechanism

Compact Schwartz IBP without auxiliary growth assumptions; subtract double primitive of continuous weak second density; use ExponentialTwist local du Bois–Reymond linearOn theorem twice to classify continuous zero-weak-second remainder as affine; derive actual classical spatial jets. Original transformed weak equation supplies literal classical radial equation.
Actual H² Sobolev profile has L¹ Fourier representative, hence bounded continuous profile. Original Green endpoint limits give compact-radius bounded extension, exact lift has exponential compact-radius bound. Difference F solves literal homogeneous ODE, is bounded, and has zero endpoint trace. Complex componentwise Landau from existing BoundedSolutionDerivative yields first-jet bound on x<-1 (4*C+M from value/second bounds).
Both original homogeneous modes transported to tortoise coordinate. Exact W(H,N)=-connection !=0. Horizon coordinate tends zero, actual H and H' decay at negative infinity via original power/Gauss limits. Constant W(F,H) vanishes from bounded actual F,F' and decaying H,H'. A=W(F,N) is constant; Cramer identity F*(-connection)=H*A; endpoint F→0,H→connection!=0 forces A=0, hence F=0. All comparison premises discharged from actual original objects.
Then original negative restriction/horizon multiplier and product-measure AE laws identify all three angular cutoff channels; finite sum plus native transform gives full source identity.

## Finished files and validation — DO NOT RE-AUDIT

14 new canonical leaves, 45 public theorems, 1014 source lines; every new source has autoImplicit false. Individually audited using `lake build <canonical module>` in isolated cache-only package; all pass with NO warnings. All 45 new theorem #print axioms checked in scratch, exactly standard foundations only (propext, Classical.choice, Quot.sound). No sorry/admit/axiom/opaque/unsafe/native_decide/ofReduceBool in new proof code. Installed all 28 olean/ilean artifacts byte-identical to individual canonical audits; every new leaf directly wired once into area umbrella. No umbrella/full build by this task. Global `formal_tools.py lint --check-generated` PASSED, no errors, 141 existing large-file warnings elsewhere. Generated indexes refreshed. Preserve unrelated concurrent modifications.

General HTGeometry leaves:
- LocalSchwartzPairing (6 public)
- ContinuousWeakSecondAffine (1)
- ContinuousWeakSecondRegularity (1)
- RealSobolevBoundedProfile (1)
- BoundedComplexDerivative (1)
- NegativeWronskianUniqueness (3)

RHTower leaves, prefix ThetaCuspHawkingBMJointSource:
- PrincipalLaplaceClassical (4)
- GreenEndpointTrace (5)
- GreenProfileBounds (5)
- PrincipalGreenDefect (6)
- HorizonModeJets (3)
- HorizonModeLimits (4)
- PrincipalGreenIdentification (2)
- CausalCuspSourceIdentification (3)

Proof card: docs/drafts/pipeline/3-formalized/hb-original-causal-cusp-source-transform.md.
Active card updated: docs/drafts/pipeline/1-in-progress/hb-joint-causal-laplace-identification.md.
No new route-independent STATUS entry was justified. Frontier map untouched by this task.
Owned scratch `/tmp/hb-green-identification.hEYpDK` (including isolated package and stable hardlinked dependency snapshot) scheduled for removal immediately after this memory; no owned Lean/Lake process remains. A concurrent task rebuilt shared old dependencies during development, temporarily removing .oleans. Stable hardlinked dependency snapshot + cache-only local package avoided any large rebuild by this task. Never kill another task's process.

## Next direct obstacle and broad-search results

Full chain to state at new turn: literal theta cusp → Xi occurrence → retained spin-two source → original causal response and physical left-QNM pairing → independent Hawking-clock extinction → RH. Source's complete original causal transform is now identified; next build original joint response to that time-dependent source, then physical continuation/pairing. Do not repeat source-identification scaffolding.

Broad OR searches `causal retarded Duhamel convolution --any` and `Hawking extinction QNM propagation --any` searched corpus, then AND `convolution Laplace`, focused AND `causal kernel --module BMJoint`, and broad non-HB OR `Duhamel retarded semigroup --any --exclude-module ThetaCuspHawking` with exploration. Checked source bodies:
1. ThetaCuspHawkingBMJointCausalRightHalfPlane: jointCausalKernel_originalResponse_rightHalfPlane(F,w,Rew>0) identifies fixed-F original joint causal kernel transform; positive damping in vector L² and absolute Laplace integrability for every positive Rew. General waveCausalKernel_* version parameterized by contraction J:V→H.
2. BMJointCausalKernel: kernel is undamped actual vector inverse Fourier class, support/probes proved, but dependence on F and resulting time-dependent source Bochner interchange still need actual proof.
3. HTGeometry.LaplaceTransformConvolution is ENNReal measure-valued Laplace-Stieltjes, NOT directly the needed spatial vector operator convolution.
4. RHTower.XiThetaSquareRateLaplace: causalLaplaceWeighted_convolution is exact exponential factorization for scalar complex function convolution; causalLaplaceIntegral_convolution requires scalar L¹ and pointwise causality. Reuse algebra/Bochner convolution method but cannot assume it supplies original spatial operator identity.
5. HTGeometry.CausalFourierBridge provides scalar causal support/convolution/Young estimates.

Possible construction to assess (not proved): establish weighted-time L² kernel-map linearity/bounds for F↦K_F and source integration, OR apply the vector Hardy inverse construction directly to original resolvent(w) applied to now-identified source transform, then prove physical time equation. Do not treat the chosen per-F L² representative as an already pointwise bounded operator K(t). Need original metric/domain/Einstein-sector identifications before left-QNM source pairing. Current source half-plane identity does not continue the response inverse across physical poles.
