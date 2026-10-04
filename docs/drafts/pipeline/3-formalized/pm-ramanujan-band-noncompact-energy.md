# Route PM: cofinal escape from every totally bounded profile family

- **ID:** pm-ramanujan-band-noncompact-energy
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Source:** actual complete-band cleared identity, positive residue test, Riemann-Lebesgue and finite-cover characterization of total boundedness.
- **Lean:** `GaloisForLFunctions/RHTower/PMRamanujanBandNoncompactEnergy.lean`.

## Exact statement

For every epsilon>0, there is c>0 such that for every totally bounded set K of actual L2 profiles and every real B, there is X>=max(1,B) whose normalized complete-band vector has norm-distance at least c from every member of K. The same statement holds for the literal original logarithmic source, through the exact fixed Mellin unitary. In particular, every finite family and every compact family misses a cofinal actual vector by this common radius.

The full image is not totally bounded; every bounded cutoff head is totally bounded. The conclusion does not assert unbounded norm. Bounded noncompact motion remains possible, and the small-damping signed-energy upper ceiling remains open.

## Paper proof

Assume the full normalized critical-frequency image for X>=1 is totally bounded. It is bounded, so phase isometry supplies a global bound on the complete moving source. For each fixed h and F, Riemann-Lebesgue applied to conj(h)*F gives <h,U_a F> tending to0. Cover the proposed totally bounded image by finitely many balls of radius eta/[2*(||h||+1)]. Each center pairing is eventually smaller than eta/2; the unitary norm and Cauchy-Schwarz bound the difference by eta/2. This proves uniform decay on that image, hence the literal tested source q_h(exp u) tends to0.

Multiply by the modulus-one factor exp(-i*Im(rho)*u). The result remains measurable, globally bounded and tends to0. The audited bounded-null Abel theorem and exact X=exp(u) substitution give delta*Q(rho+delta)->0 for the actual tested scale transform. Choose the unconditional positive Hardy critical zero rho and its actual positive compact residue test. The bounded-source continuation identifies zeta(rho+delta)*Q(rho+delta) with the continuous tested complete kernel. The zeta slope zeta(rho+delta)/delta has a finite limit (simplicity is not required), so the left side tends to0. The right side tends to the strictly positive residue pairing. Contradiction. Thus the full normalized image is not totally bounded.

For each finite B, the normalized image of [1,B] lies in a finite union of compact scalar segments: the floor pair is in Iic(floor B) times Iic(floor(2B)), and 0<=X^epsilon<=(max B 1)^epsilon. Hence each such head is totally bounded. Negating the metric finite-cover characterization of the full image gives eta>0 such that no finite union of eta-balls covers it. Given any totally bounded K and B, cover K together with the image of [1,B] by finitely many eta/2-balls. An actual vector outside all corresponding eta-balls must have cutoff at least B and have distance at least eta/2 from every F in K. The same eta/2 works for all K and all B. This proves the desired cofinal compact-profile escape, in fact for every totally bounded K.

Finally map a physical profile G to sqrt(2*pi)*V(G), using the audited exact Mellin unitary V. This map preserves total boundedness, and its distance multiplier is sqrt(2*pi). Dividing the separation radius by that constant proves the identical statement for the original normalized complete logarithmic source. No norm upper estimate, source integrability at small damping, or RH conclusion is inferred.

## Corpus grounding

Search158 was partial with inventory65010 complete; search159 completed with inventory65015 complete. Compiler freshness was mixed. All candidate/source statements and ingredient steps were inspected. The exact source proofs use current Mathlib Riemann-Lebesgue, metric finite covers and finite unions, plus the actual PM bounded-source continuation and positive residue test. Compact-operator hypotheses returned by other hits were not assumed.

## Verification — 2026-10-03

All nine public declarations in `PMRamanujanBandNoncompactEnergy.lean` are fully audited. Targeted `lake --old build GaloisForLFunctions.RHTower.PMRamanujanBandNoncompactEnergy` passed (new leaf129s). Mandatory `lake env lean GaloisForLFunctions/RHTower/PMRamanujanBandNoncompactEnergy.lean` passed with exit0 and no diagnostics. All nine public exports passed separate /tmp axiom queries with only propext, Classical.choice and Quot.sound. Umbrella import appears exactly once; whitespace checks passed. No full or umbrella build, heartbeat increase, numerical experiment, added axiom or RH assumption.

Global lint exits1 on thirteen unrelated unreachable modules: CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MertensProductDiamondPintz, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, ThetaCuspC5ClockSourceOrientation, ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving, and HTGeometry.CompactMonoidMeasureAlgebra. None is this leaf or either bounded-source extension.

The unconditional positive survivor is one radius working against every totally bounded profile collection on every real tail, in both exact carriers. Compact normalized-profile closure is falsified. Bounded noncompact motion, the weaker damping-margin moment conjecture, and the actual natural-denominator signed-energy ceiling remain open. This is not an RH proof or falsification.
