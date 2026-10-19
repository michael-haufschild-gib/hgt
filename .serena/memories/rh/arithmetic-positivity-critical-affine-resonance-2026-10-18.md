# APT affine resonance and critical prime admission — verified 2026-10-18

Active user goal: 100 novel significant native APT contributions. Accepted count remains 0/100. Affine resonance is a structural candidate; new critical admission is useful infrastructure using existing primitives, not a counted contribution. Never mark the goal complete merely because attachment was read or these modules passed. Attachment: /Users/michael/.codex/attachments/4185f2f3-69a7-4408-a6e5-51260ec1f59e/pasted-text-1.txt.

User forbids hgtl7, numerical experiments, extra premises/axioms, heartbeat increases, full builds, README edits. One own foreground Lean/build invocation at a time. Corpus research tool required before new topics/code; not rg alone. README all 92 lines read earlier; don't reread unchanged. No subagents authorized/used. update_plan and multi_tool_use.parallel unavailable; plan in card; independent tools use Promise.allSettled. Serena symbol operations ignore Lean paths; exact rg/source fallback documented.

## Authoritative files
- formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialAffineClockResonance.lean: prior verified structural package.
- formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalPrimeAdmission.lean: NEW verified 477-line leaf, six public declarations (two definitions, four theorems).
- docs/drafts/pipeline/1-in-progress/apt-critical-collar-resonance-2026-10-18.md: full goal, paper proofs, exact reuse audit, next conjectures, validation, current plan.
- docs/drafts/pipeline/5-failed/apt-uniform-critical-cross-scale-gap-2026-10-18.md: false uniform-gap route and nontrivial positive survivor.
- Both own imports wired into formal/GaloisForLFunctions/ArithmeticPositivityTheory.lean. Preserve concurrent imports/foreign changes.

## Verified affine results
Existing λ_N=N+δ_N, 4λ_N³=N²(4N+1), δ_N∈[1/15,1/12]. New e_N=N+1/12−λ_N satisfies Ne_N=δ_N²+δ_N³/(3N), 1/(225N)≤e_N≤1/(140N).
For r≥2,M≥r,N≥1: |λ_N−rλ_M|<1/15 iff 12N+1=r(12M+1). On relation r/(400M)≤gap≤r/(140M). Family r=12q+13,N=rM+q+1 works M≥1.
For positive a≤N,b≤M: |aλ_N−bλ_M|<1/15 iff a(12N+1)=b(12M+1). Exact equality forces N=M,a=b via cubic difference factor (N−M)[144NM(N+M)+4N²+40NM+4M²+N+M].
Dyadic χ(k)=0 for 4|k yields |χ(k)|/12≤|kλ_N−J|+k/(140N), J integer. Surviving k≤N have gap≥1/15 from integer frequencies.
Prime13 gap g_M=λ_(13M+1)−13λ_M positive→0. Its inverse-square cosine correlation on [1,∞)→1, fixed-scale Bohr mean→0. This is one shifted channel at beta=1/2, not full-source positivity.

## NEW verified critical admission
F(v)=Σ_(n∈S)b_n Φ_(n+1)(v), real b.
A=2Σ|b_n|, L=14Σ(n+1)|b_n|, P=12Σ|b_n|/(n+1).
Existing exact lattice primitive supplies Q'=F on v>0, |Q|≤P. Actual Bernoulli right derivatives give |F'_+|≤L across all joins.
Differentiate H(v)=v^-2 F(v)Q(rv)/r from right. Derivative = v^-2F(v)F(rv)+E(v), |E|≤P(2A+L)v^-2/r. Right-derivative FTC comparison yields |∫_1^∞v^-2F(v)F(rv)dv|≤P(4A+L)/r for r≥1. Integrand is dominated by A²v^-2.
criticalFactorialSource S b x = 1_(x≤0) exp(x/2) F(exp(-x)).
Exact source identity = Σ (b_n/factorialTailAmplitude n) exp(-x) factorialMuntzCorrectedTail n x.
Its log autocorrelation at log r equals (sqrt r)^-1 times the physical correlation. Every such correlation is integrable. Thus the series of absolute integrated atoms (Λ(r)/sqrt r)*autocorr(log r), r≥2, is summable against constant*Λ(r)/r².
This does NOT claim absolute integrability of the entire prime double integral, coefficient-uniform ℓ² bounds, full polar admission, or complete Weil positivity.

Public lines:
- criticalFactorialPrimeConstant 285
- critical_factorial_physical_correlation_bound 290
- criticalFactorialSource 309
- criticalFactorialSource_eq_correctedTail 319
- summable_criticalFactorialSource_prime 432
- integrable_criticalFactorialSource_product 470
Positive parameters encoded by natural offsets; no public unproved hypotheses.

## Validation — latest authoritative
Affine leaf earlier: targeted build exit0; actual-file audit exit0/empty; seven axiom checks standard only. Logs /tmp/apt_collar_leaf_build.log, /tmp/apt_collar_actual_audit.log, /tmp/apt_collar_final_axioms.log.
Critical leaf:
- Full scratch + four axiom audits exit0, only propext, Classical.choice, Quot.sound. /tmp/apt_critical_admission.log. Installed unchanged declarations (removed scratch API/example/axiom commands, added header).
- Targeted lake --old build '+GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeAdmission' exit0. Four required dependency refreshes: FactorialPhaseHarmonicLayers, EnvelopeCriticalPrimeTransitionAndDilationGain (237s each), FactorialPhaseWindowAndPhysicalRieszBounds (18s), FactorialPhaseBohrCoercivityAndTailIndependence (41s); new leaf 154s. Remaining 17629 jobs cached; no full/umbrella build. /tmp/apt_critical_leaf_build.log.
- Required actual-file lake env lean GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalPrimeAdmission.lean exit0, EMPTY diagnostics, /tmp/apt_critical_actual_audit.log.
- scripts/formal_tools.py index exit0; all six exports present. /tmp/apt_critical_index.log.
- scripts/formal_tools.py lint --check-generated exit0, existing large-file warnings only. /tmp/apt_critical_lint.log. Earlier unrelated umbrella ownership errors were repaired concurrently; old lint-failure reports are superseded.
- Whitespace checks passed. No commits/push or README changes.
- No own build/search/index/lint jobs remain live. Four owned /tmp critical scratch Lean/fragments deleted; prior affine scratch already cleaned. Search JSON and audit logs retained.

## Corpus audit / prior work
Used documented research command directly, candidate_lemmas AND source_arguments, coverage checked; deep long queries often irrelevant/partial. Compiler snapshot mostly pending/stale across entire corpus, so actual source/Lean applicability matters. Never infer novelty from no hits.
Earlier exhaustive lexical screens: factorialShiftedFreq9, dyadicHarmonicChi10, near resonance69, frequency dilation52, mixed frequency87, mean zero primitive80, Bernoulli Lipschitz9.
NEW: all28 bernoulli primitive hits,5 clampedLatticePrimitive hits,36 exact DeningerMeyerStrongLogTarget hits,177 affine profile hits paginated/screened.
Existing exact source primitives:
- BiScaleUncertainty/FactorialMuntzTailPrimitive.lean (full read): factorialMuntzTailLatticePrimitive_abs_le=12, derivative actual remainder, full log-tail identity.
- ClampedLatticePrimitive.lean (full read): public bernoulliCenteredPrimitive_hasDerivAt, bounded collar primitive.
- RHTower/EulerDeletionRemainderFirstCoefficient.lean 1–135 read: bounded centered Bernoulli primitive.
- ArithmeticClockFirstVariation first112 read: global half-Lipschitz and bernoulliPeriodic_hasDerivWithinAt_right (Ici).
- CCMSawtoothDilationMean 420–465 and548–621 read: weighted primitive/Fubini and averaging; generic prior machinery.
- mathlib right-derivative FTC comparison used, names verified in current Lean scratch.
- BlindCoreFarkasSeparation 57–83 read: general exponential autocorrelation change of variables already exists.
- FactorialMuntzTailPrimePolarBudget 16–41 read: canonical beta3/2 tail, correlation decay5/4, not critically reweighted source.
- DeningerCriticalFloquetVonMangoldtWall bound at817 uses its own strong-log source; inspected space at StrongLogTarget165 and LogSchwartzLanding981. Requires all-derivative faster-than-every-exponential decay; critical source does NOT satisfy it, so no external premise discharge claimed.
Generic nearby-prime covariance, divisor square energies, Mobius dilation Parseval already exist. Existing source contrast is a difference of autocorrelations, not arbitrary signed-span positivity.
Preserve foreign FactorialSpanTestPolarPrimeGammaBudgets, FactorialRampSmoothingAndGramMargin, FactorialSpanTestMellinLowFrequency and all other concurrent changes.

Relevant current JSONs:
apt-bernoulli-primitive-search(.json,-20.json), apt-clamped-primitive-search.json, apt-critical-prime-admission-search.json (complete but mostly irrelevant), apt-lipschitz-dilation-search.json (partial interrupted), apt-native-tail-critical-search.json (partial malformed/deadline), apt-autocorr-clock-search.json (complete), apt-deninger-source-space-search(.json,-20.json).
Later: apt-primitive-mellin-boundary-search.json (partial Qdrant timeout/malformed); apt-affine-profile-search.json plus20..160 (all177); apt-affine-model-perturbation-search.json and apt-separated-interpolation-search.json complete but mostly unrelated; apt-affine-model-mv-search.json all3 exact interval declarations.

## Next conjectures (not formalized / not counted)
1. Critical polar continuation: raw R(s)=∫_1∞F(v)v^(-s-1)dv on Re s>0 has candidate continuation -Q(1)+(s+1)∫_1∞Q(v)v^(-s-2)dv to Re s>-1, bound P(1+|s+1|/(Re s+1)). Values0,1 ≤2P. Must distinguish continuation from nonabsolute raw Lebesgue readout. Existing FactorialTailReadout (1–56 read) and FactorialMuntzAnalyticRepair give original tail open domain Re s>-1; critical shift brings boundary to0. Check more exact work before code.
2. WHOLE-SPAN AFFINE MODEL: Ψ_N(v)=P₀((N+1/12)v)-P₀(Nv). Conjecture universal C with ∫_1∞v^-2|Σ_(N≥M)b_N(Φ_N−Ψ_N)|² ≤ C/M Σ|b_N|², all finite complex families. Interpolate frequencies N+1/12−θe_N; remain separated. Duhamel+existing Montgomery–Vaughan gives per-harmonic unit-window bound C min(1,(k(j+1)/M)²)Σ|b|². Sum j^-2 ⇒ Ck/M. Minkowski uses Σk^-3/2<∞.
Exact corpus input HTGeometry/MontgomeryVaughanIntervalMeanSquare.interval_integral_normSq_expSum_le line243 inspected: arbitrary finite frequencies separated by D>0; bound (length+26/(pi D))Σnorm². Reuse it; do not recreate generic frame theorem.
Potential sharpness: N∫_1∞v^-2|Φ_N−Ψ_N|²→7ζ(3)/(256π²). Derivation requires Ne_N→1/144, oscillatory averaging of each mode, ∫_0∞(1−cos av)/v²=π|a|/2, χ² sum=(1−4^-3)ζ3; cross-mode and uniform harmonic-tail interchange remain unproved.
This model preserves actual near-resonances, could reduce critical prime energies to two arithmetic frequency lattices; no full-energy transfer shown.
3. Earlier odd-r χ(rk)=χ(k) mixed separation remains paper-only; dyadic exception r2,k6,N12M+1 gives 12λ_M−N=−12e_M→0, r4,k3 same. Treat prime2 separately with geometric weights.

Continue the 100-contribution goal; do not count declarations or classical helper rephrasing as contributions.