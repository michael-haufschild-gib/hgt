# Optimal successor prediction and arithmetic phase loss

- **ID:** bvi-successor-compression-phase-loss
- **Stage:** 3-formalized
- **Type:** THEOREM; COUNTED010
- **Source:** Finite sieve responses, simultaneous Selberg–Möbius forms, exact
  internal-period CRT counts, and the field's translation-period classification.
- **Statement:** Determine the exact closest divisor-sieve response to the
  integer successor of an arbitrary sieve signal, and classify all information
  preserved or lost by that arithmetic compression.

## Motivation and significance gate

The field has exact covariance and internal translation periods. A missing
structural question is whether the divisor-response model itself is closed
under integer succession, and what information an optimal model of the shifted
response must discard. This asks about the actual integer signal on its internal
period, not an abstract diagonal form alone.

Do not count a generic weighted least-squares identity, renamed inverse, or
contraction corollary as a significant contribution by itself. Require a genuine
closure/phase-loss classification and its exact physical realization. Audit any
stronger unit-average or repeated-compression law before committing to it.

## Initial audit and durable plan

- Objective and full341-line field README read; root/formal instructions, formal
  guides and pipeline template read. Architecture/testing docs absent. Starting
  verified count9 / 250. Previous goal turn: PROGRESS.
- Local memories for progress, primitive-energy frontier and local-corpus-only
  restriction read. Field inventory21 leaves. No new Lean code or owned Lean job.
- Deep searches pending: `sieve successor projection unit average` and
  `Ramanujan translation compression Markov`, both90-second budget.
- Source inventories show `DivisorPhysicalProjection` concerns continuous
  cellular velocity spaces, while `CoprimeAlternatingProjectionRate` concerns
  arithmetic tent spaces. Those are not yet evidence of this finite sieve result.
  Existing `DivisorSieveAffineSpectrum` supplies DFT/affine signal tools; inspect
  applicability before reuse. `TwoLagSievePeriod` supplies general joint counts.

1. [x] Inspect all search sections, equivalent local results, and needed source.
2. [x] Close exact paper statement, dependency proof, and novelty/significance audit.
3. [x] Probe installed APIs and formalize the unconditional package.
4. [x] Original-source checks, every public axiom closure, wiring, exhaustive index,
   lint, installed artifact checks, ledger/memories and cleanup; only then count010.

`update_plan` is unavailable; this card is the durable plan. Temporary prefix
`/tmp/bvi10-*`. Local corpus only; no RH focus, hgtl7, experiments, README edits,
full/umbrella builds, heartbeat hacks, commits or subagents. One owned Lean process
at a time: require terminal exit_code before the next launch. Preserve foreign work.

## No-go closure

If succession fails to preserve divisor responses, prove the strongest positive
survivor: exact invariant subspace, optimal compression, sharp unavoidable loss,
or complete arithmetic classification. Record all paper and Lean statuses.

## Local novelty audit (010)

All returned sections inspected in three deep searches (90 seconds each):
`sieve successor projection unit average` (20 candidates,20 arguments; partial,
reranking deadline and judge disconnect), `Ramanujan translation compression
Markov` (20,20,one idea,one ingredient; complete), `moebius totient sum multiples
divisors` (20,20,one ingredient; complete). All three report older coverage
snapshots and unavailable semantic coverage. Lexical searches, uncapped by module,
were fully paged: `Ramanujan unit`28 hits and `sieve projection`47 hits.
No equivalent finite integer successor prediction theorem found in returned
material. This is a local-corpus assessment, not a global novelty claim.

`DivisorPhysicalProjection` uses continuous cellular velocity spaces;
`CoprimeAlternatingProjectionRate` uses arithmetic tent spaces;
`DivisorSieveAffineSpectrum` provides affine DFT recovery, not this projection.
The existing two-lag period covariance is infrastructure. The newly concurrent
`JordanUpperBoundAndGcdOrbitPrimitiveEnergy` and
`RenormalizedMobiusDefectAndFirstOctaveCancellation` have distinct scopes.

## Dependency-closed paper proof

Write Y(q)=Σ_{q|d,1≤d≤N}c(d)/d, Q=Σφ(q)Y(q)², P=N!,
S_c(k)=Σ_{d|k,1≤d≤N}c(d). Define

    Kc(d)=μ(d) Σ_{d|m,1≤m≤N} c(m)/φ(m).

This vanishes outside[1,N] and on nonsquarefree d. Its actual integer signal is

    S_Kc(k)=Σ_{1≤m≤N, gcd(m,k)=1} c(m)/φ(m).

Swap the two divisor sums and apply the existing Möbius coprimality indicator
(`CoprimeClassCount.coprime_indicator`). For q|m with q,m positive,

    Σ_{q|d|m} μ(d)/d = μ(q)φ(m)/(φ(q)m).

To prove this, write m=qt and d=qr. Möbius multiplicativity gives
μ(qr)=μ(q)μ(r) when gcd(q,r)=1, and zero otherwise because a nonsquarefree
product has a squared common prime factor. The existing exact identity
`TotientMulMoebius.totient_mul_eq` gives
φ(qt)=φ(q)Σ_{r|t,gcd(q,r)=1}μ(r)t/r. Divide by qt. Swapping sums now yields

    Y_Kc(q)=μ(q)Y_c(q)/φ(q).

The zero and outside-level cases are empty sums. Every positive denominator used
above is justified by positive divisor membership; no zero division premise is
left on a main theorem.

Actual CRT counts over Ioc(0,P] give the symmetric bilinear pairings

    mean S_b(k)S_c(k)=Σφ(q)Y_b(q)Y_c(q),
    mean S_b(k)S_c(k+1)=Σμ(q)Y_b(q)Y_c(q).

The installed joint-density theorem proves symmetry even for different weights.
Polarizing the existing zero/one-lag self-covariances proves the two displayed
diagonals. Periodicity and telescoping give mean S_c(k+1)²=Q(c). Therefore

    Err(c,b)=mean (S_c(k+1)-S_b(k))²
            =L(c)+Q(b-Kc),
    L(c)=Σ_{3≤q≤N}(φ(q)-μ(q)²/φ(q))Y_c(q)².

The q=1,2 terms vanish exactly. Strict positivity of φ makes Kc the unique
minimizer on active coefficients; coefficients outside the level are irrelevant.
Two inputs have the same predictor iff all squarefree Selberg coordinates agree:
μ(q) is nonzero exactly on squarefree q and the multiples transform is invertible.
The exact range consists of zero-extended squarefree-supported raw weights.
For sufficiency, nonsquarefree coordinates of such a weight vanish (every multiple
is nonsquarefree); prescribe inverse coordinates φ(q)Y_b(q)/μ(q), then use finite
multiples inversion and zero extension.

Let W=Σ_{3≤q≤N}φ(q)Y_c(q)². Since φ(q)≥2 and |μ(q)|≤1 there,

    3W/4 ≤ L(c) ≤ W.

The lower equality modes are exactly3 and6: equality forces φ(q)=2 and |μ(q)|=1;
the installed small-totient classification leaves3,4,6 and μ(4)=0 removes4.
Upper equality means all squarefree coordinates above parity vanish. Pure3 and
pure4 modes from the existing finite inverse attain the two constants.
Thus L=0 iff all coordinates above2 vanish, equivalently all raw coefficients
above2 vanish by the existing tail-zero equivalence.

Finally Err=0 iff the actual periodic signals agree everywhere: nonnegative
summands vanish on one complete period, then periodicity extends equality to all
natural k, including k=0. Hence the successor is itself a divisor-sieve response
iff c is supported on1 and2 within its level. This proves both the closure
obstruction and its exact positive survivor; all N=0,1,2 cases are retained.

**Committed scope:** explicit coprimality predictor, physical least-squares
identity/uniqueness, exact retained information and range, closure classification,
sharp loss bounds with equality and witnesses. These form one connected result.
Unit averaging and iterated compression are not asserted. In particular, powers
of compressed succession must not be equated with projections of true multi-step
translation. Paper proof complete; Lean status pending.

## Implementation checkpoint

Three owned leaves drafted: `CoprimalitySuccessorPredictorAndSquarefreeInformation`
(explicit transport/spectrum/kernel/range), `OptimalSuccessorPredictionAndExactPhaseLoss`
(actual cycle pairings, error Pythagoras, optimality/uniqueness, zero-error equivalence),
`SharpSuccessorPhaseLossAndClosureClassification` (sharp bounds/equality, exact closure,
complete universal-constant classifications). Current inventory47 named declarations,
23 public including4 definitions. Counted once as contribution010 after verification.

Initial API probes and combined scratch checks completed. First-module cast
normalization corrected; its exact original source now compiles with no diagnostics.
The combined second/third check found one sum-normalization error and one unused
binder in the physical-pairing module, both corrected. The sharp-loss/closure
module had no additional diagnostics. The second exact original-source check
also passed with no diagnostics. Third exact original-source check passed without
diagnostics. All three leaves wired; index refreshed. Axiom/artifact audits passed.
Isolated cache `/tmp/bvi10-olean-cache`, workspace `/tmp/bvi10-formal`.
All launched owned Lean checks remain sequential; foreign builds are untouched.

Concurrent scope recheck: headers and introductory statements of
`AllOctaveFermiJumpReciprocityAndDyadicSiblingPolarization`,
`PredictableMartingaleDecompositionAndCovarianceCancellationBridge`, and
`RadicalInvariancePrimePowerAbsorptionAndSubHorizonFermiEvaluation` concern dyadic
cell jumps, compensated prefix martingale sums, and power-damped radical invariance.
None supplies this finite successor least-squares/range/closure classification.

## Final verification and closure

- Three exact original-source checks exited0, without diagnostics, using
  `lake --old env lean -j 1 --root=/Users/michael/Documents/code/hgt/formal -o <isolated olean> <original source>`.
  No full/umbrella build, altered heartbeat limit, proof debt, or numerical experiment.
- All23 public declarations (19theorems,4defs) have exactly
  `propext`, `Classical.choice`, `Quot.sound`. Every declaration audited in `/tmp`.
  Raw output: `logs/bvi-root-2026-10-18-successor-prediction-axioms.txt`.
  SHA256 `1bcfa8089d4c6146d1d89aaaf9bae2b830db211db12acec4a2a8aba0a809e778`.
- All47 named declarations match lexical index names/kinds/lines. All23 public
  declarations match cache/API names/kinds/lines; source line counts match cache.
  Three leaves wired once, with existing MainTheorems/root linkage intact.
  Verified oleans installed atomically; source and installed-artifact hashes match.
- The source/olean pairs are:
  - `CoprimalitySuccessorPredictorAndSquarefreeInformation`:266lines,10named/5public,
    source `0c8fb27866e96645308d7279e91f88d293147d0d118d7ed9db13ccc9efeb54f0`,
    olean `0c8badb9a82ffe8d744646083aa688d12782bc66d84b3e0e512c1c0c6fa7e2db` (424240bytes).
  - `OptimalSuccessorPredictionAndExactPhaseLoss`:273lines,22named/9public,
    source `34bfa4c70c3067308ec3b37772750122362bd5ff73d0bd8bda030cb2e9557036`,
    olean `8ef5d13a67dd82c64f23b72428742d2af175ee407b5527ebcc5c8c81e080767a` (686768bytes).
  - `SharpSuccessorPhaseLossAndClosureClassification`:255lines,15named/9public,
    source `37fcdf44c7c70c57004acd307086405975cf21bfb970bb67ddbf453422285592`,
    olean `1b46031c76185bd77e54fc8464345f83d2fe3e883a2ed4e44e44224f1afa7395` (674792bytes).
- Authoritative lint exited1. All397 lines processed:381 foreign large-file
  warnings and16 foreign umbrella omissions; no owned finding or proof-debt error.
  RHTower: `PaperEGCArithmeticRay`, `PaperEGCSourceRayBaseline`.
  BiScaleUncertainty: `ClampedLatticePrimitive`, `FactorialMuntzTailPrimitive`,
  `FactorialMuntzTailPrimitiveEnergy`, `FactorialMuntzTailReadoutDecay`,
  `HorizontalGammaDifference`, `LogGridUniformDirichletTail`, `SieveMomentFourier`,
  `SixthValuationPhaseRecovery`, `ValuationTripleResonance`.
  BVI: `AllOctaveFermiJumpReciprocityAndDyadicSiblingPolarization`,
  `JordanUpperBoundAndGcdOrbitPrimitiveEnergy`,
  `PredictableMartingaleDecompositionAndCovarianceCancellationBridge`,
  `RadicalInvariancePrimePowerAbsorptionAndSubHorizonFermiEvaluation`,
  `RenormalizedMobiusDefectAndFirstOctaveCancellation`.
  Concurrent wiring subsequently left only the Jordan and renormalized-defect
  leaves unwired among29 field leaves at the index/artifact audit.
- This task did not edit the field README. Concurrent work appended22 lines
  describing pillarsXIII–XV; all additions read and preserved. Current363-line
  README SHA256 is `b5a00a91eacf4d089368efb22a871ed4d5a751a7041fcdf66a48b7d92e924760`.
- Negative closure obstruction and strongest committed positive survivor are both
  formalized: explicit best response, exact information quotient/range, sharp
  unavoidable loss, and complete representability classification. No open proof
  obligation remains in this contribution. Goal remains active at10 / 250.
- Guarded cleanup removed all32 owned temporary paths. Every owned job is terminal;
  source, installed-artifact, axiom-log and current README preservation checks passed.
  Durable complete audit: `logs/bvi-root-2026-10-18-successor-prediction-audit.json`.
