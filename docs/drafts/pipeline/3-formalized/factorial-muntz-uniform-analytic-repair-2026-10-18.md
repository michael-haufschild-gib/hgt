# Uniform analytic repair of the actual factorial Müntz source

- **Stage:** 3-formalized
- **Routes:** WL/RW, actual factorial-ramp diagonal.
- **Parent:** [actual diagonal margin](../1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md).
- **Predecessor:** [exact boundary repair](../3-formalized/factorial-muntz-boundary-repair-2026-10-18.md).
- **Objective:** Remove the collar-dependent tail constant and the `Re s > 0` restriction from the canonical corrected readout. Produce uniform estimates for the actual source, including the negative polar moment, without assuming a Weil-domain or positivity certificate.

## Plan

1. Audit the source collar bounds, exact boundary remainder, and Mellin differentiation API.
2. Prove the dependency-closed estimates below, then formalise actual-source statements.
3. Check new leaves sequentially with `lake --old env lean`; audit every public declaration, wire imports, index and lint.

## Paper proof

Write `N=n+1`, `epsilon=sourceFactorialCollar N`, `F_n=factorialMuntzCompletion n`, `r_n=sourceFactorialRamp N`, and `c_n=1/(2 sqrt N)`. The already-proved exact boundary estimate has constant `K_n=25/(32 N epsilon sqrt N)`.

The source parameter bounds give `epsilon >= sourceFactorialWidth N >= 1/(15 N)`. Consequently `K_n <= 375/(32 sqrt N) <= 12/sqrt N`. This discharges the apparent nonuniform dependence on the shrinking collar; no extra hypothesis on epsilon is needed.

Let `G_n=F_n+1_(x<=0)c_n exp(x/2)` and `T_n=G_n-r_n`. Exact positive-half-line agreement implies `T_n=1_(x<=0)G_n`. The boundary estimate now gives

`|T_n(x)| <= 1_(x<=0) (12 exp(3x/2)/sqrt N)`.

For every complex `s` with `Re s > -1`, multiplication by the readout kernel gives the integrable majorant `1_(x<=0)12 exp((Re s+1)x)/sqrt N`. Thus

`|integral exp((s-1/2)x) T_n(x) dx| <= 12/(sqrt N (Re s+1))`.

The same argument on `x<=a<=0` gives the sharper cutoff factor `exp((Re s+1)a)`. In particular, both polar-weighted errors are finite with explicit uniform bounds. The compact ramp is integrable against every exponential, so `G_n` has an actual convergent readout throughout `Re s>-1`. On each half-plane `Re s>=-1+delta`, `delta>0`, the tail readouts tend uniformly to zero as `n` tends to infinity.

For analyticity, use the literal multiplicative regularisation `B_n(t)=A_n(t)+(1/2)1_(0<t<=1)`, where `A_n=factorialMuntzSum n`. It is measurable, bounded, supported above by `max(1,factorialMuntzSupport n)`, and satisfies `|B_n(t)|<=12t` on `0<t<=1`. The Mellin differentiation theorem therefore applies with lower exponent `-1`. The exact logarithmic substitution identifies `Mellin(B_n)(s)/sqrt N` with the readout of `G_n`, including at `s=0`. This supplies analytic continuation and the finite part at the negative pole, rather than an assumed holomorphic extension.

On `Re s>0`, the previous exact identity identifies the uncorrected readout with the new analytic function minus `c_n/s`. Its residue at zero is therefore exactly `-c_n`. At a zeta zero in that half-plane, the actual ramp readout is `c_n/s` minus the corrected tail readout, yielding a bound without the previous `1/Re s` singularity in the tail remainder.

The corpus additionally proves every such zero has `|Im rho|>=4`, hence `|rho|>=1`. Since `Re rho+1>=1`, the literal compact-ramp readout at every such zero is bounded by `(1/2+12)/sqrt N <=13/sqrt N`. This proves convergence to zero uniformly over the entire nontrivial zero set, without a height cutoff or RH. The zero-height theorem is used only as a proved dependency, not as a numerical experiment. An infinite unweighted zero sum still requires its own domination argument.

## Scope and open bridge

This removes weighted-tail and analytic-strip obstructions. It does not establish the archimedean/prime full-Weil identity for `G_n`, continuity of the full Weil form under these limits, the coupled diagonal margin, all-source RW positivity, or RH. The correction still jumps at zero. No numerical experiment or web/novelty search is used.

## Corpus evidence and verification

Source inspected: `SignedPrimePolarSourceParameters.lean`, `FactorialMuntzBoundaryPole.lean`, `FactorialMuntzBoundaryRepair.lean`, `FactorialMuntzReadout.lean`, `CCMBVMuntzSummation.lean`, and the installed mathlib Mellin transform API. Searches are recorded in `/tmp/bsu-muntz-continuation-search.json` and `/tmp/bsu-muntz-pole-moment-search.json`; semantic coverage is unmeasured. No exhaustive-search claim.

Both new leaves passed direct `lake --old env lean -j 1` checks: `FactorialMuntzUniformTail.lean` and `FactorialMuntzAnalyticRepair.lean`. They contain 26 public theorems and two definitions. All 28 public declarations passed the `/tmp/bsu-muntz-uniform-axioms.lean` audit, with only `propext`, `Classical.choice`, and `Quot.sound`. The narrow mathlib API probe also passed. Both modules are wired exactly once into the area umbrella.

The first initial check stopped at a missing imported object before elaboration. Three missing unchanged dependencies (`ClampedExponentialRamp`, `SignedPrimePolarHarmonicCorrection`, `SignedPrimePolarFactorialLift`) then passed direct single-thread compilation. No source change was needed in those dependencies. Checks used existing dependency objects; the import-closure audit recorded 133 pre-existing objects older than their source timestamps. This is not a fresh whole-tree build. No private object cache was created, and no full or umbrella build was run.

`scripts/formal_tools.py index` passed and refreshed `formal/LEAN_API.md`, `formal/LEAN_GAPS.md`, and `formal/LEAN_OVERVIEW.md`. `lint --check-generated` returned 1: five unrelated modules from concurrent work are unreachable from their area umbrellas:

- `BiScaleUncertainty.AffineFourierCorrelation`
- `BezoutValuationIncidence.DilatedCellScalingAndSecondOctaveFermiJumpBridge`
- `BezoutValuationIncidence.EndpointHaarCellDecompositionAndWitnessPronicTransfer`
- `BezoutValuationIncidence.PowerDampedPronicMultiplicativityAndRoutePMBridge`
- `BezoutValuationIncidence.ReturnWindowTwoMomentKernelsAndSharpZeroBlocks`

No lint error names either new module. The gate also reports 381 pre-existing large-file warnings. No unrelated module was modified. Verification evidence, exact source hashes, object freshness, import counts and all 28 axiom lists are recorded in `/tmp/bsu-muntz-uniform-verification.json`. Logs: `/tmp/bsu-FactorialMuntzUniformTail.log`, `/tmp/bsu-FactorialMuntzAnalyticRepair.log`, `/tmp/bsu-muntz-uniform-axioms.log`, `/tmp/bsu-uniform-index.log`, `/tmp/bsu-uniform-lint.log`. The first leaf has one harmless tactic-style warning; the second leaf log is empty. All owned compiler and gate processes have exited.

## Next source-level bridge

`RHTower.WeilSpectral.archPoleEnergy_eq_re_W_add_abelPrimePairing` supplies the explicit formula once an actual `ExpDecayTest` is produced. A compact smooth convolution of the canonically corrected source is a concrete candidate: use the new exponential bound to justify convolution, move derivatives onto the kernel, and prove the exact readout product by Fubini. This construction and its normalization have not been formalized here. The search `/tmp/bsu-muntz-smoothing-followup-search.json` completed without reported execution errors but with unmeasured semantic coverage. Its `AllExpDecay.convolution` hit requires decay at every exponential rate; the present fixed-rate estimate does not discharge that premise. Do not silently use it or infer an unsmoothed full-Weil limit.
