# CCM-FU: middle-prime energy with fixed signed reserves

- **ID:** CCM-FU-MIDDLE-RESERVES
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Parent:** [growing signed batches](../3-formalized/ccm-fu-growing-signed-prime-batches.md)
- **Target:** Control the nonempty overlapping field during actual middle-prime processing, retaining the fixed isolated signed supplies and their finite square reserve.

## Full proof chain and exact gap

Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints → signed curvature → prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green → RH. Growing selected batches have a proved uniform quadratic energy ceiling, but do not cover all primes or bound the complete final signed source.

After processing P0, the primes below eight, every unprocessed p with M<8p is isolated. Its singleton survives arbitrary further processing that does not consume p. Such scalar supplies steer the head and remove their own squares, but do not alter other nonempty fibres. The remaining obstruction is therefore a source bound on the overlapping nonempty field and complete final compensation, not mere availability of both signs.

## Diagnostic question

For increasing prime processing starting after P0 and ending at the square-root threshold, does the nonempty field excluding all fixed isolated primes stay within an observed uniform quadratic budget? Where does it increase, and which source-labelled mixed products create the largest increases? These values have not been established by the existing small-cutoff step-contraction diagnostic.

Run only a bounded multicore diagnostic on RunPod, using the corpus's exact clipped channel formula as a numerical representation. Retain both signed and unsigned conventions explicitly. Inspect a fixed geometric set of cutoffs through 2^20; no exhaustive prime-order search. Download the script, per-stage results, and summary under the computations directory. These results guide symbolic arguments only and cannot enter a Lean proof.

## Formal work to select from evidence

- Derive exact fixed-reserve projection and arbitrary-middle-state transport.
- Identify an actual arithmetic estimate or a counterexample before positing nonempty contraction.
- Prove any selected estimate analytically in Lean; a general control receiver alone does not settle the source bound.
- Retain complete final-source control as a separate open obligation even if the middle stage is bounded.

## Analytic obstruction selected from the diagnostic

The RunPod screen found residual energy above the original diagonal even after
subtracting every fixed isolated singleton square. The main growth lies in
retained singleton labels, inherited from smaller-cutoff partially processed
heads. This suggests the following stronger, non-numerical obstruction.

Take parent cutoff `M=64N^2` and processed core consisting of all primes below
`4N`. For every prime `p in (8N,9N]`, both adjacent quotient cutoffs `K=floor(M/p)`
and `K+1` lie in `[7N,8N]`. At either child cutoff all unprocessed primes are
late. The exact head identity is the complete signed source plus their positive
unsigned mass. The window `(4N,5N]` supplies at least
`N sqrt(N)/(80 log(4N))`: a uniform first-block floor `sqrt(N)/40` and the
corpus prime-window count. The proved uniform limit
`S(K) log(K)/(K sqrt(K))->0` makes the complete-source correction at most half
that mass throughout `[7N,8N]`. Thus each child head is at least
`N sqrt(N)/(160 log(4N))`.

Exact clipped reflection gives a negative parent singleton of magnitude at
least `N^2/(80 log(4N))` for every p in the parent window. There are eventually
at least `N/(2 log(8N))` such primes. Their squared energy divided by M² is
therefore at least `N/(52428800 log(8N)^3)`, which tends to infinity.

Any selected pool of fixed scalar primes `l` with `M<8l` changes neither these
middle singleton fibres nor their positive square sum. Hence increasing
middle-prime processing cannot be rescued by arbitrary interleavings of those
fixed scalar supplies, even with any fixed quadratic energy multiplier.

The positive survivor is the exact nested source-head amplification and its
unchanged nonempty-coordinate energy under fixed scalar control. A surviving
complete schedule must move nonisolated primes across the increasing middle
front, or otherwise control this inherited field before the indicated stage.
This paper argument is being formalized; the analytic no-go is not yet a Lean
certificate. Full adaptive schedules, SD1, and RH remain open.
