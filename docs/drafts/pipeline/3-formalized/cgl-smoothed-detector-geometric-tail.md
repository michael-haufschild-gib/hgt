# CGL smoothed detector geometric tail

- **ID:** cgl-smoothed-detector-geometric-tail
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Chen--Gupta--Li, arXiv:2507.08296v2, Section 12.1 after equation (12.1)
- **Statement:** The shifted detector Laplace profile beyond prefix `K` is bounded uniformly by `C exp(-K x)/(1-exp(-x))`; the exact CGL choice `x=(Y+1)⁻¹`, `K=ceil((Y+1)log²(Y+1))` has remainder at most `2 C (Y+1) exp(-log²(Y+1))`, hence is `o(1)`.

## Goal
Close CGL Section 12.1's smoothed coefficient-tail truncation quantitatively and uniformly in detector length, modulus, character, and critical-strip point. This is one actual Class-I/Class-II partition obligation, not an RH-equivalent reformulation.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: targeted Lean check green, every new declaration axiom-clean
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Use the corpus's universal bound on every shifted detector-tail coefficient and exact geometric sum for `exp(-nx)`. Split the convergent series at `K`, identify the remainder with the translated `tsum`, dominate termwise, and evaluate the geometric tail exactly. At source scale, use `1-exp(-x) >= x/2`, the ceiling inequality `K >= (Y+1)log²(Y+1)`, and exponential monotonicity. Decay follows from

`(Y+1) exp(-log²(Y+1)) = exp(-(log(Y+1))(log(Y+1)-1)) -> 0`.

## Proof

**[PROVED HERE]** Let `a_n` be the shifted detector-tail coefficient. Existing source theorem supplies one `C>0`, independent of `X,q,chi,s,n`, with `‖a_n‖ <= C`. Absolute summability permits the exact split

`sum_n a_n exp(-nx) - sum_{n<K} a_n exp(-nx) = sum_n a_(n+K) exp(-(n+K)x)`.

The norm is at most the corresponding positive series, so

`‖remainder‖ <= C sum_n exp(-(n+K)x) = C exp(-Kx)/(1-exp(-x))`.

For `x=1/(Y+1)` and `K=ceil((Y+1)log²(Y+1))`, the numerator is at most `exp(-log²(Y+1))`; since `0<x<=1`, the denominator is at least `x/2`. This gives the stated uniform bound. Its exponent is `-log(Y+1)(log(Y+1)-1)`, which tends to negative infinity, proving convergence to zero.

## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/ChenGuptaLiClassITailGeometricBound.lean`.

- `exists_cglShiftedDetectorTail_geometric_bound`
- `cglClassITailSmoothingScale`
- `cglClassITailTruncationCutoff`
- `tendsto_cglClassITail_logSquareMajorant_zero`
- `exists_cglShiftedDetectorTail_source_truncation_bound`
- `cglShiftedDetectorTail_source_truncation_tendsto_zero`

Direct source check passed. `#print axioms` for all six declarations reports only `propext`, `Classical.choice`, and `Quot.sound`. Formal lint reports no task-caused error; two unrelated pre-existing umbrella reachability errors remain (`RHTower.WoldDepthXiCompactUniformAmplification`, `HTGeometry.CompactUniformDilation`).

## Frontier effect

CGL Section 12.1's smoothed coefficient tail is closed at the paper's exact cutoff, uniformly in source parameters. Remaining nearby obligations are the safe-line integral-tail truncation and bounded-head principal zero census; downstream Class-I/Class-II moment and global zero-density estimates remain separate.

## Log
- 2026-08-23 — created in 1-in-progress after corpus search exposed universal coefficient bound and exact translated geometric sum.
- 2026-08-23 — `[PROVED HERE]` and formalized; moved to 3-formalized after exact source-scale specialization, targeted Lean, axiom, and lint checks.
