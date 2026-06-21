# R48 - prime-shift aggregation artifact

Status: dead end / PNT substrate warning.

Random source chain:
- seed RandomNode: heavy-tailed waiting times can make sample means unstable and convergence painfully slow
- broad topic RNG: 14, human dynamics and bursty activity patterns
- NODE RNG: 5, aggregating heterogeneous individuals can create apparent power laws even when no individual follows one
- target-file RNG: 2, `docs/consolidated/01-landscape-and-geometry.md`
- target-topic RNG: 5, `G_a` = translation-by-`log p` prime shifts
- scientific-method RNG: 5, make visual
- perturbation-method RNG: 19, fake proof

## Transfer

Each prime-shift lane has exponential dependence in the displacement variable:

```text
exp(-delta log p) = p^{-delta}.
```

But the heterogeneous aggregate

```text
A_X(delta) = sum_{p <= X} log(p) p^{-(1+delta)}
```

approaches the PNT pole-like behavior `A(delta) ~ 1/delta` in the appropriate
limit. Thus a continuum-looking singularity can be manufactured by aggregating
heterogeneous `G_a` rates even though no individual prime lane has such a law.

## Evidence

Script:

```text
computations/2026-06-21-penrose-r48-prime-shift-aggregation.py
```

For `X=2,000,000`:

```text
delta=0.020: A=11.310424, delta*A=0.226208, largest_lane_share=0.031674
delta=0.050: A= 9.101541, delta*A=0.455077, largest_lane_share=0.038085
delta=0.120: A= 5.786403, delta*A=0.694368, largest_lane_share=0.055470
delta=0.200: A= 3.756006, delta*A=0.751201, largest_lane_share=0.080327
```

The visual cue is that the aggregate moves toward pole scaling while the
largest individual prime lane remains a small share.

## Verdict

Dead end for non-reducing count. The fake proof "aggregate pole means a prime
lane carries power-law/RH content" fails at the aggregation step. This is
standard PNT/substrate behavior of the `G_a` prime-shift ensemble, not new
weld or RH-bearing content.
