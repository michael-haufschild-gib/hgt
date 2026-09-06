# Larger-scale stress test E3

Frozen after B2 validation and before computing any prime counts above `90^4`. B2 remains a successful finite test, not an all-scale theorem. Its ratios visibly increase with scale. The primary-source variance papers cited in the report supply a reason to question persistence of a fixed fractional improvement, but do not settle this particular finite statistic.

**E3, extension conjecture:** the same whole-block/fine-cell mean-square ratio remains at most `1/2` at every one of the eight prescribed boundary phases on the new range `k=128..159`. No coefficient, phase, baseline, or threshold is fitted. Test all 32 blocks and all eight phases, not a selected subset. One phase exceeding the ceiling rejects E3; report every phase.

Only intervals required for this new range are sieved; do not generate the entire prime array to the larger endpoint. Eight workers, one core each, 120-second cap. Compare 32-/64-point quadrature in every new cell. Archive actual endpoints, counts, masses and diagnostics. Numerical outcome neither proves an all-scale law nor disproves RH. If the fixed margin fails, do not lower the threshold to preserve a successful label.

## Frozen second scale band, after E3 passes

E3 passes all eight phases with ratios `0.3759..0.4761`. Freeze **E4** on `k=256..319`, preserving the proportional band `[K,5K/4)` used in E3. Its threshold, reference, cell count, and eight phases are unchanged. Test every block. This is the last numerical scale extension in this experiment, regardless of its outcome; a surviving finite bound would still need a new arithmetic proof mechanism. Use the same eight-worker, 120-second cap. Each worker holds only one interval at a time.
