# Boundary placement diagnostic and weaker bridge B2

M1 remains failed. Its 20% contraction at every doubling is not weakened or reinstated here.

**[BRIDGE] B2:** the large reduction from sixteen fine cells to a whole block is robust to moving the bin origin. Specifically, the ratio of whole-block to fine-cell mean squared normalized count error is at most `1/2` at each of eight prescribed origin shifts, in each prescribed range. This is a finite empirical bridge concerning endpoint suppression, not an all-scale theorem, monotonicity at intermediate widths, or a sufficient RH criterion.

For quartic width `W=(k+1)^4-k^4`, use edges `k^4+floor(W*(8*j+t)/128)` for `j=0..16`, `t=0..7`. Thus `t/8` shifts the origin by a fraction of one fine cell. Use exactly the original `dx/log x` reference and no fitted parameters. All eight phases are reported; they share primes and are not independent replications.

Discovery training uses `k=4..22`, screening uses `k=24..30`. Validation, opened only if all discovery phases pass, uses `k=32..62` and final range `k=64..88`. The final block of each earlier interval is omitted so shifted cells never cross a data-split boundary. All shifted discovery cells are below `32^4`. The first predictor and M1 validation sets remain unused for their rejected candidates.

Save actual cell counts, reference masses, and endpoints. Report the full phase table, worst whole-block normalized error, and the number of individual blocks whose normalized square exceeds their children's average square. Check 32-point quadrature against 64 points for all cells. Run eight independent phase jobs with one thread each on the authorized Runpod. Discovery precedes validation; no new threshold is fitted after either output.

The scientific use is discrimination: if suppression is fragile under harmless shifts of a boundary, the original grid is a poor source of rigidity conjectures. Robust endpoint suppression would expose a real finite-range correlation to explain, while the failed intermediate contractions would still rule out the tested monotone mechanism. Neither outcome controls exceptional prefixes, all Mellin phases, or unbounded scales.

## Frozen before validation

B2 passes all sixteen discovery range/phase comparisons, with ratios `0.0813..0.3099`. Its original `1/2` threshold and every phase remain fixed for validation.

Discovery also has zero individually expanding whole blocks. Freeze a separate stronger mathematical hunch **C2** before viewing validation: for every `k>=4` and every integer `t=0..7`, let `C_j` and `L_j` be the exact prime count residual and reference mass in the sixteen intervals prescribed above. Then

`(sum_j C_j)^2/(sum_j L_j) <= (1/16) sum_j C_j^2/L_j`.

The motivation is the absence of expansion in all 208 discovery phase/block observations, with their substantial overlap explicitly acknowledged. C2 is a pointwise source inequality, not a statistical model; one reliably recomputed ordinary-prime block violating it falsifies C2. It is not claimed sufficient for RH: its particular quartic windows do not supply recursive control of arbitrary intervals. The displayed inequality would be a nontrivial improvement over Cauchy–Schwarz, which only supplies the right side without the factor `1/16`. C2 is independently tested, regardless of B2's aggregate verdict. A failure must not be repaired by selecting a favorable phase or deleting the offending block.
