# Separate multiscale conjecture

Frozen after the eight-lag count/centroid predictor failed its discovery gate, before any data with `k>=32` have been inspected. This is a new candidate, not a relaxation of that predictor's 5% gate.

## Observation and question

Discovery covariance of normalized prime counts falls substantially when sixteen cells are replaced by one whole quartic block. All eight fitted count-history coefficients are negative. This suggests testing contraction under aggregation directly, independently of prediction. The exact aggregation identity does not determine the sign or size of the cross terms for the prime source.

**M1, empirical candidate:** over each specified scale range, every successive doubling of cell width among `1,2,4,8,16` fine cells reduces the mean squared normalized count error by at least 20%. No intercept is fitted and no baseline is changed: retain the original `dx/log x` reference. Discovery requires this in `k=4..23` and `k=24..31`; if it advances, validation requires it separately in `k=32..63` and `k=64..89`. Failure retires this specific uniform 20% contraction proposal. It does not refute weaker contraction, RH, or every multiscale mechanism.

For adjacent cells with residuals `C_i=count_i-L_i`, define a group's normalized error as `sum C_i/sqrt(sum L_i)`. Report the mean square and centered variance at all five widths. The advancement rule uses mean squares only. Report every doubling, not only favorable ones.

For the full sixteen-cell grouping, decompose its squared normalized error exactly into diagonal contributions and signed cross terms indexed by cell separation `1..15`. This locates the cancellation rather than imposing a sign on any term. Compare the decomposed total against the independently available whole-block coordinate to check mass/reference bookkeeping. For a statistical control, shuffle the fine normalized errors within each declared range, keeping reference masses fixed; use 256 fixed-seed replicates, and report all widths. These are artificial diagnostic arrays, not prime systems or zero-preserving perturbations.

No mathematical theorem is inferred from a finite variance contraction. A proof route would still need a source-derived deterministic law controlling all relevant prefixes and Mellin phases; average behavior can conceal exceptional blocks. Therefore also report extrema of group errors and counts of adjacent merges that increase the normalized square. Run discovery first and freeze its verdict before opening held-out ranges.
