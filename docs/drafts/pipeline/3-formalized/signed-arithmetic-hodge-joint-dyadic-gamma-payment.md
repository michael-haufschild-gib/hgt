# One Gamma reserve for every nested dyadic parent

For every real compactly supported bounded-variation source f, every real
translation t and every finite set S of pairs (j,a), with j natural and a
positive, the sum of actual parent variances on
[t+j log2+log(2a), t+j log2+log(2a+2)] is at most 16 Gamma(f).
All coarse means are arbitrary. The complete arithmetic-profile specialization
quantifies over every coefficient family and horizon.

The ordered sibling rectangles are pairwise disjoint across levels and labels.
Floor(exp(x-t)) and floor(exp(y-t)) identify their unique binary split. The
local charge pays parent variance/8. Summing disjoint product-measure regions
uses at most the symmetric Gamma difference integral, equal to 2 Gamma(f).

Lean: `SignedArithmeticHodgeTheory/OneGammaReservePaysAllDyadicParentVariances.lean`.
Capstones: `logCellSiblingRectangle_pairwise_disjoint`,
`sum_logCellDyadicParentVariance_le`,
`completePair_sum_logCellDyadicParentVariance_le`.
Final individual no-olean audit passes. Transitive axioms:
`propext`, `Classical.choice`, `Quot.sound` only.

This pays the entire variance family, without an assumed sign for the Weil
form. Weighted Haar bounds require exact variance identities and ancestor counts.
