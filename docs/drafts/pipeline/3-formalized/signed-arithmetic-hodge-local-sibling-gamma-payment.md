# Local Gamma payment of the entire parent variance

For a real L2 source and adjacent intervals of widths L,R, the actual parent
variance equals the sum of the two child variances plus
LR/(L+R) times the squared difference of their actual means.

When L+R<=1, the ordered sibling rectangle of the original Gamma difference
kernel pays min(L,R)/(2(L+R)) times parent variance. Constant-kernel payment
retains both child variances and the mean displacement; the proved density
bound 1/(2t)<=archLevyDensity(t) supplies the comparison.

The actual logarithmic children have at least one quarter of the parent's
width. Their sibling rectangle therefore pays parent variance/8, uniformly
over every positive parent label and every real translation. The complete
arithmetic profile capstone quantifies over all coarse coefficients, detail
coefficients and horizons, with no unpaid analytic premise.

Lean: `SignedArithmeticHodgeTheory/TheSiblingGammaChargePaysItsParentVariance.lean`.
Capstones: `intervalVariance_adjacent_eq`, `sibling_gamma_ge_parent_variance`,
`logCellSibling_gamma_ge_variance`,
`completePair_logCellSibling_gamma_ge_variance`.
Final individual no-olean audit passes. Transitive axioms are
`propext`, `Classical.choice`, and `Quot.sound` only.

Joint allocation across nested parents is formalized in
`OneGammaReservePaysAllDyadicParentVariances.lean`, using disjoint sibling
rectangles. These Gamma estimates supply no full-Weil sign.
