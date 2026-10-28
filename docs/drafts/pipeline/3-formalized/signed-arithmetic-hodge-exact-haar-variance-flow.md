# Exact physical Haar readout and dyadic variance conservation

The normalized readout on the actual pair at level j and label a is
c(j,a)=sqrt(haarMass(a)) times the difference of its two interval means.
Its pairing with the existing translated haarProfile equals
sqrt(haarMass(a))*c(j,a). This fixes the physical normalization.

The exact source identities are

V(j+1,a)=V(j,2a)+V(j,2a+1)+c(j+1,a)^2,
c(j,a)^2<=V(j,a).

The proof uses exact adjacent-interval variance splitting and the literal
logarithmic endpoint identities under translation by log2. All statements
hold for every real L2 source and every common real translation. Coarse means
are unconstrained. The identities supply the conservation law needed to
count ancestors without a second Gamma allocation.

Lean: `SignedArithmeticHodgeTheory/DyadicVarianceSplitsIntoTheLiteralHaarReadout.lean`.
Capstones: `integral_translated_haarProfile_mul`,
`logCellHaarReadout_sq_le_variance`, `logCellDyadicParentVariance_split`.
Final individual no-olean audit passes. Transitive axioms:
`propext`, `Classical.choice`, `Quot.sound` only.
