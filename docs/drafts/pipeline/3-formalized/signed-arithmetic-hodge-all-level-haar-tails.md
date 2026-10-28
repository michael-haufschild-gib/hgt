# High generator tails are small across every level

For every compactly supported real bounded-variation source f, every common
real translation t, and every natural cutoff A>=1, the actual Haar readouts obey

sum_(j>=0,a>=A) c(j,a)^2 <=32 Gamma(f)/(1+log A).

The bound also holds after summing each generator's entire level orbit first.
The square-summable analysis vector has the same squared norm error after
projection onto labels a<A. Every level of each retained label survives.
Complete arithmetic profiles inherit the estimate with arbitrary coarse
coefficients, details and horizon.

Logarithmic weighted summability pays the tail. Product reindexing and the
actual coordinate projection identify its norm; no Gamma estimate on a
projected source is assumed.

Lean: `SignedArithmeticHodgeTheory/HighGeneratorTailsAreSmallAcrossAllLevels.lean`.
Capstones: `logCellHaar_high_orbit_tail_le`,
`logCellHaar_high_detail_tail_le`,
`norm_logCellHaarAnalysis_sub_orbitHead_sq_le`,
`completePair_high_detail_tail_le`.
Final individual no-olean audit passes. Printed capstone dependencies contain
only `propext`, `Classical.choice`, `Quot.sound`.
