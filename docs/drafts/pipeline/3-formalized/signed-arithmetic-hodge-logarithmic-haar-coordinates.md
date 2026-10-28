# One Gamma reserve controls the logarithmic Haar square function

For every compactly supported real bounded-variation source, every common
real translation, and every finite set S of dyadic level / positive generator
labels, the actual normalized Haar readouts satisfy

sum_(j,a in S) (1+Nat.log(2,a))*c(j,a)^2 <=16 Gamma(f),
sum_(j,a in S) (1+log(a))*c(j,a)^2 <=32 Gamma(f).

Both bounds also retain the complete level orbit of each label in any finite
generator family. The entire ancestor-weighted square function is summable
and bounded by16 Gamma.

Exact variance conservation, summed over every level, gives a binary flow on
generator labels. Its tail quantities obey Q(M)+P(2M)<=P(M), where P is
parent variance and Q is actual readout square mass. Telescoping at powers of
two counts exactly1+Nat.log(2,a) ancestors of label a. All summability is
derived from the joint parent-variance bound; no weighted-variance summability
or source mean constraint is assumed.

Lean: `SignedArithmeticHodgeTheory/BinaryVarianceFlowCountsEveryAncestor.lean`.
Capstones: `logCellHaarOrbitEnergy_flow`,
`sum_logCellAncestorWeight_orbit_le`, `sum_log_weight_haar_orbit_le`,
`tsum_ancestor_weight_readout_sq_le`, `sum_ancestor_weight_readout_sq_le`,
`sum_log_weight_readout_sq_le`.
Final individual no-olean audit passes. All printed capstone dependency lists
contain only `propext`, `Classical.choice`, `Quot.sound`.
