# Uniform Gamma stability of actual generator heads and tails

Status: formalized in Lean 4.

## Theorem

For every positive generator cutoff A and every finite real logarithmic-cell
source f, let h be its actual whole-orbit generator head and t=f-h. Then

Gamma(h)<=32 exp(2) Gamma(f),
Gamma(h)+Gamma(t)<=(2+96 exp(2)) Gamma(f).

The constant is independent of source cardinality, coefficients, horizon,
cutoff and translation depth. Both profiles are the literal compact BV
functions; no Gamma-stability premise is added.

The complete even-prime-power source also satisfies

abs(S_even(f)-S_even(h))
 <=(epsilon+C_epsilon/(1+log A))*Gamma(f).

For every delta>0 there is one A0 before all finite sources and horizons;
every A>=A0 gives error<=delta Gamma(f).

## Mathematical argument

Write k(s)=exp(-s/2)/(1-exp(-2s)). For 0<s<=t<=7s and
t-s<=2, the geometric-series inequality 1-r^7<=7(1-r) gives
k(s)<=7 exp(1) k(t). The bound 1<=2 exp(1) t k(t), for 0<t<=2,
pays integrated touching-boundary defects with far-end rectangle charges.
Together these give the uniform rectangle constant C=32 exp(2).

The padded grid starts at -log(2), reaches zero after one cell, follows the
original log cells up to log(A), and then repeats the widths log(a+1)-log(a)
for A<=a<2A at every dyadic translate. Reciprocal bounds for log-cell widths
give adjacent ratios<=3. An intervening neighbor pays both endpoint widths
for every nonadjacent pair. A nonzero row separated from a padded exterior
has the same width-scale gap.

Each translated block indicator is the square-root block-length multiple of
a normalized retained cell. The generator projection fixes this indicator.
Self-adjointness equates its pairing with the original source and the head,
so the two profiles have the same integral on each block. The explicit
physical-height formula makes the head constant there. Therefore the head
is the original interval mean, including on every translated stopping cell.

Both profiles are finite compact BV sources, vanish below zero and vanish
above finite explicit endpoints. Choose the right grid boundary above both
support endpoints plus one. Since every width is at most one, the last cell
has zero original mean; the initial negative cell does too. All geometric,
mean and support conditions of the averaged-kernel theorem are then actual
properties of these sources.

The exact averaged-energy decomposition consists of mean-pair rectangles
and twice the exterior rows. Each is at most C times its far-end charge.
The simultaneous original-source mean-variance capacity inequality pays their
sum once, giving Gamma(h)<=C Gamma(f). The quadratic triangle inequality
gives Gamma(t)<=2 Gamma(f)+2 Gamma(h). Consequently
Gamma(h)+Gamma(t)<=(2+3C)Gamma(f)=(2+96 exp(2))Gamma(f).

For the complete even-power source, choose its signed compensation parameter
as epsilon/K. This gives error<=(epsilon+C_epsilon/(1+log A))Gamma(f).
Choosing A0 above exp(2 C_epsilon/delta), with epsilon=delta/2, pays the full
error by delta Gamma(f), uniformly for every A>=A0 and every finite source.

## Lean declarations

- [ComparableIntervalsHaveComparableGammaKernels](../../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/ComparableIntervalsHaveComparableGammaKernels.lean): `gammaIntervalKernel_le_stopping_of_touching`, `gammaIntervalKernel_le_stopping_of_gap`, `gammaKernel_le_stopping_far_of_gap`.
- [GradedIntervalAveragesHaveUniformGammaControl](../../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/GradedIntervalAveragesHaveUniformGammaControl.lean): `levyEnergy_interval_average_le`.
- [StoppingCellsFormAUniformlyGradedPartition](../../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/StoppingCellsFormAUniformlyGradedPartition.lean): `stoppingGridWidth_adjacent`, `stoppingGridBoundary_strictMono`, `stoppingGridBoundary_band`.
- [PaddedGradedGridsHaveUniformGammaControl](../../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/PaddedGradedGridsHaveUniformGammaControl.lean): `levyEnergy_padded_grid_average_le`.
- [ActualGeneratorHeadsAreLocalIntervalMeans](../../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/ActualGeneratorHeadsAreLocalIntervalMeans.lean): `actualGeneratorHead_eq_intervalMean`, `integral_actualGeneratorHead_block`.
- [ActualGeneratorHeadsAndTailsHaveUniformGammaBounds](../../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/ActualGeneratorHeadsAndTailsHaveUniformGammaBounds.lean): `actualGeneratorHead_gamma_le`, `actualGeneratorHead_tail_gamma_le`, `actualGeneratorHead_tail_gamma_wholeCell`.
- [AllEvenPrimePowersHaveOriginalGammaApproximation](../../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/AllEvenPrimePowersHaveOriginalGammaApproximation.lean): `exists_actualGenerator_even_originalGamma_bound`, `exists_allEvenPrimePowers_generator_approximation`.

## Verification and scope

All seven modules pass individual Lean checks. Printed capstones depend only
on propext, Classical.choice and Quot.sound. The umbrella imports the modules;
no umbrella or full build is run.

This is uniform Gamma stability combined with small L2 tails. Complete
retained translation orbits remain infinite-dimensional and noncompact.
First-prime payment, both exponential Weil moments and retained-orbit sign
remain separate from the Gamma bound and even-power approximation.
