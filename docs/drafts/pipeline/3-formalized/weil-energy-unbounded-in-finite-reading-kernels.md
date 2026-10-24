# Weil energy is unbounded in every finite-reading kernel

- **ID:** weil-energy-unbounded-in-finite-reading-kernels
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Q-II research](../1-in-progress/q-ii-source-effectivity-and-linear-degree.md)
- **Statement:** At every positive aperture, every finite-dimensional linear source reading has a kernel with unbounded Weil Rayleigh quotient and unbounded positive Weil energy.

## Exact statement

For every `r>0`, every finite-dimensional real vector space `V`, every linear map
`L:realTestsAt r→V`, and every real `M`, there is a test `f` with
`L(f)=0`, `∫f²>0`, and `M∫f²<W(f,f)`. Consequently, for every real `A`, such a kernel
also contains a test with `A<W(f,f)`.

No positivity, RH, spectral location, or source-recovery premise is assumed.

## Paper proof

[PROVED HERE] A finite-dimensional reading cannot annihilate all compact tests in a
positive interval. Take more independent translates of a nonzero compact smooth bump than
the dimension of the target. The restricted linear map has a nonzero kernel.

Apply this construction jointly to `L`, the pole reading, and the finite Fourier grid at
`horizonFreqEps r (max M 0)`. If the resulting nonzero test had Weil energy at most
`max(M,0)∫f²`, the established near-radical concentration law would imply
`π∫f²≤bandMass`. Vanishing on the chosen grid implies `bandMass≤∫f²`. Since the mass is
positive and `π>1`, this is impossible. The support remains in the original fixed aperture.
Scaling a kernel test with positive energy gives arbitrarily large absolute energy.

## Consequences

Every finite scalar L² source reserve fails Bézout at every positive aperture, for the
closed, strict, and graded source cones. In particular the unconditional negative-Chebyshev
graded RR cone fails Bézout. Removing the cone boundary cannot fix the obstruction.

More generally, every reserve `F(Lf)` fails Bézout, including arbitrary nonlinear `F` and
arbitrary offsets. On `ker L` the reserve is the constant `F(0)`, while Weil energy is
unbounded. Translate a suitable source to polar capacity `max(F(0),0)`: it is effective and
has negative square. Finite Fourier sampling and finite sums of squared samples are special
cases. This argument concerns the whole positive-aperture source space, not a prescribed
finite-dimensional source subspace.

## Lean certificate

`formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/WeilEnergyIsUnboundedAtEveryAperture.lean`:

- `exists_nonzero_realTestAt_in_ker`
- `exists_realTestAt_in_ker_weilPair_gt_mul_integral_sq`
- `exists_realTestAt_in_ker_weilPair_gt`
- `realTestsAt_l2SourceCones_not_bezout`
- `gradedChebyshevSourceCone_riemannRoch_and_not_bezout`
- `finiteLinearReadingSourceCone_not_bezout`

Individual Lean compilation succeeded. Transitive `#print axioms` for both unbounded-energy
endpoints and the three main Bézout consequences reports only `propext`, `Classical.choice`,
and `Quot.sound`. The module is imported by the ACS umbrella.

## Positive survivor and remaining scope

The positive theorem is unbounded energy under every finite family of linear constraints,
not just rejection of a proposed reserve. The broader affine-cycle fibre consequence is
being formalized on the parent card. Infinite-dimensional source readings and genuinely
dimensional section theories remain outside this obstruction.
