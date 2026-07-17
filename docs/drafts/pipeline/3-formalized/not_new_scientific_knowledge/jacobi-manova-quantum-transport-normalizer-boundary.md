# Jacobi--MANOVA normalization exposes a unique denominator clock

- **ID:** `jacobi-manova-quantum-transport-normalizer-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[SEARCH]` exact Jacobi/MANOVA normalizer and quantum-transport consumer; `[BRIDGE]` exposed refined-orbit HT boundary
- **Source:** I. Dumitriu and A. Edelman, *Matrix Models for Beta Ensembles*, arXiv:math-ph/0206043, equations (2), (5), and (6)
- **Statement:** On the classical rectangular ray, every positive-size Jacobi/MANOVA normalizer divided by the Gaussian normalizer is HT in the Dyson coupling because its signed Gamma family contains a unique largest-scale denominator orbit.

## Goal

Extract a mixed-sign value relation whose HT proof cannot use same-sign positivity, prove it from
the existing refined-orbit API, and identify a direct quantum observable carrying the Jacobi law.
The varying coordinate is the observed ensemble parameter `z=beta/2`, not the physical time of a
mesoscopic cavity or fermionic system.

## Gates

- [x] 0 → 1 in-progress: primary-source Jacobi normalizer and direct transport consumer extracted
- [x] 1 → 2 fully-proven: unique largest-scale denominator orbit proved exposed
- [x] 2 → 3 formalized: exact quotient relation and positive-size HT equivalence verified
- [ ] 3 → 4 publication-ready: standalone exposition not written

## Primary-source value relation

Dumitriu--Edelman equation (6) gives the Jacobi/MANOVA density normalizer.  Put `z=beta/2` and
specialize its two shape parameters to the classical rectangular ray `a1=n1*z`, `a2=n2*z`.
After quotienting by the beta-Hermite/Gaussian normalizer from equation (2), and omitting only the
common nonzero elementary gauge, the exact Gamma-dependent value relation is

`J_{m,n1,n2}(z) / G_m(z) = product_{r=0}^{m-1}
  Gamma((n1-r)*z) Gamma((n2-r)*z) / Gamma((n1+n2-r)*z)`.

This is not a same-sign family.  It has two positive numerator bands with scales `n1-r` and
`n2-r`, and one negative denominator band with scales `n1+n2-r`.

## Exact positive theorem after the mixed-sign obstruction

Assume `0<m<=n1,n2`.  The first denominator factor has scale `K=n1+n2`, strictly larger than every
other scale, and charge `-1`.  Gauss refinement exposes its slot at center `1/K`.  For any smaller
positive scale `j<=K`, a refined center `k/j` can coincide with `1/K` modulo an integer only at the
same top slot.  Hence this negative orbit cannot be cancelled by either numerator band or by the
remaining denominator factors.

Therefore

`HT(J_{m,n1,n2}/G_m) iff m>0`.

The `m=0` direction is exact: the quotient is the constant one.  No genericity, irrationality, or
pairwise separation hypothesis remains.

## Direct physics consumers

The Jacobi ensemble is the exact random-matrix law for transmission eigenvalues in chaotic
mesoscopic cavities.  These eigenvalues determine conductance and shot noise; thus the formal
normalizer boundary applies directly to the observation law used in quantum transport.  See
P. Vivo and E. Vivo, *Transmission Eigenvalue Densities and Moments in Chaotic Cavities from Random
Matrix Theory*, arXiv:0801.3026, and S. Kumar and A. Pandey, *Jacobi Crossover Ensembles of Random
Matrices and Statistics of Transmission Eigenvalues*, arXiv:1105.4353.

The beta-Jacobi law also occurs in the analytic entanglement entropy of the free `SYK2` model;
see C. Liu, X. Chen, and L. Balents, *Quantum Entanglement of the Sachdev-Ye-Kitaev Models*,
arXiv:1709.06259.  This is a direct ensemble consumer, but the theorem classifies the normalization
as the symmetry coupling varies, not entropy as physical time evolves.

No exact value identification was found here with black-hole thermodynamic, cosmological,
Higgs/inflaton, neutron-star, gravitational-wave, or unified-field normalizers.  The significant
positive residue is stronger than analogy: chaotic-cavity transmission and `SYK2` entanglement
both use the ordinary Jacobi observation law covered by the theorem.

## Observability interpretation

The density normalizer is forced by the measurement law: it is what makes the joint distribution
of the observed transmission or entanglement-spectrum eigenvalues integrate to one.  Its HT
coordinate is `beta/2`, the continuously varied symmetry/repulsion clock.  Nothing in the proof
propagates a state through time.  The surviving invariant is a non-cancellable refined observation
slot at `1/(n1+n2)`.

## Existing-corpus application

This module is a new direct consumer of the existing exposed-refined-orbit theorem.  It supplies a
mixed-sign complement to the unconditional same-sign parent theorem: same-sign products are
handled by collision merging, whereas this Jacobi quotient is handled by a unique extremal
denominator clock.  The combination covers two structurally different normalizer regimes without
adding a new hypothesis to either interface.

No pre-existing Jacobi/MANOVA normalizer declaration was found elsewhere in the Lean corpus, so no
older theorem could be simplified directly.  The reusable gain is an exact instantiated theorem
surface for future quantum-transport, beta-Jacobi, and entanglement-spectrum consumers.

The one-channel specialization does connect to an existing theorem family: it is exactly the
scaled Euler beta/Veneziano carrier `Gamma(n1*z) Gamma(n2*z) / Gamma((n1+n2)*z)`.  The companion
`scaled-euler-beta-jacobi-transport-boundary` card records the equality and transfers the Jacobi HT
certificate to a two-slope open-string/Regge scattering amplitude.

## Lean certificate

Module:

- `GaloisForLFunctions.HTGeometry.JacobiMANOVANormalizerBoundary`

Capstones:

- `hypertranscendentalOver_jacobiMANOVAGammaQuotientMero`
- `jacobiMANOVAPartitionNormalizer_div_gaussian_eq_gammaQuotient`
- `hypertranscendentalOver_jacobiMANOVA_div_gaussian_iff_pos`
- `jacobiMANOVAPartitionNormalizer_one_div_gaussian_eq_scaledEulerBeta`
- `hypertranscendentalOver_scaledEulerBetaMero`

The exact cached module build and the direct file check pass.  The capstone axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.  The file contains no `sorry`, `admit`, `axiom`,
`opaque`, or `unsafe` declaration.

## RH pressure test

The result strengthens the archimedean cancellation audit: a mixed-sign Gamma quotient can be
certified HT from one unique refined denominator orbit even when the rest of its factors collide.
This gives future completed-factor arguments an exact local source criterion rather than a global
pairwise-separation premise.

It does not supply prime arithmetic, positivity, a zero-free region, a sign change, or a
zero-location theorem.  It therefore does not advance an RH implication by itself.  Its immediate
RH-search value is diagnostic: opposite-sign Gamma factors do not create useful cancellation unless
their refined observation orbits actually coincide, and a unique extremal scale rules that out.

## Log

- 2026-07-17 -- Dumitriu--Edelman Jacobi normalizer specialized to the classical rectangular ray;
  exact Gaussian quotient, unique negative top orbit, HT iff positive size, and quantum-transport
  interpretation formalized and verified with serialized targeted Lean processes.
