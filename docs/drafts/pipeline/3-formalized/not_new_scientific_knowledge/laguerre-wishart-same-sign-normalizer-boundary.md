# Laguerre--Wishart normalization forces an unconditional same-sign Gamma theorem

- **ID:** `laguerre-wishart-same-sign-normalizer-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[SEARCH]` exact primary-source normalizer and physics uses; `[BRIDGE]` unconditional same-sign parent theorem and two exact ensemble quotients
- **Source:** I. Dumitriu and A. Edelman, *Matrix Models for Beta Ensembles*, arXiv:math-ph/0206043, equations (2)--(4)
- **Statement:** Every nonempty finite same-orientation Gamma product with positive integer charges is HT, with no translation-orbit separation hypotheses.  Consequently the fixed-shape beta-Laguerre/Gaussian quotient is HT exactly beyond one eigenvalue, and the rectangular Wishart/Gaussian quotient is HT exactly for positive matrix size.

## Goal

Extract the exact value relation carried by the beta-Laguerre/Wishart density normalization and
promote the collision problem it exposes to a reusable HT theorem.  The coupling `z=beta/2` is an
observed ensemble/symmetry parameter.  No theorem treats a matrix, scattering system, covariance
sample, or quantum state as being propagated by this clock.

## Gates

- [x] 0 → 1 in-progress: primary-source Gamma normalizer and classical Wishart ray extracted
- [x] 1 → 2 fully-proven: collision-elimination induction and reflection transfer proved
- [x] 2 → 3 formalized: parent theorems, exact quotient boundaries, circuit source extraction, and existing-corpus consumer pass
- [ ] 3 → 4 publication-ready: standalone exposition not written

## Primary-source value relations

Dumitriu--Edelman equation (2) gives the beta-Hermite/Gaussian density constant.  Equations (3)
and (4) give the beta-Laguerre/Wishart density and the exact constant

`c_L = 2^(-m*a) product_{j=1}^m Gamma(1+z) /
  [Gamma(1+j*z) Gamma(a-z*(m-j))]`,

where `z=beta/2`.  For fixed shape `a`, omit only `Gamma(a)` and the elementary power of two,
which are independent of `z`.  With `m=N+1`, the reciprocal Gamma normalizers obey

`L_{N+1}(a,z) / G_{N+1}(z) = product_{r=1}^N Gamma(a-r*z)`.

The same source states that the classical `m`-by-`n` Wishart model lies on `a=n*z`.  On this ray
`Gamma(a)` is no longer constant.  The complete quotient becomes

`W_{m,n}(z) / G_m(z) = product_{r=0}^{m-1} Gamma((n-r)*z)`.

The omitted factor `2^(m*n*z)` is a nonzero exponential DA gauge, so it cannot change the HT
classification.

## Parent theorem forced by the fixed-shape collision problem

After Gauss refinement, the factors `Gamma(a-r*z)` produce finitely many translated unit-scale
Gamma clocks.  At exceptional `a`, every convenient exposed-orbit choice may collide with another
refined slot.  Requiring a generic separation hypothesis would therefore fail to classify the
actual normalizer uniformly.

The new proof eliminates the hypothesis rather than avoiding the exceptional locus:

1. For a finite product with positive integer charges, choose one factor.
2. If its integer-translation orbit is separated, the existing meromorphic orbit theorem proves HT.
3. If another factor is integer-related, use the exact Gamma recurrence to replace the pair by a
   nonzero rational gauge times one Gamma factor whose charge is the sum of the two positive charges.
4. Induct on the number of factors.  Collision strictly preserves a positive charge and therefore
   can never create cancellation.

This proves unconditionally:

- every nonempty finite positive-charge shifted-Gamma product is HT;
- every nonempty positive-integer-scale positive-orientation Gamma family is HT for arbitrary
  complex shifts;
- by Euler reflection and inversion, the same statements hold for negative orientation;
- arbitrary collision loci require no exposed-orbit or generic-parameter premise.

## Exact positive statements

For every complex `a`,

`HT(L_{N+1}(a,.) / G_{N+1}) iff N>0`.

For every rectangular classical Wishart pair `m<=n`,

`HT(W_{m,n}/G_m) iff m>0`.

The second theorem includes the `Gamma(n*z)` factor that must not be discarded after specializing
`a=n*z`.  Any scalar-aware finite differential circuit presenting a nontrivial fixed-shape
Laguerre/Gaussian quotient contains an HT non-scalar atom.

## Existing-corpus application

`GammaOrientationQuotientBoundary.hypertranscendentalOver_gammaPositiveShiftPairMero` formerly
split into integer-separated and noninteger-separated cases.  It now invokes the same-sign parent
theorem directly.  The two specialized lemmas remain available as explicit normal forms, but the
capstone no longer carries a collision case split.

The parent theorem is ready to replace separation hypotheses in any future thermal, scattering,
Bogoliubov, random-matrix, or normalization theorem once all refined charges have one sign.

## Physics and cross-field reach

The exact carrier is directly reused wherever the ordinary Wishart--Laguerre eigenvalue law is the
model:

- Wigner--Smith inverse proper delay times in quantum chaotic scattering;
- fixed-trace Wishart--Laguerre spectra of reduced density matrices and bipartite entanglement;
- chiral random-matrix models for low-energy QCD Dirac spectra;
- Wishart covariance spectra in multivariate statistics, machine learning, genomics, genetics,
  neuroscience, and covariance estimation.

Laguerre spectral form factors and Wishart-SYK/Q-Laguerre models identify adjacent quantum-chaos
routes, but they are not claimed as direct consumers: the `Q`-Laguerre deformation has a different
normalizer and needs its own exact value extraction.  No direct black-hole, cosmological, Higgs,
inflaton, neutron-star, gravitational-wave, or unified-field normalization matching this carrier
was found in this pass.  The significant positive statement after that no-go is the exact
Wigner--Smith clock: proper time-delay observables are a direct Laguerre consumer, so the theorem
already reaches a genuine quantum clock without interpreting HT as temporal evolution.

## Observability interpretation

The parameter `z=beta/2` labels the observed symmetry/interaction law of an eigenvalue ensemble.
The Gamma quotient is a normalization required to turn that observation law into a probability
density.  In Wigner--Smith scattering the measured objects are delay-time eigenvalues, yet the HT
statement concerns the normalization as the symmetry clock varies; it does not concern the time
evolution of the scatterer.  This is an exact realization of “hypertranscendence is about the
observability structure of a clock, not temporal evolution.”

## Lean certificate

Modules:

- `GaloisForLFunctions.HTGeometry.GammaSameSignProductBoundary`
- `GaloisForLFunctions.HTGeometry.LaguerreWishartNormalizerBoundary`
- `GaloisForLFunctions.HTGeometry.GammaOrientationQuotientBoundary`

Parent capstones:

- `hypertranscendentalOver_gammaFintypeOrbitProductMero_of_pos`
- `hypertranscendentalOver_gammaNatScaleFamilyMero_of_pos`
- `hypertranscendentalOver_gammaFintypeNegativeOrbitProductMero_of_pos`
- `hypertranscendentalOver_gammaNegativeNatScaleFamilyMero_of_pos`

Application capstones:

- `laguerreBetaEnsemble_div_gaussian_eq_deformationTower`
- `hypertranscendentalOver_laguerreBetaEnsemble_div_gaussian_iff_pos`
- `wishartRectangular_div_gaussian_eq_gammaBand`
- `hypertranscendentalOver_wishartRectangular_div_gaussian_iff_pos`
- `exists_hypertranscendental_atom_of_laguerreGaussianNormalizerQuotientCircuit`

The exact cached application-module build and every touched-file direct Lean check pass.  The
capstone axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`; the touched files
contain no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declarations.

## RH pressure test

The result strengthens the archimedean side of the corpus: a same-sign refined Gamma sector is now
an unconditional HT source even on every collision locus.  This can simplify future completed
L-function factor audits and rules out cancellation arguments that relied only on commensurable
same-sign Gamma factors.

It does not produce prime arithmetic, a zero-free region, a positivity kernel, a sign theorem, or a
zero-location constraint.  Therefore it does not presently advance an RH implication by itself.
Its concrete RH-search value is sharper triage: same-sign archimedean complexity can no longer be
mistaken for the missing arithmetic source, and any proposed cancellation route must exhibit an
actual opposite-sign orbit charge.

## Log

- 2026-07-17 -- Dumitriu--Edelman equations (2)--(4) extracted; fixed-shape Laguerre/Gaussian and
  classical rectangular Wishart/Gaussian quotients derived; unconditional positive- and
  negative-orientation same-sign parent theorems formalized; quotient boundaries and circuit
  source extraction verified with serialized targeted Lean processes; existing two-factor
  collision capstone simplified by direct reuse.
