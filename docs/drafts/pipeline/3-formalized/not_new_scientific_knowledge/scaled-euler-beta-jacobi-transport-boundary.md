# One-channel Jacobi normalization is a scaled Euler beta amplitude

- **ID:** `scaled-euler-beta-jacobi-transport-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[BRIDGE] [LEAN-FORMALIZED]` exact cross-corpus value relation
- **Statement:** The one-channel classical Jacobi/Gaussian quotient is exactly `B(n1*z,n2*z)` and is HT for all positive integer channel slopes.

## Goal

Connect the newly formalized Jacobi/MANOVA quantum-transport normalizer to the Euler beta carrier
of Veneziano/open-string and Regge scattering.  Unlike the existing fixed-second-channel
Veneziano theorem, both numerator arguments and their sum vary with the observed clock.

## Gates

- [x] 0 → 1 in-progress: relation found in the existing normalizer formulas; no duplicate declaration
- [x] 1 → 2 fully-proven: exact one-channel identity and exposed-orbit HT proof
- [x] 2 → 3 formalized: direct Lean check and axiom audit
- [ ] 3 → 4 publication-ready: standalone exposition not written

## Exact value relation

Define

`B_{n1,n2}(z) = Gamma(n1*z) Gamma(n2*z) / Gamma((n1+n2)*z)`.

Expanding the three slots of `jacobiMANOVAGammaQuotientMero 1 n1 n2` proves

`J_{1,n1,n2}(z) / G_1(z) = B_{n1,n2}(z)`.

Thus one and the same value is the Gamma-dependent normalization of a one-transmission-eigenvalue
Jacobi/MANOVA observation law and an Euler beta scattering carrier.  This is not merely a shared
special-function analogy: the Lean theorem is equality in the global meromorphic field.

At unit slopes there is a further exact existing-corpus identification:

`B_{1,1}(z) = D_2(z)^(-1)`,

where `D_2(z)=Gamma(2*z)/Gamma(z)^2` is the binary symmetric-Dirichlet normalizer used by the
project's AI/genomic interface.  Combining this with the already formalized circular-beta/
Dirichlet relation proves that the product of the two-eigenangle circular-beta normalizer and the
unit-slope one-channel Jacobi/Gaussian quotient is exactly the rational gauge `2*z/z^2`.  Thus two
individually HT Gamma carriers cancel completely across four application labels: circular random
matrices, Jacobi quantum transport, beta scattering, and binary Dirichlet inference.

## Positive theorem

For `n1,n2>0`, the denominator scale `n1+n2` is strictly larger than the numerator scales.  Its
refined center `1/(n1+n2)` is an exposed charge-minus-one orbit.  Specializing the Jacobi theorem
at matrix size one gives

`HT(B_{n1,n2})`.

Consequently no rational or finite-Laurent function of the common clock equals this amplitude, and
every scalar-aware finite differential circuit presenting it contains an HT non-scalar atom.

This complements, rather than duplicates, the existing `VenezianoGammaRatioBoundary`: that module
classifies `Gamma(z+a)/Gamma(z+a+b)` when the second beta argument is fixed, whereas the new theorem
varies both beta arguments and their sum on positive integer slopes.

## Lean certificate

Module:

- `GaloisForLFunctions.HTGeometry.JacobiMANOVANormalizerBoundary`
- `GaloisForLFunctions.HTGeometry.ScaledEulerBetaCrossDomainBoundary`

Declarations:

- `scaledEulerBetaMero`
- `jacobiMANOVAGammaQuotientMero_one_eq_scaledEulerBeta`
- `jacobiMANOVAPartitionNormalizer_one_div_gaussian_eq_scaledEulerBeta`
- `hypertranscendentalOver_scaledEulerBetaMero`
- `scaledEulerBetaMero_ne_ratFuncModel`
- `exists_hypertranscendental_atom_of_scaledEulerBetaCircuit`
- `scaledEulerBetaMero_one_one_eq_inv_symmetricDirichlet`
- `jacobiMANOVA_one_one_one_div_gaussian_eq_inv_symmetricDirichlet`
- `circularBeta_two_mul_jacobiMANOVA_one_one_one_div_gaussian_eq_gauge`
- `differentialAlgebraicOver_circularBeta_two_mul_jacobiMANOVA_div_gaussian`

Both exact module targets, both direct file checks, and both capstone axiom audits pass.  The audits
report only `propext`, `Classical.choice`, and `Quot.sound`; the files contain no forbidden proof
escape declaration.

## Observability and physics reach

For quantum transport, `z=beta/2` is the symmetry/repulsion parameter of the transmission
eigenvalue observation law.  For Veneziano or Regge scattering, it is the common channel-slope
coordinate.  The equality identifies the value read by these two observation structures; it does
not identify their temporal dynamics.

The fixed-channel Veneziano provenance is recorded in the existing
`veneziano-gamma-ratio-differential-boundary` card.  The transport use is supported by
arXiv:0801.3026 and arXiv:1105.4353.  The normalizer formula comes from Dumitriu--Edelman equation
(6), arXiv:math-ph/0206043.

## RH pressure test

This improves the HT corpus beyond a single application domain: one exposed-orbit theorem now
controls both an exact quantum-transport normalizer and a genuinely two-slope beta scattering
amplitude.  It provides a reusable mixed-scale archimedean source and rules out rational
finite-clock models of that source.

It still carries no primes, positivity kernel, zero-free region, or critical-line orientation.
Hence it does not advance an RH implication directly.  Its RH-search value is architectural: it
shows that a shared special-function carrier can transport an HT certificate across observation
theories, but cannot by itself transport the arithmetic information that RH needs.

## Log

- 2026-07-17 -- exact one-channel Jacobi/scaled-beta equality, positive-slope HT theorem,
  no-rational-model consequence, and finite-circuit source extraction formalized; serialized exact
  target, direct file check, and axiom audit passed.
- 2026-07-17 -- unit-slope carrier identified exactly with the reciprocal binary Dirichlet
  normalizer; circular-beta times Jacobi/Gaussian Gamma cancellation reduced to the existing
  rational gauge; cross-domain module built, checked, and axiom-audited.
