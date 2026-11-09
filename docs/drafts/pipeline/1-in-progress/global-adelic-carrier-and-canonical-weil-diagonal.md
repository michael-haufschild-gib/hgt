# Global adelic carrier and canonical Weil diagonal

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** B133.
- **Statement:** Construct an arithmetic quotient, a global operator and its Green
  regularization whose degree configuration gives the full Frobenius pairing and
  whose diagonal finite part is Weil's diagonal.

## Required construction

Specify the discrete group, its action on the archimedean and finite factors,
the degree points, the operator, its domain and the regularization independently
of the desired Weil pairing. Prove automorphy, the off-diagonal identity and the
diagonal identity. A definition that inserts Weil's form or its diagonal as an
input does not solve the problem. Positivity of the resulting form is separate.

## Available exact data

The prime kernel is a sum of transverse tree channels: each prime acts on its
valuation coordinate and imposes equality at every other coordinate. Each channel
is `log p` times the normalized critical apartment Green kernel minus its identity diagonal.
The archimedean term is the critical hyperbolic Green kernel restricted to the
degree geodesic. These are local formulas, not yet a global Green resolvent.

The specified arithmetic prime-unit action identifies ladder levels with unequal
Frobenius intersections, even under norm-preserving automorphy. The positive
twisted tree fibres retain the ladder through Fourier coefficients. Scalar and
Gram-coupled damping constructions retain explicit discriminant defects.

## Construction question

Can a global arithmetic quotient and its canonical local finite parts assemble
these channels while retaining the degree configuration? The self-dual Haar
normalization and the corpus's adelic trace finite parts provide possible
normalizations; their actual geometric and analytic hypotheses must be discharged.

## Existing global trace constructions

`CCMRationalAdelicMoritaTraceFormula.ccmRationalAdelicMoritaRepresentation_opTrace_eq_orbitSum`
identifies the genuine crossed-product operator trace with a rational-orbit sum.
It does not identify this trace with a Green kernel or its Robin mass.
`CCMArchimedeanPhaseWeilBridge.opTrace_ccmIntegratedScaling_mul_geometricScatteringLogDifferential_eq_weilDistribution`
derives the archimedean Weil distribution, including its normalization, from a
geometric scattering operator. It supplies one place, not the global diagonal.
`DeningerMeyerConvolutionWeilTrace.deningerWeilConvolutionSource_pair_full_arithmetic`
realizes the complete Weil form as a trace, but its Hilbert realization has the
zero-indexed basis `xiDivisorHilbertBasis`; no Green carrier on the requested
adelic quotient is identified by that theorem.

## Opposite finite orientation

Candidate configuration on square degrees: let `g_n = diag(n,n⁻¹)` and
`K_p = SL₂(ℤ_p)`. In the diagonal `SL₂(ℚ)` quotient, compare
`(z_{n²}, (g_n K_p)_p)` with `(z_{n²}, (g_n⁻¹ K_p)_p)`.
The first has representative `(z_1, (K_p)_p)`; the second has representative
`(z_{n⁴}, (K_p)_p)`. A rational matrix fixing every finite base vertex has
integer entries. Integral modular transformations cannot identify distinct
points of the degree ray at heights at least one. Thus opposite finite
orientation should retain all square degrees. Local apartment distances are
unchanged by this reversal. This changes the original configuration and does
not assert a Green or Robin identity. The adelic orbit statement is being
formalized using actual p-adic matrix cosets.

## Verification gates

- [ ] Actual global quotient and operator constructed.
- [ ] Local resolvent expansion gives the existing off-diagonal kernel.
- [ ] The same regularization derives Weil's diagonal with no free counterterm.
- [ ] Lean source checks, transitive axiom audit, and umbrella integration.
