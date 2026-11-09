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

## Proved carrier geometry on square degrees

[Finite Weyl conjugation](../3-formalized/finite-weyl-conjugation-retains-the-global-degree-configuration.md)
constructs a faithful discrete rational group in `SL₂(ℂ)×Π'_p SL₂(ℚ_p)`
and actual finite coset vertices. For `g_q=diag(q,q⁻¹)`, the split configuration
`(z_{(ab)²},(g_{a/b}K_p)_p)` has normal form `(z_{b⁴},(K_p)_p)`;
two classes agree exactly when `b` agrees. Conjugating the arithmetic group
by the finite integral Weyl element retains every original square-degree point.
Discreteness and injectivity are formalized with standard axioms only.

The construction presently uses determinant-one local vertex spaces. Extending
to all degrees and full `PGL₂` trees remains open. Finite-factor adjacency on
the quotient must be realized as Hecke correspondences; the normal form alone
does not identify a Green operator. No global kernel or Robin identity follows
from the orbit classification.

For all degrees, use the full local homothety cosets of `GL₂(ℚ_p)`.
The base stabilizer satisfies `‖Mᵢⱼ‖²≤‖det M‖`. Applied to the opposite
degree vertices, all-place integrality should force `c²/(mn)` and `d²m/n`
to be integers for an orbit matrix with bottom row `(c,d)`. Together with
`n=m/(c²m²+d²)` and the inverse orbit, this should force `m=n`, without
restricting the degrees to squares. This extension is not yet formalized.

## Verification gates

- [ ] Actual global quotient and operator constructed.
- [ ] Local resolvent expansion gives the existing off-diagonal kernel.
- [ ] The same regularization derives Weil's diagonal with no free counterterm.
- [ ] Lean source checks, transitive axiom audit, and umbrella integration.
