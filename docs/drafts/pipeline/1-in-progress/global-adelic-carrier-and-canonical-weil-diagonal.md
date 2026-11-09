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

## Proved projective carrier geometry

[The full projective carrier](../3-formalized/full-projective-adelic-carrier-retains-every-degree.md)
constructs the discrete group `Γ=J⁻¹SL₂(ℚ)J` in
`SL₂(ℂ)×Π'_p PGL₂(ℚ_p)`, where `J` is the finite integral Weyl element.
Its ordinary action on `ℍ³×Π'_p(PGL₂(ℚ_p)/PGL₂(ℤ_p))` retains every original
point `x_n=(z_n,(diag(n,1)K_p)_p)` distinctly. Both local parity classes and
all positive integer degrees are included. Projective integrality forces
quadratic entry quotients to be integers; an orbit forces `(m/n)²∈ℤ`, and
the inverse orbit forces `m=n`. Discreteness and injectivity are formalized
with standard axioms only.

The earlier [split-degree classification](../3-formalized/finite-weyl-conjugation-retains-the-global-degree-configuration.md)
gives exact fourth-power height normal forms on the determinant-one cover.
Local finiteness of the full degree image and finite-factor adjacency on the
quotient remain to be proved. The latter must be realized as Hecke
correspondences. These orbit results do not yet identify a Green operator,
its off-diagonal kernel, or its Robin diagonal.

## Prime adjacency construction

At `p`, the orbit of `diag(1,p)K_p` under `K_p` should have the `p+1`
representatives `diag(1,p)` and `[[p,-b],[0,1]]`, `b∈𝔽_p`.
Reduction of the first column gives the representative; integrality of the
transition matrix proves equality of lattice classes. This defines local
adjacency independently of the target kernel. The prime operator on the
arithmetic quotient must sum over these neighbours before taking quotient
classes, preserving multiplicity when distinct neighbours become identified.
The exact local degree and quotient descent are not yet formalized.

## Local Green construction

For `g∈GL₂(ℚ_p)`, put `R(g)=|det g|_p/(maxᵢⱼ |gᵢⱼ|_p)²`.
The next target is to descend `R(g_x⁻¹g_y)` to local vertices and prove
the actual adjacency identity for

`G_s(x,y)=p^s/(p^(2s)-1) · R(g_x⁻¹g_y)^s`, `s>0`.

Integral row and column reduction should give `diag(1,d)`, `|d|_p≤1`.
Away from the base class, one neighbour should have ratio `pR` and the
other `p` neighbours ratio `R/p`; at the base all ratios should be `1/p`.
This would realize the existing radial Green recurrence on actual vertices
without assuming a tree identification. Invariance, the reduction and this
neighbour law remain unproved. Global descent of a Green kernel and its
diagonal regularization remain separate requirements.

## Verification gates

- [ ] Actual global quotient and operator constructed.
- [ ] Local resolvent expansion gives the existing off-diagonal kernel.
- [ ] The same regularization derives Weil's diagonal with no free counterterm.
- [ ] Lean source checks, transitive axiom audit, and umbrella integration.
