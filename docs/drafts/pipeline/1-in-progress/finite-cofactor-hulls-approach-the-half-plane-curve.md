# Finite cofactor hulls approach the half-plane curve

- **ID:** finite-cofactor-hulls-approach-the-half-plane-curve
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (Lean completion pending)
- **Parent:** [Q-III](q-iii-escape-state-classification.md)
- **Statement:** Every finite actual cofactor hull character is a pointwise
  limit, on the full critical Wiener algebra, of half-plane evaluations.

## Corpus evidence and exact scope

`AKernelBoundedBelowOnTheHalfPlaneIsAUnit.le_norm_bohrEval_of_onTorus`
already constructs vertical characters approximating any prescribed finite
set of prime phases with common radial exponent. Its argument uses
`PrimeTorusKroneckerDensity.primeTorus_cpow_dense`, prime factorization,
and dominated convergence of absolutely summable Wiener coefficients.
The missing reusable statement lets the prime aperture grow and obtains
one sequence converging on every Wiener element simultaneously.

The pending finite-module modulus classification supplies either
`|omega(p)|=p^(-alpha)` for one alpha>=0 or augmentation. The former case
should lie in the closure of the vertical line Re(s)=1/2+alpha. Augmentation
should be approached as Re(s) tends to infinity. Values at zero are ignored
by all arithmetic-function evaluations; no artificial normalization of
raw Bohr points is needed for the character statement.

This is approximation by the whole half-plane curve. It does not assert
exact curve membership, approximation by translated zeta zeros, occurrence
of these points in actual modules, or a result for infinite module hulls.

## Formalization

Extract a prime-approximation helper from the existing tied-torus proof;
reuse it there. Choose aperture j and tolerance 1/(j+1). Prime coordinate
convergence extends to positive integers by factorization. Summable
domination gives convergence of all Wiener evaluations using the same
sequence. Prove the augmentation endpoint separately and apply the pending
finite actual modulus theorem. All claims remain OPEN until Lean checks,
transitive axiom audits, canonical source checks, and umbrella wiring pass.

The common-eigenvector input is complete:
`HTGeometry/FiniteCommutingFamiliesHaveCommonEigenvectors.exists_common_eigenvector_family`
passed final canonical source audit `15948` with only standard axioms. Its
olean is available to the written finite-hull application. Numeric operator
order, tied-torus limits and the actual finite-hull application still require
their direct checks.
