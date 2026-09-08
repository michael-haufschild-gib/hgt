# Scalar positive-curvature quarter comparison

- **ID:** SELBERG-SCALAR-QUARTER-COMPARISON
- **Stage:** 5-failed
- **Type:** NO-GO
- **Parent:** [Selberg conjecturing loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 39.
- **Scope:** Only the scalar shortcut below is retired. The all-congruence Maass quarter bound remains unproved and active.

## Falsified comparison

Smooth modularity, a positive amplitude a vanishing at the cusp, strictly positive q=y²*Delta(a)+lambda*a, finite positive hyperbolic amplitude mass, integrable curvature, vanishing top current, and the exact identity integral(q)=lambda*integral(a) do not force a uniform positive lower bound for the curvature/amplitude mass ratio. In particular, these properties alone do not force the quarter bound.

The literal family a_lambda=E(z,2)^(-lambda/4), constructed from the original positive primitive-pair Eisenstein series, has all these properties for every lambda>0. Its ratio is exactly lambda. Taking lambda=c/2 contradicts any proposed positive uniform comparison c*integral(a)<=integral(q).

Closed Lean statements: `SelbergScalarCurvatureFamily.no_positive_uniform_comparison` and `SelbergScalarCurvatureFamily.no_scalar_quarter_comparison`. The model and curvature are literal functions with actual Frechet derivatives; they are not arbitrary scalar-data records with assumed analytic fields.

## Strongest positive survivor and complete status

The survivor is the constructed all-positive family, including original series positivity, global actual smoothness, exact pointwise power-transform curvature decomposition, explicit source gradient/current bounds, full modular invariance, finite positive mass, actual boundary cancellation, full-domain Stokes limit, and the exact all-positive ratio classification. `SelbergScalarCurvatureFamily.cell_curvature_mass_ratio` gives the classification on the literal standard hyperbolic cell.

[Dependency-closed paper proof and full audit](../3-formalized/selberg-scalar-curvature-flexibility.md). All seven complete scratch proofs, seven needed source olean checks, and seven serialized final single-module builds passed. Both initial and final-artifact axiom audits covered all 91 public declarations, with only the standard three Lean axioms or none. Modules are wired and indexed; no full or umbrella build ran. Final repository-wide lint passed with existing large-file warnings; the earlier unrelated wiring errors were resolved outside this task.

## What survives for Selberg

These models have power-law cusp decay. They do not supply exponential Maass cusp decay, the common original component eigen-equations, the permutation-equivariant direction field with its amplitude-weighted zero means, or the original nodal/regulator constraints. No Maass eigenform or counterexample to Selberg is constructed. The next [source-current loop](../1-in-progress/selberg-original-source-conserved-currents.md) tests the original shared eigen-equation and exact current/energy identities, retaining the regulator's distinct forcing term. Conservation or a nonnegative decomposition must not be promoted to a spectral gap without an actual quantitative source estimate.
