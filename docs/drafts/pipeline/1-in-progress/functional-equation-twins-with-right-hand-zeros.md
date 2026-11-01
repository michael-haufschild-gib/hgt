# Functional-equation twins with arbitrarily right-hand zeros

- **ID:** functional-equation-twins-with-right-hand-zeros
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Γ15; degree-three functional-equation twins.
- **Statement:** For every coefficient cutoff `N` and real bound `B`, an entire reflection-even perturbation of the completed `ζ³` preserves the coefficients below `N` and has a real zero beyond `max(B,3)`.

## Proof target

Choose a nonzero polynomial-growth coefficient sequence from
`gammaRCube_theta_relations_vanishing_below`. Its entire completion `E` satisfies
`E(1-s)=E(s)`. Dirichlet uniqueness supplies a real `σ>max(B,3)` with `E(σ)≠0`.
Then `Λ(s)³−Λ(σ)³ E(s)/E(σ)` has the required zero, reflection law and unchanged
principal parts. Scaling the coefficients preserves their vanishing initial segment.

The target is an existence theorem with no analytic premise. It does not assert a
degree-one twin or positivity of the new coefficients. Degree-one rigidity is already
formalized in `HTGeometry.HamburgerFunctionalEquation`.

## Gates

- [x] Corpus inputs identified; exact degree and coefficient class fixed.
- [ ] Dependency-closed paper proof and nonzero Dirichlet-completion bridge.
- [ ] Lean leaf check, transitive axiom audit, umbrella import.
