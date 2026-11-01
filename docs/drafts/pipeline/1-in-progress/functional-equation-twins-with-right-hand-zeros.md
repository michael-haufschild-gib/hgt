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

## Finite-zero interpolation

**Conjecture:** For every `N`, `B` and `k`, one such twin has `k` distinct real zeros
beyond `max(B,3)`. Thus finite coefficient data give neither a uniform rightmost-zero
bound nor a uniform count of right-hand real zeros in this functional-equation class.

Take `k` independent theta perturbations. Their restrictions to any real right ray
remain independent: a vanishing linear combination gives a vanishing Dirichlet series,
hence zero coefficients. The corpus evaluation-minor theorem supplies `k` distinct
points with invertible evaluation matrix. Solve against the negative values of `Λ³`.
The resulting finite linear combination preserves the coefficient prefix and all
principal parts. The interpolation points are chosen by the proof; they are not an
arbitrary prescribed tuple.
