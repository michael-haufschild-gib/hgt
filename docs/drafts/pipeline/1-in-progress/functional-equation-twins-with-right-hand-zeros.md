# Functional-equation twins with arbitrarily right-hand zeros

- **ID:** functional-equation-twins-with-right-hand-zeros
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Γ15; degree-three functional-equation twins.
- **Statement:** For every `N`, `k` and real `B`, a normalized Dirichlet series matching `ζ³` below `N` has a completion with `k` distinct real zeros beyond `max(B,3)`, the same functional equation and the same principal parts.

## Proof

The family in `gammaRCube_theta_relations_vanishing_below (max N 2)` has independent
coefficients vanishing below `max(N,2)` and growth `O(n²)`. Its completions `E_j`
are entire, satisfy `E_j(1-s)=E_j(s)`, and have absolutely convergent Dirichlet
representations on `Re s>3`.

Restrict any `k` members to `σ>max(B,3)`. A zero linear combination there gives an
eventually zero Dirichlet series because `Γ_ℝ(σ)≠0`. Dirichlet uniqueness forces its
coefficients to vanish; independence forces every scalar to vanish. Thus these
restrictions are independent. The evaluation-minor theorem supplies distinct `σ_i`
with invertible matrix `P_ij=E_j(σ_i)`.

Solve `Pc=−(Λ(σ_i)³)_i`. Then `F=Λ³+Σc_j E_j` vanishes at every `σ_i`.
The perturbation is entire and reflection-even. Its coefficient prefix vanishes,
including the coefficient at `1`, so the new series is normalized and matches the
prescribed prefix. A finite sum preserves absolute convergence on `Re s>3`.

## Scope

The result gives neither a uniform rightmost-zero bound nor a uniform count of
right-hand real zeros across this fixed-prefix functional-equation class. The
points are chosen by the proof; they are not an arbitrary prescribed tuple.
The twin may depend on `k` and `B`.

No analytic premise is added. Coefficients are complex; coefficient positivity,
finite order and the Selberg Euler-product axioms are not established. This is
degree three; degree-one rigidity is formalized in `HTGeometry.HamburgerFunctionalEquation`.

## Verification

- [x] Dependency-closed paper proof.
- [ ] Lean leaf check, transitive axiom audit, umbrella import.
