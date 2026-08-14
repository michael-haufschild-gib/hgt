# Scalar-power multiplicity amplification for Schanuel curves — failed

- **ID:** schanuel-scalar-power-multiplicity-amplification
- **Stage:** 5-failed
- **Type:** FALSIFIED CONJECTURE + FORMALIZED POSITIVE SURVIVOR
- **Source:** power-primitive isogeny normal form; isolated exponential-curve intersections

## Conjecture attacked

Given a hypothetical stage-two counterexample on an algebraic curve, use the infinitely many
scalar transforms

\[
  (x_i,y_i)\longmapsto (m x_i,y_i^m)
\]

to amplify the local intersection multiplicity of the curve with the graph of exponentiation.
A growing multiplicity could then feed a zero estimate or force a positive-dimensional analytic
intersection to which Ax--Schanuel applies.

## Exact obstruction

For any commutative ring and positive integer `m`,

\[
  a^m-b^m=(a-b)\sum_{j=0}^{m-1}a^j b^{m-1-j}. \tag{1}
\]

At a characteristic-zero field-valued point with `a=b != 0`, the cofactor specializes to

\[
  m a^{m-1}\ne0. \tag{2}
\]

For analytic germs, `(2)` makes the cofactor a unit. Therefore `a^m-b^m` and `a-b` generate the
same local principal ideal and have exactly the same zero multiplicity. Applied with
`a=y_i` and `b=exp(x_i)`, scalar isogenies preserve the local exponential-intersection ideal;
they do not amplify it.

The two-coordinate ideal is unchanged coordinatewise, so simultaneous multiplicity also cannot
grow by scalar powering. Power-primitive stabilization of generated fields does not alter this
local-unit identity.

## No-go closure

- **Killing mechanism:** every powered exponential equation is the original equation times a
  unit at the selected nonzero exponential point.
- **Positive survivor:** exact factorization `(1)` and nonvanishing law `(2)`.
- **Universal principle:** finite étale torus isogenies preserve both Kähler rank and local
  intersection multiplicity. Any successful amplification must use period translation or another
  operation ramified/noninvertible at the selected analytic branch.
- **Lean status:** `RHTower/SchanuelPowerMultiplicityNoGo.lean` formalizes `(1)`, the exact diagonal
  cofactor value, and its nonvanishing in characteristic zero. Scratch axiom audit reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- **Novelty:** elementary factorization is classical; its role as exact closure of this Schanuel
  amplification route is new internal synthesis. No external priority claim.

## Literature audit

Ax--Schanuel governs positive-dimensional analytic intersections, not an isolated point. Common-zero
and Shapiro-type rigidity for exponential polynomials is not an unconditional replacement: the
available results explicitly derive major zero statements from Schanuel itself. See James Ax,
[On Schanuel's conjectures](https://annals.math.princeton.edu/1971/93-2/p03), and Fischler--Rivoal,
[Zeros of E-functions and of exponential polynomials](https://arxiv.org/abs/2503.20345).

## Next conjecture

Search for a branch-sensitive invariant whose value changes under affine period translation but
is still constrained arithmetically by the `Qbar`-defined curve. Finite isogeny, ordinary Kummer
degree, local multiplicity, and abstract function-field Galois data are now all proved blind.

## Log

- 2026-08-14 -- scalar multiplicity amplification conjectured, killed by exact local-unit
  factorization, positive survivor formalized and umbrella-wired.
