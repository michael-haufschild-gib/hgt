# Terminal-linear Bell polynomial/derivation-orbit universality law

## Status

`[LEAN PROVED — LITERATURE AUDITED]`

## Lean-derived conjecture

For every terminal-linear differential state `δx = A x`, the first `n+2` actual derivation
iterates are obtained by evaluating one universal terminal-linear Bell polynomial chart at the
finite `A`-jet and terminal state `x`.

The generic chart has pure Jacobian determinant
`(-1)^(n+1) X_terminal^(n+1)`.  In every compatible actual coordinate frame this specializes to
the exact lower-`A`-jet determinant formula; nonvanishing forces algebraic independence of the
actual orbit.

## Corpus inputs

- `terminalLinearBellOutput`
- `polynomialOutputJacobian_terminalLinearBellOutput_det`
- `derivation_iterate_terminalLinear_eq_derivationBellValue`
- `derivationIterateOutputJacobian_det`
- `algebraicIndependent_derivationIterates_terminalLinear`

## New connector

The corpus separately proves a generic Bell polynomial Jacobian law and an actual-derivation
Jacobian law.  Evaluating the generic chart at the finite logarithmic-derivative jet identifies
every output coordinate with the corresponding actual iterate, so both determinant laws are one
universal specialization mechanism rather than parallel analogies.

No numerical computation is used.

## Novelty protocol

No literature search before exact Lean proof.

## Lean target

`formal/GaloisForLFunctions/HTGeometry/TerminalLinearBellDerivationOrbitUniversalityLaw.lean`

## Exact Lean verification

From `formal/`:

```text
lake env lean GaloisForLFunctions/HTGeometry/TerminalLinearBellDerivationOrbitUniversalityLaw.lean
```

completed with zero diagnostics.

## Post-proof literature audit

Nearest literature:

- H. M. Srivastava et al., *Application of the Bell polynomials for the solution of some
  differential-algebraic equations*,
  [arXiv:2304.06856](https://arxiv.org/abs/2304.06856), uses Bell polynomials to expand
  differential-algebraic equations.
- J. Mittmann, N. Saxena, P. Scheiblechner,
  *Algebraic Independence in Positive Characteristic -- A p-Adic Calculus*,
  [arXiv:1202.4301](https://arxiv.org/abs/1202.4301), develops Jacobian criteria for
  algebraic independence.
- A. Johnston, C. Prochno, *Faà di Bruno's formula and inversion of power series*,
  [Advances in Mathematics 395 (2022)](https://doi.org/10.1016/j.aim.2021.108080),
  connects Faà di Bruno combinatorics with polynomial-map Jacobians and inversion.

These sources treat Bell/Faà di Bruno expansions or Jacobian independence criteria separately.
No source found states the exact specialization law proved here: a universal
terminal-linear Bell polynomial chart evaluates coordinate-for-coordinate to every actual
finite derivation orbit `δx = A x`, its pure terminal monomial Jacobian specializes to the
lower-`A`-jet determinant in an arbitrary compatible derivation frame, and nonvanishing forces
algebraic independence.  No exact match was found.
