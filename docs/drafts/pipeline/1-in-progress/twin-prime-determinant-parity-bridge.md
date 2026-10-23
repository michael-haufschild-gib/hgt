# Exact parity conjugation of the determinant sum

- **ID:** twin-prime-determinant-parity-bridge
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / BRIDGE
- **Source:** [signed determinant operator](twin-prime-determinant-operator.md)
- **Statement:** A Liouville change of row and column coordinates moves both Möbius signs into the single shifted parity sequence `lambda(s)lambda(s+2)`.

## Dependency-closed proof

All indices below are positive integers. Write `lambda` for Liouville
and `mu` for Möbius. Complete multiplicativity gives
`lambda(ab)=lambda(a)lambda(b)`, and `lambda(a)^2=1`.
Squarefree support gives `mu(a)=lambda(a)mu(a)^2`.

On `mn+2=qh`, put `s=mn`. Then

`mu(m)mu(h)
 =lambda(q)lambda(n)lambda(s)lambda(s+2) mu(m)^2 mu(h)^2`.

Indeed substitute `lambda(s)=lambda(m)lambda(n)` and
`lambda(s+2)=lambda(q)lambda(h)`. The two extra row and column
signs square to one, leaving `lambda(m)lambda(h)`.
Both sides are zero off the determinant surface if multiplied
by its indicator. This proves the identity for every positive
quadruple, without a determinant premise in the theorem statement.

For finite factor sets `M,H` and any nonnegative weight
`w(m,n,q,h)`, define two matrices, with row `q` and column `n`:

`K(q,n)=sum_(m in M,h in H,mn+2=qh) mu(m)mu(h) w(m,n,q,h)`,

`G(q,n)=sum_(m in M,h in H,mn+2=qh)
  lambda(mn)lambda(mn+2) mu(m)^2 mu(h)^2 w(m,n,q,h)`.

The entry identity gives `K(q,n)=lambda(q)lambda(n)G(q,n)`.
Consequently their bilinear pairings agree after applying
`x(j) -> lambda(j)x(j)` to both boundary vectors. This coordinate
change is involutive and preserves every finite sum of squared
absolute values. Thus the sets of pairing values over Euclidean
unit balls are identical, and in particular the operator norms
are identical. Finite cutoff, coprimality, squarefree-row, marking,
and roughness restrictions can all be included in `w`.

For the Mellin phase, `m^(iv)=(mn)^(iv)n^(-iv)` moves the extra
column phase outside the matrix. The internal scalar sequence then
becomes `lambda(s)lambda(s+2)s^(iv)`. This observation is a paper
extension; the first Lean certificate will cover real coefficients
at `v=0` and arbitrary finite nonnegative weights.

## What this changes in the attempted proof

The Möbius signs in multiplicative incidence do not themselves
reduce the operator norm: complete multiplicativity moves them
to boundary coordinates. After introducing the additive shift,
the surviving sign is exactly the two-point Liouville sequence.
The hard object is that sequence tested against divisor-incidence
weights. An unweighted scalar cancellation theorem does not
automatically give cancellation against these weights.

This does not refute the operator conjecture. It exposes its exact
arithmetic input and prevents treating the two interior signs as
independent sources of a saving. The fourth trace moment tests
products of four shifted parity values; repeated-product terms
and genuine off-diagonal terms must be distinguished before any
random-sign heuristic is used.

## Frontier and status

The basic multiplicativity identity is known mathematics, not a
novel cancellation theorem. The corpus already uses Liouville
coordinates to align finite Möbius inversion in
`RHTower/ChronologicalSelbergSharpMass.lean`, notably
`moebius_mul_liouville_mul_real`. Its statement and proof were
read. The determinant specialization above was derived directly.
No further web search was used to produce it.

**Verdict: BRIDGE.** Complete algebraic proof; no analytic estimate
and no assertion of scientific novelty. The signed operator
conjecture and twin-prime infinitude remain open in this work.

## Gates

- [x] Exact positive-index definitions and complete paper proof.
- [x] Source check for the multiplicative sign identity.
- [ ] Lean certificate for entry conjugation and equality of unit-ball pairing values.
- [ ] Leaf compile and foundational axiom audit.

## Log

- 2026-10-23 — Derived the exact conjugation while attacking the
  signed determinant norm. No cancellation estimate is claimed.
